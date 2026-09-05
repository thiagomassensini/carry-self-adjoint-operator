from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

import pytest
import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "script/c2_green_native_range_provenance_graph.py"
SPEC = importlib.util.spec_from_file_location("c2_native_range_provenance", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MOD = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)


@pytest.fixture(scope="session", autouse=True)
def generate_current_round() -> None:
    assert MOD.main([]) == 0


def test_frozen_inputs_and_witnesses_are_loaded() -> None:
    audit = MOD.integrity_audit()
    assert audit["frozen_witness_count"] == 54
    assert all(size > 0 for size in audit["mandatory_input_sizes"].values())
    assert not any(audit["forbidden_methods"].values())


def test_exact_mobius_ell2_witness() -> None:
    witness = MOD.free_module_witness_audit()["ell_2_witness"]
    assert witness["mu_ell"] == sp.Matrix([1, -1])
    assert witness["Q_mu"] == sp.zeros(1, 1)
    assert sp.simplify(witness["A_even_pre_mu"] - (1 - sp.sqrt(3)) / 2) == 0


@pytest.mark.parametrize("ell", [2, 3, 4, 6, 8, 12, 18, 30, 60, 120])
def test_mobius_divisor_sum_is_zero(ell: int) -> None:
    assert sum(MOD.mobius_divisor_vector(ell)) == 0


def test_mobius_proof_is_not_promoted_to_native_input() -> None:
    audit = MOD.free_module_witness_audit()
    assert audit["checkpoint"] == "QUALIFY_STOP_NATIVE_A_AS_FREE_MODULE_ONLY"
    assert audit["native_preimage_constructed"] is False
    assert audit["mu_ell_called_native"] is False
    assert audit["native_membership"] == "undetermined until E_native^preT0 exists"


def test_all_designated_constructor_functions_are_source_hashed() -> None:
    audit = MOD.source_contract_audit()
    assert len(audit["candidate_constructors"]) == 4
    for record in audit["candidate_constructors"]:
        assert len(record["source_sha256"]) == 64
        assert record["source_size"] > 100
        assert record["line_span"][1] >= record["line_span"][0]


def test_no_constructor_carries_all_forward_axes() -> None:
    audit = MOD.source_contract_audit()
    required = set(audit["required_forward_axes"])
    assert audit["complete_generator_candidates"] == []
    assert audit["canonical_join_constructor_persisted"] is False
    assert all(not required <= set(row["axes_carried"]) for row in audit["candidate_constructors"])
    assert audit["checkpoint"] == "STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED"


def test_post_t0_flags_have_collapsed_dj_and_no_tau_or_pa() -> None:
    audit = MOD.source_contract_audit()
    assert audit["collapsed_d_J_marker_verified"] is True
    assert audit["raw_d_J_retained"] is False
    assert audit["tau_retained"] is False
    assert audit["p_A_retained"] is False
    assert audit["post_t0_flag_count"] > 0


def test_jh_feature_and_native_flag_schemas_are_complementary_not_joined() -> None:
    audit = MOD.source_contract_audit()
    by_function = {row["function"]: row for row in audit["candidate_constructors"]}
    assert {"p_A", "tau", "d_J"} <= set(by_function["laplace_jordan_lift_audit"]["axes_carried"])
    assert {"cell", "corner", "orientation", "flags"} <= set(
        by_function["contextual_flags_for_native_cell"]["axes_carried"]
    )
    assert "p_A" in by_function["contextual_flags_for_native_cell"]["axes_missing"]
    assert "cell" in by_function["laplace_jordan_lift_audit"]["axes_missing"]


def test_native_range_and_kernel_are_not_fabricated() -> None:
    source = MOD.source_contract_audit()
    audit = MOD.native_range_gate_audit(source)
    assert audit["E_native_preT0_constructed"] is False
    assert audit["R_native_defined"] is False
    assert audit["K_native_defined"] is False
    assert audit["K_native_classified"] is False
    assert audit["native_witness_constructed"] is False
    assert audit["mu_mode_native_realizable"] == "not determined"


def test_no_false_native_mobius_pass_or_stop_is_emitted() -> None:
    audit = MOD.native_range_gate_audit(MOD.source_contract_audit())
    assert "PASS_MOBIUS_MODE_NATIVE_REALIZABLE" in audit["not_emitted"]
    assert "STOP_MOBIUS_MODE_NOT_IN_NATIVE_RANGE" in audit["not_emitted"]
    assert "STOP_NATIVE_A_NONZERO_ON_NATIVE_COEQUALIZER_KERNEL" in audit["not_emitted"]


def test_divisor_haar_phase_obeys_native_witness_gate() -> None:
    native = MOD.native_range_gate_audit(MOD.source_contract_audit())
    audit = MOD.divisor_haar_gate_audit(native)
    assert audit["activation_condition_met"] is False
    assert audit["phase_executed"] is False
    assert audit["P_ell_div_constructed"] is False
    assert audit["Qtilde_constructed"] is False
    assert audit["not_confused_with_Haar_Mangoldt"] is True


def test_enriched_graph_is_deferred_before_native_range() -> None:
    source = MOD.source_contract_audit()
    native = MOD.native_range_gate_audit(source)
    divisor = MOD.divisor_haar_gate_audit(native)
    audit = MOD.enriched_graph_gate_audit(source, divisor)
    assert audit["tower_number_descent_preserved"] is True
    assert audit["post_T0_closed_relation_preserved"] is True
    assert audit["previous_frontier_definitively_activated"] is False
    assert audit["current_frontier"] == "NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE"
    assert audit["enriched_scales_constructed"] is False


def test_persisted_summary_scopes_result_and_frontier() -> None:
    summary = json.loads((MOD.RESULT / "summary.json").read_text(encoding="utf-8"))
    assert summary["result"] == "STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED"
    assert summary["qualification"] == "QUALIFY_STOP_NATIVE_A_AS_FREE_MODULE_ONLY"
    assert summary["frontier"] == "NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE"
    assert summary["free_module_witness_exact"] is True
    assert summary["free_module_witness_is_native"] is False
    assert summary["definitive_native_A_stop_emitted"] is False
    assert summary["frozen_passes_preserved"] == MOD.FROZEN_PASSES


def test_validation_is_exact_and_complete() -> None:
    validation = json.loads((MOD.RESULT / "validation.json").read_text(encoding="utf-8"))
    assert validation["all_passed"] is True
    assert all(validation["checks"].values())


def test_requested_reports_are_nonempty() -> None:
    reports = (MOD.REPORT_RANGE, MOD.REPORT_MOBIUS, MOD.REPORT_DIVISOR, MOD.REPORT_GRAPH)
    assert all(path.exists() and path.stat().st_size > 700 for path in reports)


def test_result_artifacts_are_nonempty_and_independent() -> None:
    required = {
        "summary.json",
        "manifest.json",
        "free_module_witness.json",
        "constructor_inventory.json",
        "native_range_gate.json",
        "mobius_kernel.json",
        "divisor_haar_gate.json",
        "enriched_graph_gate.json",
    }
    assert required <= {path.name for path in MOD.RESULT.iterdir() if path.is_file()}
    assert all((MOD.RESULT / name).stat().st_size > 100 for name in required)
    assert (MOD.RESULT / "constructor_inventory.json").read_bytes() != (
        MOD.RESULT / "mobius_kernel.json"
    ).read_bytes()


def test_manifest_preserves_historical_artifacts() -> None:
    manifest = json.loads((MOD.RESULT / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["historical_integrity"]["all_preserved"] is True
    assert manifest["historical_integrity"]["mismatches"] == {}
    assert manifest["frozen_witness_count"] == 54
    assert manifest["reverse_section_used"] is False
    assert manifest["pseudoinverse_used"] is False
    assert manifest["Householder_used"] is False
    assert manifest["LP_or_solver_used"] is False
    assert manifest["Green_to_zero_claimed"] is False
