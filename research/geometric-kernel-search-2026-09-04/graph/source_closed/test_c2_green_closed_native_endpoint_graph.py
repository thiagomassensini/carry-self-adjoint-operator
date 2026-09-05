from __future__ import annotations

from fractions import Fraction
import importlib.util
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "script/c2_green_closed_native_endpoint_graph.py"
SPEC = importlib.util.spec_from_file_location("closed_native_endpoint", SCRIPT)
assert SPEC and SPEC.loader
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_frozen_frontier_is_loaded_without_reinterpretation() -> None:
    audit = MOD.integrity_audit()
    assert audit["frozen_results"] == [
        "PASS_NATIVE_C2_A_BULK_TYPED_PULLBACK",
        "STOP_PRE_T0_PROVENANCE_INSUFFICIENT_FOR_A_LIFT",
        "STOP_NATIVE_C2_ENDPOINT_NOT_IN_A_FIBRE",
        "NEEDS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT",
    ]
    assert audit["frozen_witness_count"] == 54


def test_native_visible_mass_is_exact_fraction() -> None:
    assert MOD.visible_mass(64, 1) == Fraction(61, 64)
    assert isinstance(MOD.visible_mass(64, 3), Fraction)


def test_local_prime_tower_has_normalized_constant_term() -> None:
    coefficients = MOD.local_mass_coefficients(64, 3, 5)
    assert coefficients[0] == 1
    assert all(isinstance(value, Fraction) for value in coefficients)


def test_newton_power_sum_matches_log_derivative() -> None:
    coefficients = [Fraction(1), Fraction(2, 3), Fraction(5, 7), Fraction(11, 13)]
    powers = MOD.newton_power_sums(coefficients)
    logs = MOD.formal_log_coefficients(coefficients)
    for j in range(1, len(coefficients)):
        assert sp.Rational(powers[j].numerator, powers[j].denominator) == sp.simplify(j * logs[j])


def test_richardson_log_coefficients_are_exact() -> None:
    audit = MOD.exact_logjet_audit()
    assert audit["checkpoint"] == "PASS_C2_PRIME_POWER_LOGJET_CORE"
    assert audit["rho_provenance"]["literal_specialization"].endswith("p_T^(-j tau)")
    assert all(record["number_identity_residual"] == 0 for record in audit["finite_exact_records"])


def test_unit_mass_limit_has_kappa_one_over_j() -> None:
    records = MOD.exact_logjet_audit()["unit_mass_limit"]["records"]
    assert [record["kappa_j"] for record in records] == [Fraction(1, j) for j in range(1, 9)]
    assert all(record["N_h_coefficient_at_tau_0"] == 1 for record in records)


def test_global_odd_mass_matches_native_two_branch_mass() -> None:
    audit = MOD.global_odd_convolution_audit()
    assert audit["mass_comparison"]["low_all_odd_equal"]
    assert audit["mass_comparison"]["high_all_odd_equal"]
    assert audit["mass_comparison"]["low_odd_core_count"] == 199
    assert audit["mass_comparison"]["high_odd_core_count"] == 399


def test_global_odd_inversion_restricts_exactly_to_local_prime_towers() -> None:
    audit = MOD.global_odd_convolution_audit()
    restriction = audit["prime_power_restriction"]
    assert restriction["all_exact"]
    assert restriction["record_count"] == 53


def test_global_mixed_channels_remain_separate_from_j_and_dj() -> None:
    audit = MOD.global_odd_convolution_audit()
    mixed = audit["mixed_channels"]
    assert mixed["retained_by_global_inversion"]
    assert mixed["not_part_of_the_single_prime_tower_jet"]
    assert mixed["not_identified_with_d_J"]
    fifteen = next(record for record in mixed["records"] if record["integer"] == 15)
    assert fifteen["global_log_basis"] == [
        {"prime": 3, "coefficient_of_log_prime": Fraction(1, 4096)},
        {"prime": 5, "coefficient_of_log_prime": Fraction(1, 4096)},
    ]


def test_zero_time_hilbert_scale_memberships() -> None:
    scale = MOD.hilbert_scale_audit()
    zero = scale["zero_time"]
    assert zero["h_in_H0"]
    assert zero["Nh_not_in_H0"]
    assert zero["Nh_in_Hminus1"]
    assert scale["number_operator"]["operator_norm"] == 1


def test_number_operator_is_exact_h0_to_hminus1_isometry() -> None:
    scale = MOD.hilbert_scale_audit()
    for record in scale["number_operator"]["exact_checks"]:
        assert record["H0_norm_squared"] == record["N_image_Hminus1_norm_squared"]


def test_positive_tau_flow_norm_formula() -> None:
    tau = sp.symbols("tau", positive=True)
    p = sp.Integer(3)
    formula = sp.log(p) ** 2 / (p ** (2 * tau) - 1)
    assert sp.limit(tau * formula, tau, 0, dir="+") == sp.log(3) / 2


def test_endpoint_h_support_is_exact_prime_power_indicator() -> None:
    assert MOD.h_at_zero_over_logp(1, 3) == 0
    assert MOD.h_at_zero_over_logp(3, 3) == 1
    assert MOD.h_at_zero_over_logp(9, 3) == 1
    assert MOD.h_at_zero_over_logp(27, 3) == 1
    assert MOD.h_at_zero_over_logp(15, 3) == 0
    assert MOD.h_at_zero_over_logp(45, 3) == 0


def test_q_sums_dj_but_preserves_j() -> None:
    values = {
        (1, 1): Fraction(1, 2),
        (2, 1): Fraction(1, 3),
        (1, 2): Fraction(2, 5),
    }
    assert MOD.q_jh(values) == {1: Fraction(5, 6), 2: Fraction(2, 5)}


def test_number_commutes_with_tensor_coequalizer() -> None:
    values = {
        (1, 1): Fraction(2, 3),
        (2, 1): Fraction(-2, 3),
        (1, 4): Fraction(7, 11),
    }
    assert MOD.q_jh(MOD.number_pre(values)) == MOD.number_post(MOD.q_jh(values))


def test_coequalizer_kernel_is_number_invariant() -> None:
    gauge = {(1, 5): Fraction(7, 13), (3, 5): Fraction(-7, 13)}
    assert MOD.q_jh(gauge) == {}
    assert MOD.q_jh(MOD.number_pre(gauge)) == {}


def test_post_t0_relation_is_closed_and_single_valued() -> None:
    relation = MOD.coequalizer_graph_audit()
    assert relation["closed_relation"]["closed"]
    assert relation["closed_relation"]["single_valued"]
    assert relation["closed_relation"]["multivalued_part"] == "{0}"
    assert "PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER" in relation["checkpoints"]


def test_forbidden_tower_level_sum_is_not_used_as_q() -> None:
    relation = MOD.coequalizer_graph_audit()
    assert "summing the tower levels j" in relation["typing_warning"]
    assert relation["coequalizer"] == "Q=Q_JH tensor I_tower; Q_JH sums d_J contributions only"


def test_a_leg_detects_exact_coequalizer_gauge() -> None:
    descent = MOD.a_descent_audit()
    witness = descent["witness"]
    assert witness["Q_gauge"] == sp.zeros(1, 1)
    assert sp.simplify(witness["A_even_pre_gauge"] - (1 - sp.sqrt(3)) / 2) == 0
    assert descent["checkpoint"] == "STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL"


def test_a_descent_stop_precedes_any_graph_bound() -> None:
    descent = MOD.a_descent_audit()
    assert not descent["A_even_pre_descends_to_Q_quotient"]
    assert not descent["graph_bound_after_descent_tested"]
    assert descent["frontier"] == "NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION"


def test_native_comparison_does_not_overclaim_full_lift() -> None:
    logjet = MOD.exact_logjet_audit()
    scale = MOD.hilbert_scale_audit()
    coequalizer = MOD.coequalizer_graph_audit()
    descent = MOD.a_descent_audit()
    comparison = MOD.native_comparison_audit(logjet, scale, coequalizer, descent)
    assert comparison["post_t0_logjet_graph_constructed"]
    assert not comparison["full_native_endpoint_graph_lift_constructed"]
    assert "PASS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT" in comparison["not_emitted"]


def test_persisted_summary_has_scoped_result() -> None:
    summary = json.loads(
        (ROOT / "result/c2_green_closed_native_endpoint_graph/summary.json").read_text(
            encoding="utf-8"
        )
    )
    assert summary["result"] == "STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL"
    assert summary["frontier"] == "NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION"
    assert "PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION" in summary["passes"]
    assert summary["global_prime_power_agreements"] == 53
    assert summary["global_mixed_channels_retained"]
    assert not summary["full_native_endpoint_graph_lift_constructed"]


def test_reports_and_result_artifacts_are_nonempty() -> None:
    paths = [
        ROOT / "C2_GREEN_C2_PRIME_POWER_LOGJET_GRAPH.md",
        ROOT / "C2_GREEN_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT.md",
        ROOT / "C2_GREEN_JH_COEQUALIZER_GRAPH_RELATION.md",
        ROOT / "result/c2_green_closed_native_endpoint_graph/summary.json",
        ROOT / "result/c2_green_closed_native_endpoint_graph/manifest.json",
    ]
    assert all(path.exists() and path.stat().st_size > 0 for path in paths)


def test_manifest_preserves_historical_hashes_and_witnesses() -> None:
    manifest = json.loads(
        (ROOT / "result/c2_green_closed_native_endpoint_graph/manifest.json").read_text(
            encoding="utf-8"
        )
    )
    assert manifest["historical_integrity"]["all_preserved"]
    assert manifest["historical_integrity"]["mismatches"] == {}
    assert manifest["frozen_witness_count"] == 54
    assert not manifest["reverse_section_used"]
    assert not manifest["LP_or_solver_used"]


def test_no_forbidden_endpoint_reconstruction_was_claimed() -> None:
    integrity = json.loads(
        (ROOT / "result/c2_green_closed_native_endpoint_graph/integrity.json").read_text(
            encoding="utf-8"
        )
    )
    assert not any(integrity["forbidden_methods"].values())
