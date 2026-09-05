#!/usr/bin/env python3
"""Audit the native pre-T0 range before any divisor-Haar enrichment.

The audit is deliberately forward-only.  It qualifies the old free-module
Möbius witness, inventories the original C2/Jordan/Hodge constructors, and
tests whether any persisted constructor carries all native and pre-T0 axes at
once.  It never selects a section of the J/H coequalizer.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "result/c2_green_native_range_provenance_graph"
TEST_PATH = ROOT / "tests/test_c2_green_native_range_provenance_graph.py"

REPORT_RANGE = ROOT / "C2_GREEN_NATIVE_PRET0_RANGE.md"
REPORT_MOBIUS = ROOT / "C2_GREEN_MOBIUS_JORDAN_KERNEL_AUDIT.md"
REPORT_DIVISOR = ROOT / "C2_GREEN_DIVISOR_HAAR_PROVENANCE_PORT.md"
REPORT_GRAPH = ROOT / "C2_GREEN_PROVENANCE_ENRICHED_GRAPH_RELATION.md"

FROZEN_PASSES = [
    "PASS_C2_PRIME_POWER_LOGJET_CORE",
    "PASS_POSITIVE_TAU_LOGJET_GRAPH",
    "PASS_ZERO_TIME_LOGJET_IN_HMINUS1",
    "PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER",
    "PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION",
]

MANDATORY_INPUTS = [
    ROOT / "C2_GREEN_C2_PRIME_POWER_LOGJET_GRAPH.md",
    ROOT / "C2_GREEN_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT.md",
    ROOT / "C2_GREEN_JH_COEQUALIZER_GRAPH_RELATION.md",
    ROOT / "C2_GREEN_NATIVE_A_PRET0_TYPE_REGISTRY.md",
    ROOT / "C2_GREEN_NATIVE_A_COMMON_CODOMAIN.md",
    ROOT / "C2_GREEN_NATIVE_A_ENDPOINT_LIFT.md",
    ROOT / "script/c2_green_closed_native_endpoint_graph.py",
    ROOT / "script/c2_green_native_a_endpoint_all_fibres.py",
    ROOT / "script/c2_green_centered_b_contextual_endpoint.py",
    ROOT / "script/c2_green_centered_jordan_krein.py",
    ROOT / "script/c2_green_molecule_gcd_laplace_jordan.py",
    ROOT / "script/c2_green_full_even_hodge_endpoint.py",
    ROOT / "result/c2_green_closed_native_endpoint_graph/a_descent.json",
    ROOT / "result/c2_green_closed_native_endpoint_graph/coequalizer_relation.json",
    ROOT / "result/c2_green_centered_b_contextual_endpoint/pre_sigma0_endpoint.json",
    ROOT / "result/c2_green_centered_b_contextual_endpoint/combined_jh_endpoint.json",
    ROOT / "result/c2_green_molecule_gcd_laplace_jordan/laplace_jordan_lift.json",
]

REQUIRED_FORWARD_AXES = [
    "p_A",
    "tau",
    "d_J",
    "p_T",
    "j",
    "K",
    "m",
    "cell",
    "corner",
    "orientation",
    "flags",
    "role",
]


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def json_default(value: object) -> object:
    if isinstance(value, sp.Basic):
        return str(value)
    if isinstance(value, sp.MatrixBase):
        return [[str(entry) for entry in row] for row in value.tolist()]
    if isinstance(value, Path):
        return str(value)
    raise TypeError(f"cannot serialize {type(value)!r}")


def json_dump(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=json_default) + "\n",
        encoding="utf-8",
    )


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def witness_paths() -> list[Path]:
    return sorted(ROOT.glob("result/c2_green_carry_current_audit/n*/witness_*.npz"))


def snapshot(paths: Sequence[Path]) -> dict[str, str]:
    return {relative(path): sha256_file(path) for path in paths}


def integrity_audit() -> dict[str, object]:
    missing = [relative(path) for path in MANDATORY_INPUTS if not path.exists()]
    empty = [relative(path) for path in MANDATORY_INPUTS if path.exists() and path.stat().st_size == 0]
    if missing:
        raise FileNotFoundError(f"missing canonical inputs: {missing}")
    if empty:
        raise RuntimeError(f"empty canonical inputs: {empty}")
    witnesses = witness_paths()
    if len(witnesses) != 54:
        raise RuntimeError(f"expected 54 frozen witnesses, found {len(witnesses)}")
    tracked = sorted(set(MANDATORY_INPUTS + witnesses))
    return {
        "schema": "c2.green.native_range_provenance.integrity.v1",
        "Genuine_First": True,
        "mandatory_input_count": len(MANDATORY_INPUTS),
        "mandatory_input_sizes": {relative(path): path.stat().st_size for path in MANDATORY_INPUTS},
        "frozen_witness_count": len(witnesses),
        "historical_hashes_before": snapshot(tracked),
        "forbidden_methods": {
            "reverse_section": False,
            "pseudoinverse": False,
            "Householder": False,
            "LP": False,
            "solver": False,
            "prime_number_theorem": False,
            "zero_data": False,
            "Green_to_zero": False,
        },
    }


def divisors_exact(index: int) -> list[int]:
    if index < 1:
        raise ValueError("index must be positive")
    small: list[int] = []
    large: list[int] = []
    divisor = 1
    while divisor * divisor <= index:
        if index % divisor == 0:
            small.append(divisor)
            if divisor * divisor != index:
                large.append(index // divisor)
        divisor += 1
    return small + list(reversed(large))


def mobius_exact(index: int) -> int:
    if index < 1:
        raise ValueError("index must be positive")
    remaining = index
    distinct = 0
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            if remaining % prime == 0:
                return 0
            distinct += 1
            while remaining % prime == 0:
                remaining //= prime
        prime = 3 if prime == 2 else prime + 2
    if remaining > 1:
        distinct += 1
    return -1 if distinct % 2 else 1


def mobius_divisor_vector(ell: int) -> list[int]:
    return [mobius_exact(divisor) for divisor in divisors_exact(ell)]


def free_module_witness_audit(maximum_ell: int = 128) -> dict[str, object]:
    ell = 2
    divisors = divisors_exact(ell)
    gauge = sp.Matrix(mobius_divisor_vector(ell))
    q_row = sp.ones(1, len(divisors))
    q_gauge = sp.simplify(q_row * gauge)
    a_weights = sp.Matrix([sp.Rational(1, 2), sp.sqrt(3) / 2])
    a_gauge = sp.simplify((a_weights.T * gauge)[0])
    if q_gauge != sp.zeros(1, 1) or a_gauge != (1 - sp.sqrt(3)) / 2:
        raise RuntimeError("free-module witness changed")

    checks = []
    for value in range(2, maximum_ell + 1):
        vector = mobius_divisor_vector(value)
        total = sum(vector)
        if total != 0:
            raise RuntimeError(f"Mobius divisor identity failed at ell={value}")
        checks.append(
            {
                "ell": value,
                "divisors": divisors_exact(value),
                "mu_vector": vector,
                "Q_mu": total,
            }
        )
    return {
        "schema": "c2.green.mobius_jordan.free_module_witness.v1",
        "checkpoint": "QUALIFY_STOP_NATIVE_A_AS_FREE_MODULE_ONLY",
        "old_checkpoint": "STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL",
        "old_checkpoint_scope": "free d_J coefficient module only",
        "ell_2_witness": {
            "ell": 2,
            "tau": 1,
            "leg_n": 2,
            "d_J": divisors,
            "mu_ell": gauge,
            "identity": "(1,-1)=(mu(1),mu(2))",
            "Q_row": q_row,
            "Q_mu": q_gauge,
            "A_even_pre_row": a_weights.T,
            "A_even_pre_mu": a_gauge,
            "nonzero_proof": "(1-sqrt(3))/2 != 0 because squaring 1=sqrt(3) would give 1=3",
        },
        "general_identity": {
            "formula": "sum_(d|ell)mu(d)=product_(p|ell)(1-1)=0 for ell>1",
            "proof": (
                "only square-free divisors contribute; choosing a square-free divisor is choosing "
                "a subset of the distinct prime divisors, with sign (-1)^cardinality"
            ),
            "exact_checked_interval": [2, maximum_ell],
            "records": checks,
        },
        "native_preimage_constructed": False,
        "mu_ell_called_native": False,
        "native_membership": "undetermined until E_native^preT0 exists",
    }


def function_contract(path: Path, function_name: str) -> dict[str, object]:
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(path))
    nodes = [
        node
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == function_name
    ]
    if len(nodes) != 1:
        raise RuntimeError(f"expected one {function_name} in {relative(path)}, found {len(nodes)}")
    node = nodes[0]
    lines = source.splitlines(keepends=True)
    fragment = "".join(lines[node.lineno - 1 : node.end_lineno])
    return {
        "path": relative(path),
        "function": function_name,
        "line_span": [node.lineno, node.end_lineno],
        "arguments": [argument.arg for argument in node.args.args],
        "source_sha256": sha256_text(fragment),
        "source_size": len(fragment.encode("utf-8")),
    }


def source_contract_audit() -> dict[str, object]:
    native_path = ROOT / "script/c2_green_full_even_hodge_endpoint.py"
    lift_path = ROOT / "script/c2_green_molecule_gcd_laplace_jordan.py"
    centered_path = ROOT / "script/c2_green_centered_jordan_krein.py"
    endpoint_path = ROOT / "script/c2_green_centered_b_contextual_endpoint.py"

    pre_sigma = load_json(
        ROOT / "result/c2_green_centered_b_contextual_endpoint/pre_sigma0_endpoint.json"
    )
    lift = load_json(
        ROOT / "result/c2_green_molecule_gcd_laplace_jordan/laplace_jordan_lift.json"
    )
    flags = pre_sigma["selected_complete_flags"]
    retained_flag_fields = sorted(set.intersection(*(set(row) for row in flags)))
    collapsed_dj = all(
        row.get("d_Jordan") in {"summed over d_J|ell before endpoint", "seed"}
        for row in flags
    )
    if not collapsed_dj:
        raise RuntimeError("historical endpoint no longer has the audited collapsed d_J marker")

    candidates = [
        {
            **function_contract(native_path, "contextual_flags_for_native_cell"),
            "layer": "native C2 -> rational pair flags -> post-T0 endpoint record",
            "axes_carried": ["K", "m", "cell", "corner", "orientation", "flags", "p_T", "j"],
            "axes_missing": ["p_A", "tau", "d_J", "role"],
            "decisive_fact": "d_Jordan is a collapsed marker supplied by endpoint_pair_record",
        },
        {
            **function_contract(lift_path, "laplace_jordan_lift_audit"),
            "layer": "unreduced J/H one-leg feature contract",
            "axes_carried": ["p_A", "tau", "d_J", "orientation"],
            "axes_missing": ["p_T", "j", "K", "m", "cell", "corner", "flags", "role"],
            "decisive_fact": lift["one_leg_channels"],
        },
        {
            **function_contract(centered_path, "centered_coordinates"),
            "layer": "separated centered A/B coordinate",
            "axes_carried": ["p_A", "tau", "d_J"],
            "axes_missing": ["p_T", "j", "K", "m", "cell", "corner", "orientation", "flags", "role"],
            "decisive_fact": "returns only the numeric pair (A,B); it does not attach native provenance",
        },
        {
            **function_contract(endpoint_path, "pre_sigma0_endpoint_audit"),
            "layer": "completed endpoint after J/H coequalizer and tau=0",
            "axes_carried": ["p_T", "j", "cell", "corner", "orientation", "flags"],
            "axes_missing": ["p_A", "tau", "d_J", "K", "m", "role"],
            "decisive_fact": "selected_complete_flags retain pair geometry but not raw J/H coordinates",
        },
    ]
    complete = [
        candidate
        for candidate in candidates
        if set(REQUIRED_FORWARD_AXES) <= set(candidate["axes_carried"])
    ]
    if complete:
        raise RuntimeError("a complete persisted native pre-T0 generator appeared; re-audit required")

    missing_join = {
        "native_flag_side": ["p_A", "tau", "raw d_J", "J/H role"],
        "JH_feature_side": ["native cell/corner/flag role", "K=k_eff", "odd fibre m", "tower p_T,j"],
        "post_T0_side": ["p_A", "tau", "raw d_J", "J/H role"],
    }
    return {
        "schema": "c2.green.native_pret0.constructor_inventory.v1",
        "checkpoint": "STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED",
        "required_forward_axes": REQUIRED_FORWARD_AXES,
        "candidate_constructors": candidates,
        "complete_generator_candidates": complete,
        "canonical_join_constructor_persisted": False,
        "retained_post_t0_flag_fields": retained_flag_fields,
        "post_t0_flag_count": len(flags),
        "raw_d_J_retained": False,
        "tau_retained": all("tau" in row for row in flags),
        "p_A_retained": all("p_A" in row for row in flags),
        "collapsed_d_J_marker_verified": collapsed_dj,
        "missing_join_data": missing_join,
        "why_formulas_do_not_supply_the_map": (
            "composing the separate formulas would require a new choice of how p_A,tau,d_J,J/H role "
            "attach to each native flag and tower level; no original constructor persists that join"
        ),
        "reverse_endpoint_used": False,
        "post_t0_used_to_fabricate_tau_or_d_J": False,
    }


def native_range_gate_audit(source_audit: Mapping[str, object]) -> dict[str, object]:
    constructed = bool(source_audit["canonical_join_constructor_persisted"])
    if constructed:
        raise RuntimeError("unexpected constructed native range")
    return {
        "schema": "c2.green.native_pret0.range_gate.v1",
        "E_native_preT0_constructed": False,
        "R_native_defined": False,
        "K_native_defined": False,
        "K_native_classified": False,
        "ell_2_native_preimage_of_mu": "not determined",
        "mu_mode_native_realizable": "not determined",
        "mu_mode_not_in_native_range_proved": False,
        "native_witness_constructed": False,
        "restricted_kernel_inclusion_tested": False,
        "native_A_descends_on_restricted_quotient": False,
        "reason": "R_native cannot be formed from the persisted constructors without inventing the missing join",
        "checkpoint": "STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED",
        "not_emitted": [
            "PASS_NATIVE_PRET0_RANGE_CONSTRUCTED",
            "PASS_NATIVE_RANGE_COEQUALIZER_KERNEL_CLASSIFIED",
            "PASS_MOBIUS_MODE_NATIVE_REALIZABLE",
            "STOP_MOBIUS_MODE_NOT_IN_NATIVE_RANGE",
            "PASS_NATIVE_RANGE_ELIMINATES_FREE_JH_GAUGE",
            "PASS_NATIVE_A_DESCENDS_ON_RESTRICTED_QUOTIENT",
            "STOP_NATIVE_A_NONZERO_ON_NATIVE_COEQUALIZER_KERNEL",
        ],
    }


def divisor_haar_gate_audit(native_range: Mapping[str, object]) -> dict[str, object]:
    native_witness = bool(native_range["native_witness_constructed"])
    if native_witness:
        raise RuntimeError("conditional divisor-Haar phase unexpectedly activated")
    return {
        "schema": "c2.green.divisor_haar.conditional_gate.v1",
        "activation_condition": "a complete native witness in K_native with nonzero A_even_pre image",
        "activation_condition_met": False,
        "phase_executed": False,
        "P_ell_div_constructed": False,
        "eta_ell_d_frame_claimed": False,
        "Qtilde_constructed": False,
        "minimal_A_observable_provenance_computed": False,
        "mobius_moment_sufficiency_tested": False,
        "reason": "the task permits this enrichment only after a native witness; free-module mu_ell is insufficient",
        "not_confused_with_Haar_Mangoldt": True,
        "not_emitted": [
            "PASS_CANONICAL_DIVISOR_HAAR_PROVENANCE_FRAME",
            "PASS_MINIMAL_A_OBSERVABLE_PROVENANCE",
        ],
    }


def enriched_graph_gate_audit(
    source_audit: Mapping[str, object], divisor_gate: Mapping[str, object]
) -> dict[str, object]:
    if source_audit["canonical_join_constructor_persisted"] or divisor_gate["phase_executed"]:
        raise RuntimeError("enriched graph gate state changed")
    return {
        "schema": "c2.green.provenance_enriched_graph.gate.v1",
        "tower_number_descent_preserved": True,
        "post_T0_closed_relation_preserved": True,
        "Qtilde_number_intertwiner_tested": False,
        "enriched_scales_constructed": False,
        "native_A_descent_to_enriched_graph_tested": False,
        "closed_native_endpoint_graph_lift_constructed": False,
        "previous_frontier": "NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION",
        "previous_frontier_definitively_activated": False,
        "current_frontier": "NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE",
        "reason": (
            "minimal enrichment is downstream of native-range classification; the range is unavailable "
            "because the forward pre-T0 generator was not persisted"
        ),
        "not_emitted": [
            "PASS_NATIVE_A_DESCENDS_TO_ENRICHED_GRAPH",
            "PASS_PROVENANCE_ENRICHED_GRAPH_RELATION",
            "PASS_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT",
        ],
    }


def build_summary(
    witness: Mapping[str, object],
    source: Mapping[str, object],
    native: Mapping[str, object],
    divisor: Mapping[str, object],
    graph: Mapping[str, object],
) -> dict[str, object]:
    return {
        "schema": "c2.green.native_range_provenance.summary.v1",
        "Genuine_First": True,
        "result": "STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED",
        "qualification": witness["checkpoint"],
        "frontier": graph["current_frontier"],
        "frozen_passes_preserved": FROZEN_PASSES,
        "free_module_witness_exact": True,
        "free_module_witness_is_native": False,
        "mobius_native_membership": native["mu_mode_native_realizable"],
        "native_range_constructed": native["R_native_defined"],
        "native_kernel_classified": native["K_native_classified"],
        "native_witness_constructed": native["native_witness_constructed"],
        "definitive_native_A_stop_emitted": False,
        "divisor_haar_phase_executed": divisor["phase_executed"],
        "enriched_graph_constructed": graph["enriched_scales_constructed"],
        "source_constructor_count": len(source["candidate_constructors"]),
        "complete_forward_constructor_count": len(source["complete_generator_candidates"]),
        "phase_status": {
            "free_module_witness": "qualified exactly",
            "forward_native_range": "stopped: generator not persisted",
            "native_kernel": "not defined",
            "restricted_descent": "not tested",
            "divisor_Haar": "conditional phase not activated",
            "minimal_provenance": "not tested",
            "enriched_graph": "not constructed",
        },
        "claims_not_emitted": native["not_emitted"] + divisor["not_emitted"] + graph["not_emitted"],
        "reverse_section_used": False,
        "Green_to_zero_claimed": False,
    }


def render_range_report(source: Mapping[str, object], native: Mapping[str, object]) -> str:
    rows = []
    for candidate in source["candidate_constructors"]:
        rows.append(
            f"| `{candidate['function']}` | {', '.join(candidate['axes_carried'])} | "
            f"{', '.join(candidate['axes_missing'])} |"
        )
    return f"""# Faixa nativa pre-T0 do coequalizer

## Resultado

`STOP_NATIVE_PRET0_GENERATOR_NOT_PERSISTED`

A auditoria foi feita na direção forward. Nenhuma seção do coequalizer foi
escolhida e nenhum endpoint pós-`T0` foi invertido. Os quatro construtores
canônicos auditados têm hashes de fonte persistidos, mas nenhum carrega ao
mesmo tempo todos os eixos

```text
{', '.join(source['required_forward_axes'])}.
```

| Construtor | Eixos carregados | Eixos ausentes |
|---|---|---|
{chr(10).join(rows)}

O ledger de flags retém `{source['post_t0_flag_count']}` registros completos de
geometria de pares. Neles, porém, `d_Jordan` é literalmente o marcador
“summed over d_J|ell before endpoint”; `tau` e `p_A` não aparecem. O construtor
one-leg J/H retém `p_A,tau,d_J`, mas não retém `cell,corner,flags,role,K,m` nem
o fator de torre `p_T,j`. Compor essas duas descrições agora exigiria inventar
um join que não pertence aos construtores originais.

Consequentemente `E_native^preT0`, `R_native` e `K_native` não foram definidos.
Não foi provada nem a realizabilidade nativa do modo Möbius, nem sua exclusão.
Em particular, nenhum dos checkpoints de classificação de faixa em
`{', '.join(native['not_emitted'])}` foi emitido.

## Dados que faltam

- no lado dos flags nativos: `p_A`, `tau`, o valor cru de `d_J` e o papel J/H;
- no lado das features J/H: o flag C2 completo, `K=k_eff`, a fibra ímpar `m` e
  o nível de torre `p_T,j`;
- no endpoint pós-T0: a proveniência anterior ao somatório em `d_J`.

A fronteira correta é `NEEDS_NATIVE_PRET0_GENERATOR_PERSISTENCE`, anterior a
qualquer quociente enriquecido.
"""


def render_mobius_report(witness: Mapping[str, object], native: Mapping[str, object]) -> str:
    ell2 = witness["ell_2_witness"]
    return f"""# Auditoria do kernel Möbius–Jordan

## Qualificação

`QUALIFY_STOP_NATIVE_A_AS_FREE_MODULE_ONLY`

Na fibra livre `ell=2`, `tau=1`, `n=2`, os divisores são `(1,2)` e

```text
mu_2=(mu(1),mu(2))=(1,-1).
Q mu_2=1-1=0,
A_even_pre mu_2=(1-sqrt(3))/2 != 0.
```

A não anulação é exata: uma igualdade `1=sqrt(3)` implicaria `1=3` após
quadrar. Para todo `ell>1`, somente divisores square-free contribuem, de modo
que

```text
sum_(d|ell) mu(d)=product_(p|ell)(1-1)=0.
```

O script confirmou essa identidade por aritmética inteira em
`ell=2,...,{witness['general_identity']['exact_checked_interval'][1]}`; a prova
é o produto sobre subconjuntos dos primos distintos de `ell`, não uma inferência
numérica.

## Escopo

Esse vetor vive no módulo livre de coeficientes `d_J`. Como
`E_native^preT0` não está persistido, não existe nesta rodada um input C2 `x`
com imagem demonstrada `mu_2`, nem uma prova de que tal input seja impossível.
A pertença nativa permanece `{native['mu_mode_native_realizable']}`. Portanto o
stop histórico não foi promovido a
`STOP_NATIVE_A_NONZERO_ON_NATIVE_COEQUALIZER_KERNEL`.
"""


def render_divisor_report(divisor: Mapping[str, object]) -> str:
    return f"""# Porta de proveniência divisor-Haar

## Gate condicional

A fase não foi executada. Sua condição era um witness nativo completo em
`K_native`; essa condição vale `{str(divisor['activation_condition_met']).lower()}`.
O modo Möbius do módulo livre não substitui esse witness.

Por isso não foram construídos `P_ell^div`, os átomos `eta_(ell,d)`,
`Qtilde_ell` ou `V_A(ell)`, e não foi testada a suficiência de um único momento
Möbius. Fazer qualquer uma dessas construções agora violaria a ordem do gate e
poderia preservar uma proveniência que a faixa C2 real nunca excita.

Esta porta eventual é divisor-Haar/Möbius–Jordan na variável `d_J`. Ela não é
o complemento Haar–Mangoldt histórico na fibra primo-potência. Nenhuma seção,
pseudoinversa ou base Householder foi usada.
"""


def render_graph_report(graph: Mapping[str, object]) -> str:
    return f"""# Relação de grafo com proveniência enriquecida

## Estado

Os resultados `PASS_TOWER_NUMBER_DESCENDS_THROUGH_JH_COEQUALIZER` e
`PASS_CLOSED_POST_T0_TOWER_BOUNDARY_RELATION` permanecem válidos: o operador
número age no eixo `j`, enquanto o coequalizer age em `d_J`.

Isso não fornece a descida da perna `A` na faixa nativa. Como a faixa ainda não
foi construída, não há `Qtilde`, não há escalas enriquecidas e não foi testada
a identidade `Qtilde N=Ntilde Qtilde`. O frontier histórico
`{graph['previous_frontier']}` não foi ativado definitivamente; ele pressupõe
uma classificação nativa que ainda falta.

O próximo objeto necessário é o construtor forward persistido que associe, em
cada contribuição C2, os eixos

```text
p_A,tau,d_J,J/H-role,cell,corner,orientation,flags,p_T,j,K,m.
```

Somente então se pode formar `R_native`, calcular `K_native`, decidir se o
modo Möbius é realizável e, se houver witness, ativar o enriquecimento mínimo.
A fronteira atual é `{graph['current_frontier']}`.
"""


def validation_record(
    witness: Mapping[str, object],
    source: Mapping[str, object],
    native: Mapping[str, object],
    divisor: Mapping[str, object],
    graph: Mapping[str, object],
) -> dict[str, object]:
    checks = {
        "ell2_Q_mu_zero": witness["ell_2_witness"]["Q_mu"] == sp.zeros(1, 1),
        "ell2_A_mu_nonzero": witness["ell_2_witness"]["A_even_pre_mu"] != 0,
        "all_exact_mobius_checks_zero": all(
            record["Q_mu"] == 0 for record in witness["general_identity"]["records"]
        ),
        "no_complete_forward_constructor": len(source["complete_generator_candidates"]) == 0,
        "native_range_not_fabricated": not native["R_native_defined"],
        "conditional_enrichment_not_run": not divisor["phase_executed"],
        "enriched_graph_not_overclaimed": not graph["enriched_scales_constructed"],
    }
    if not all(checks.values()):
        raise RuntimeError(f"validation failed: {checks}")
    return {
        "schema": "c2.green.native_range_provenance.validation.v1",
        "checks": checks,
        "all_passed": True,
    }


def generated_paths() -> list[Path]:
    paths = [
        REPORT_RANGE,
        REPORT_MOBIUS,
        REPORT_DIVISOR,
        REPORT_GRAPH,
        Path(__file__),
        TEST_PATH,
    ]
    if RESULT.exists():
        paths.extend(sorted(path for path in RESULT.iterdir() if path.is_file() and path.name != "manifest.json"))
    return sorted(set(path for path in paths if path.exists()))


def write_manifest(integrity: Mapping[str, object]) -> None:
    before = integrity["historical_hashes_before"]
    after = {relative(ROOT / name): sha256_file(ROOT / name) for name in before}
    mismatches = {name: {"before": before[name], "after": after[name]} for name in before if before[name] != after[name]}
    payload = {
        "schema": "c2.green.native_range_provenance.manifest.v1",
        "generated_files": {
            relative(path): {"size": path.stat().st_size, "sha256": sha256_file(path)}
            for path in generated_paths()
        },
        "historical_integrity": {
            "tracked_count": len(before),
            "all_preserved": not mismatches,
            "mismatches": mismatches,
        },
        "frozen_witness_count": integrity["frozen_witness_count"],
        "reverse_section_used": False,
        "pseudoinverse_used": False,
        "Householder_used": False,
        "LP_or_solver_used": False,
        "Green_to_zero_claimed": False,
    }
    if mismatches:
        raise RuntimeError(f"historical artifact changed: {mismatches}")
    json_dump(RESULT / "manifest.json", payload)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--result-dir", type=Path, default=RESULT)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    global RESULT
    RESULT = args.result_dir.resolve()
    RESULT.mkdir(parents=True, exist_ok=True)

    integrity = integrity_audit()
    witness = free_module_witness_audit()
    source = source_contract_audit()
    native = native_range_gate_audit(source)
    divisor = divisor_haar_gate_audit(native)
    graph = enriched_graph_gate_audit(source, divisor)
    summary = build_summary(witness, source, native, divisor, graph)
    validation = validation_record(witness, source, native, divisor, graph)

    payloads = {
        "integrity.json": integrity,
        "free_module_witness.json": witness,
        "constructor_inventory.json": source,
        "native_range_gate.json": native,
        "mobius_kernel.json": {
            "qualification": witness["checkpoint"],
            "ell_2_witness": witness["ell_2_witness"],
            "general_identity": witness["general_identity"],
            "native_range_gate": native,
        },
        "divisor_haar_gate.json": divisor,
        "enriched_graph_gate.json": graph,
        "validation.json": validation,
        "summary.json": summary,
    }
    for name, payload in payloads.items():
        json_dump(RESULT / name, payload)

    REPORT_RANGE.write_text(render_range_report(source, native), encoding="utf-8")
    REPORT_MOBIUS.write_text(render_mobius_report(witness, native), encoding="utf-8")
    REPORT_DIVISOR.write_text(render_divisor_report(divisor), encoding="utf-8")
    REPORT_GRAPH.write_text(render_graph_report(graph), encoding="utf-8")
    write_manifest(integrity)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
