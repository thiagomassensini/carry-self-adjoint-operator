#!/usr/bin/env python3
"""Generate rational Lean certificates for theta moments through order eight."""
from fractions import Fraction as F
from math import ceil, factorial, floor
from pathlib import Path
import argparse
import json

parser = argparse.ArgumentParser()
parser.add_argument("--output-directory", required=True)
args = parser.parse_args()

N = 256
POWERS = [0, 2, 4, 6, 8]
out = Path(args.output_directory)
out.mkdir(parents=True, exist_ok=True)

def term(x):
    return f"({x.numerator}/{x.denominator}:ℝ)"

def exp_lower(x):
    return sum((x / 32) ** i / factorial(i) for i in range(12)) ** 32

def exp_upper(x):
    return (sum((x / 32) ** i / factorial(i) for i in range(12)) +
            (x / 32) ** 12 * F(13, factorial(12) * 12)) ** 32

nodes = {F(j, N) for j in range(N + 1)}
for p in POWERS:
    for j in range(N):
        a, b = F(j, N), F(j + 1, N)
        mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
        first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
        nodes.add(first / mass)

records = []
for ident, q in enumerate(sorted(nodes)):
    el = F(floor(exp_lower(2 * q) * 10 ** 12), 10 ** 12)
    eu = F(ceil(exp_upper(2 * q) * 10 ** 12), 10 ** 12)
    arglo = F(3141592, 10 ** 6) * el - q / 2
    arghi = F(3141593, 10 ** 6) * eu - q / 2
    lower = F(floor(2 / exp_upper(arghi) * 10 ** 14), 10 ** 14)
    upper = F(ceil(2 / exp_lower(arglo) * 10 ** 14), 10 ** 14)
    assert 0 <= arglo <= arghi <= 32 and 0 <= lower <= upper
    records.append({"id": ident, "q": str(q), "l": str(lower), "r": str(upper)})
    group = ident // 32
    path = out / f"ThetaNodes{group:02d}.lean"
    if ident % 32 == 0:
        path.write_text(
            "import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds\n\n"
            "namespace CarrySelfAdjointOperator\nset_option maxHeartbeats 4000000\n\n")
    code = f'''theorem thetaFirstMode_refined_node_{ident:04d} :
    {term(lower)} ≤ thetaFirstMode {term(q)} ∧ thetaFirstMode {term(q)} ≤ {term(upper)} := by
  apply thetaFirstMode_node_bounds {term(q)} {term(el)} {term(eu)} {term(lower)} {term(upper)}
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

'''
    with path.open("a") as handle:
        handle.write(code)
    if ident % 32 == 31 or ident == len(nodes) - 1:
        with path.open("a") as handle:
            handle.write("end CarrySelfAdjointOperator\n")

(out / "nodes.json").write_text(json.dumps(records, indent=2))
by_q = {F(r["q"]): r for r in records}

def node_name(q):
    return f"thetaFirstMode_refined_node_{by_q[q]['id']:04d}"

def low(q):
    return F(by_q[q]["l"])

def high(q):
    return F(by_q[q]["r"])

node_imports = "".join(
    f"import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes{group:02d}\n"
    for group in range((len(nodes) + 31) // 32))
cell_files = []
totals = {}
for p in POWERS:
    lows, highs = [], []
    for j in range(N):
        a, b = F(j, N), F(j + 1, N)
        mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
        first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
        mean = first / mass
        lower = low(mean) * mass
        upper = ((b * high(a) - a * high(b)) * mass +
                 (high(b) - high(a)) * first) / (b - a)
        lows.append(lower)
        highs.append(upper)
        group = j // 32
        path = out / f"ThetaCells{p}_{group}.lean"
        if j % 32 == 0:
            path.write_text(
                node_imports +
                "import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature\n\n"
                "namespace CarrySelfAdjointOperator\nnoncomputable section\n"
                "set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n")
            cell_files.append(path.stem)
        code = f'''theorem thetaFirstMode_refined_cell_lower_{p}_{j:03d} :
    {term(lower)} ≤ ∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower {p} {term(a)} {term(b)} {term(mean)} {term(low(mean))}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) ({node_name(mean)}).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_{p}_{j:03d} :
    (∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x) ≤ {term(upper)} := by
  have h := thetaFirstMode_weighted_cell_upper {p} {term(a)} {term(b)} {term(high(a))} {term(high(b))}
    (by norm_num) (by norm_num) ({node_name(a)}).2 ({node_name(b)}).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

'''
        with path.open("a") as handle:
            handle.write(code)
        if j % 32 == 31:
            with path.open("a") as handle:
                handle.write("end\nend CarrySelfAdjointOperator\n")
    totals[p] = {"L": sum(lows), "U": sum(highs)}

(out / "cell-summary.json").write_text(json.dumps(
    {p: {key: str(value) for key, value in result.items()} for p, result in totals.items()}, indent=2))

aggregate = "".join(
    f"import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.{name}\n"
    for name in cell_files)
aggregate += "\nopen MeasureTheory\nnamespace CarrySelfAdjointOperator\nnoncomputable section\n"
aggregate += "set_option maxHeartbeats 16000000\nset_option maxRecDepth 8192\n\n"
aggregate += '''theorem thetaFirstMode_refined_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range 256, ∫ x in ((j:ℝ)/256)..(((j+1:ℕ):ℝ)/256), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < 256 → IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x)
      volume ((k:ℝ)/256) (((k+1:ℕ):ℝ)/256) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

'''
for p in POWERS:
    for side, key in [("lower", "L"), ("upper", "U")]:
        value = totals[p][key]
        statement = (f"{term(value)} ≤ (∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x)"
                     if side == "lower" else
                     f"(∫ x in (0:ℝ)..1, x^{p}*thetaFirstMode x) ≤ {term(value)}")
        terms = [f"thetaFirstMode_refined_cell_{side}_{p}_{j:03d}" for j in range(N)]
        while len(terms) > 1:
            terms = [f"(add_le_add {terms[i]} {terms[i+1]})"
                     for i in range(0, len(terms), 2)]
        aggregate += f'''theorem thetaFirstMode_refined_integral_{side}_{p} :
    {statement} := by
  have h := {terms[0]}
  rw [thetaFirstMode_refined_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
aggregate += "end\nend CarrySelfAdjointOperator\n"
(out / "CompletedNativeThetaEighthMomentCertificate.lean").write_text(aggregate)

for p, values in totals.items():
    print(p, "first-mode", float(values["L"]), float(values["U"]))
