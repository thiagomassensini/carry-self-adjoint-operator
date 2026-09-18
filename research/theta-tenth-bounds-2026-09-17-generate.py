#!/usr/bin/env python3
"""Generate the rational first/second-mode order-ten theta certificate.

The planning screen deliberately stays separate from this generator.  This
file emits Lean declarations only after the exact rational node boxes have
been selected.  The second-mode cells use the convexity lemmas in
``CompletedNativeThetaSecondModeQuadrature``; no first-mode theorem is reused
at the second mode by type coercion or by an unchecked numerical assumption.
"""

from __future__ import annotations

import argparse
import importlib.util
from fractions import Fraction as Q
from pathlib import Path


def load_screen_module():
    here = Path(__file__).resolve().parent
    screen_path = here / "theta-tenth-screen-2026-09-17.py"
    spec = importlib.util.spec_from_file_location("theta_tenth_screen", screen_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {screen_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def term(x: Q) -> str:
    return f"({x.numerator}/{x.denominator}:ℝ)"


def balanced_add(names: list[str]) -> str:
    current = names
    while len(current) > 1:
        if len(current) % 2:
            current = [
                f"add_le_add {current[i]} {current[i + 1]}"
                for i in range(0, len(current) - 1, 2)
            ] + [current[-1]]
        else:
            current = [
                f"(add_le_add {current[i]} {current[i + 1]})"
                for i in range(0, len(current), 2)
            ]
    return current[0]


def node_set(screen, cells: int) -> list[Q]:
    nodes = {Q(j, cells) for j in range(cells + 1)}
    for p in screen.POWERS:
        for j in range(cells):
            a, b = Q(j, cells), Q(j + 1, cells)
            mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
            first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
            nodes.add(first / mass)
    return sorted(nodes)


def mode_integral_boxes(nodes: list[Q], cells: int, node_bounds,
                        powers, mode: int) -> dict[int, tuple[Q, Q]]:
    boxes: dict[int, tuple[Q, Q]] = {}
    for p in powers:
        lower, upper = Q(), Q()
        for j in range(cells):
            a, b = Q(j, cells), Q(j + 1, cells)
            mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
            first = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
            mean = first / mass
            mean_lo, _ = node_bounds[mean][mode]
            _, a_hi = node_bounds[a][mode]
            _, b_hi = node_bounds[b][mode]
            lower += mean_lo * mass
            upper += ((b * a_hi - a * b_hi) * mass +
                      (b_hi - a_hi) * first) / (b - a)
        boxes[p] = lower, upper
    return boxes


def clean_generated(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    for pattern in ("ThetaNodes*.lean", "ThetaCells*.lean",
                    "CompletedNativeThetaTenthMomentCertificate.lean",
                    "nodes.json", "cell-summary.json"):
        for path in out.glob(pattern):
            path.unlink()


def module_prefix(project_root: Path, out: Path) -> str:
    relative = out.relative_to(project_root).with_suffix("")
    return ".".join(relative.parts)


def write_nodes(out: Path, prefix: str, screen, nodes: list[Q], scale: int,
                groupsize: int, node_bounds, inner_bounds) -> dict[Q, int]:
    indices: dict[Q, int] = {}
    paths: dict[int, Path] = {}
    for index, q in enumerate(nodes):
        indices[q] = index
        group = index // groupsize
        path = out / f"ThetaNodes{group:03d}.lean"
        if index % groupsize == 0:
            path.write_text(
                "import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature\n\n"
                "namespace CarrySelfAdjointOperator\nnoncomputable section\n"
                "set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n",
                encoding="utf-8")
            paths[group] = path
        el, eu = inner_bounds[q]
        l1, r1 = node_bounds[q][0]
        l2, r2 = node_bounds[q][1]
        code = f'''theorem thetaTenth_node_{index:04d} :
    {term(l1)} ≤ thetaFirstMode {term(q)} ∧
      thetaFirstMode {term(q)} ≤ {term(r1)} ∧
      {term(l2)} ≤ thetaSecondMode {term(q)} ∧
      thetaSecondMode {term(q)} ≤ {term(r2)} := by
  have hfirst : {term(l1)} ≤ thetaFirstMode {term(q)} ∧
      thetaFirstMode {term(q)} ≤ {term(r1)} := by
    apply thetaFirstMode_node_bounds_d20 {term(q)} {term(el)} {term(eu)}
      {term(l1)} {term(r1)}
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : {term(l2)} ≤ thetaSecondMode {term(q)} ∧
      thetaSecondMode {term(q)} ≤ {term(r2)} := by
    apply thetaSecondMode_node_bounds_d20 {term(q)} {term(el)} {term(eu)}
      {term(l2)} {term(r2)}
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

'''
        path = paths[group]
        with path.open("a", encoding="utf-8") as handle:
            handle.write(code)
        if index % groupsize == groupsize - 1 or index == len(nodes) - 1:
            with path.open("a", encoding="utf-8") as handle:
                handle.write("end\nend CarrySelfAdjointOperator\n")
    return indices


def write_cells(out: Path, prefix: str, screen, nodes: list[Q], indices: dict[Q, int],
                node_bounds, cells: int, groupsize: int) -> list[str]:
    names: list[str] = []
    node_imports = "".join(
        f"import {prefix}.ThetaNodes{group:03d}\n"
        for group in range((len(nodes) + groupsize - 1) // groupsize))
    for j0 in range(0, cells, groupsize):
        group = j0 // groupsize
        path = out / f"ThetaCells{group:03d}.lean"
        path.write_text(
            node_imports +
            "import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature\n\n"
            "namespace CarrySelfAdjointOperator\nnoncomputable section\n"
            "set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n\n",
            encoding="utf-8")
        names.append(path.stem)
        with path.open("a", encoding="utf-8") as handle:
            for j in range(j0, min(j0 + groupsize, cells)):
                for p in screen.POWERS:
                    a, b = Q(j, cells), Q(j + 1, cells)
                    mass = (b ** (p + 1) - a ** (p + 1)) / (p + 1)
                    first_mass = (b ** (p + 2) - a ** (p + 2)) / (p + 2)
                    mean = first_mass / mass
                    mean_l1, _ = node_bounds[mean][0]
                    _, a_u1 = node_bounds[a][0]
                    _, b_u1 = node_bounds[b][0]
                    mean_l2, _ = node_bounds[mean][1]
                    _, a_u2 = node_bounds[a][1]
                    _, b_u2 = node_bounds[b][1]
                    l1 = mean_l1 * mass
                    u1 = ((b * a_u1 - a * b_u1) * mass +
                          (b_u1 - a_u1) * first_mass) / (b - a)
                    l2 = mean_l2 * mass
                    u2 = ((b * a_u2 - a * b_u2) * mass +
                          (b_u2 - a_u2) * first_mass) / (b - a)
                    node_mean = f"thetaTenth_node_{indices[mean]:04d}"
                    node_a = f"thetaTenth_node_{indices[a]:04d}"
                    node_b = f"thetaTenth_node_{indices[b]:04d}"
                    first_lower = f"thetaTenth_first_cell_lower_{p}_{j:03d}"
                    first_upper = f"thetaTenth_first_cell_upper_{p}_{j:03d}"
                    second_lower = f"thetaTenth_second_cell_lower_{p}_{j:03d}"
                    second_upper = f"thetaTenth_second_cell_upper_{p}_{j:03d}"
                    handle.write(f'''theorem {first_lower} :
    {term(l1)} ≤ ∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower {p} {term(a)} {term(b)}
      {term(mean)} {term(mean_l1)}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    ({node_mean}).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem {first_upper} :
    (∫ x in {term(a)}..{term(b)}, x^{p}*thetaFirstMode x) ≤ {term(u1)} := by
  have h := thetaFirstMode_weighted_cell_upper {p} {term(a)} {term(b)}
      {term(a_u1)} {term(b_u1)}
    (by norm_num) (by norm_num) ({node_a}).2.1 ({node_b}).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem {second_lower} :
    {term(l2)} ≤ ∫ x in {term(a)}..{term(b)}, x^{p}*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower {p} {term(a)} {term(b)}
      {term(mean)} {term(mean_l2)}
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    ({node_mean}).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem {second_upper} :
    (∫ x in {term(a)}..{term(b)}, x^{p}*thetaSecondMode x) ≤ {term(u2)} := by
  have h := thetaSecondMode_weighted_cell_upper {p} {term(a)} {term(b)}
      {term(a_u2)} {term(b_u2)}
    (by norm_num) (by norm_num) ({node_a}).2.2.2 ({node_b}).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

''')
            handle.write("end\nend CarrySelfAdjointOperator\n")
    return names


def write_aggregate(out: Path, prefix: str, screen, cells: int,
                    cell_modules: list[str], first: dict[int, tuple[Q, Q]],
                    second: dict[int, tuple[Q, Q]], groupsize: int) -> None:
    path = out / "CompletedNativeThetaTenthMomentCertificate.lean"
    imports = "".join(f"import {prefix}.{name}\n" for name in cell_modules)
    powers = list(screen.POWERS)
    text = imports + '''
open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem thetaTenth_first_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaFirstMode x) =
      ∑ j ∈ Finset.range CELLS, ∫ x in ((j:ℝ)/CELLS)..
        (((j+1:ℕ):ℝ)/CELLS), x^p*thetaFirstMode x := by
  have hint : ∀ k : ℕ, k < CELLS →
      IntervalIntegrable (fun x : ℝ ↦ x^p*thetaFirstMode x)
        volume ((k:ℝ)/CELLS) (((k+1:ℕ):ℝ)/CELLS) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaFirstMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

theorem thetaTenth_second_integral_eq_sum_cells (p : ℕ) :
    (∫ x in (0:ℝ)..1, x^p*thetaSecondMode x) =
      ∑ j ∈ Finset.range CELLS, ∫ x in ((j:ℝ)/CELLS)..
        (((j+1:ℕ):ℝ)/CELLS), x^p*thetaSecondMode x := by
  have hint : ∀ k : ℕ, k < CELLS →
      IntervalIntegrable (fun x : ℝ ↦ x^p*thetaSecondMode x)
        volume ((k:ℝ)/CELLS) (((k+1:ℕ):ℝ)/CELLS) := by
    intro k _
    apply Continuous.intervalIntegrable
    unfold thetaSecondMode
    fun_prop
  simpa using (intervalIntegral.sum_integral_adjacent_intervals hint).symm

'''.replace("CELLS", str(cells))

    for mode, boxes, stem in (("first", first, "thetaTenth_first"),
                              ("second", second, "thetaTenth_second")):
        for p in powers:
            lower_names = [f"{stem}_cell_lower_{p}_{j:03d}" for j in range(cells)]
            upper_names = [f"{stem}_cell_upper_{p}_{j:03d}" for j in range(cells)]
            lower_tree = balanced_add(lower_names)
            upper_tree = balanced_add(upper_names)
            lower, upper = boxes[p]
            text += f'''theorem {stem}_integral_lower_{p} :
    {term(lower)} ≤ (∫ x in (0:ℝ)..1, x^{p}*{'thetaFirstMode' if mode == 'first' else 'thetaSecondMode'} x) := by
  have h := {lower_tree}
  rw [{stem}_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

theorem {stem}_integral_upper_{p} :
    (∫ x in (0:ℝ)..1, x^{p}*{'thetaFirstMode' if mode == 'first' else 'thetaSecondMode'} x) ≤ {term(upper)} := by
  have h := {upper_tree}
  rw [{stem}_integral_eq_sum_cells]
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

'''
    text += "end\nend CarrySelfAdjointOperator\n"
    path.write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", required=True)
    parser.add_argument("--cells", type=int, default=512)
    parser.add_argument("--node-decimals", type=int, default=20)
    parser.add_argument("--groupsize", type=int, default=32)
    args = parser.parse_args()
    if args.cells <= 0 or args.groupsize <= 0:
        raise SystemExit("--cells and --groupsize must be positive")
    project_root = Path(__file__).resolve().parents[1]
    out = (project_root / args.output_directory).resolve()
    if not out.is_relative_to(project_root):
        raise SystemExit("output directory must be inside the repository")
    clean_generated(out)
    screen = load_screen_module()
    scale = 10 ** args.node_decimals
    nodes = node_set(screen, args.cells)
    print(f"nodes={len(nodes)}; cells={args.cells}; scale=10^{args.node_decimals}")
    prefix = module_prefix(project_root, out)
    inner_bounds = {
        q: (Q(screen.qfloor(screen.exp_lower(2 * q) * scale), scale),
            Q(screen.qceil(screen.exp_upper(2 * q) * scale), scale))
        for q in nodes
    }
    node_bounds = {q: (screen.node_box(q, scale, 1),
                       screen.node_box(q, scale, 2)) for q in nodes}
    indices = write_nodes(out, prefix, screen, nodes, scale, args.groupsize,
                          node_bounds, inner_bounds)
    first = mode_integral_boxes(nodes, args.cells, node_bounds, screen.POWERS, 0)
    second = mode_integral_boxes(nodes, args.cells, node_bounds, screen.POWERS, 1)
    cells = write_cells(out, prefix, screen, nodes, indices, node_bounds,
                        args.cells, args.groupsize)
    write_aggregate(out, prefix, screen, args.cells, cells, first, second,
                    args.groupsize)
    print("first-mode integral boxes")
    for p in screen.POWERS:
        print(p, float(first[p][0]), float(first[p][1]))
    print("second-mode integral boxes")
    for p in screen.POWERS:
        print(p, float(second[p][0]), float(second[p][1]))


if __name__ == "__main__":
    main()
