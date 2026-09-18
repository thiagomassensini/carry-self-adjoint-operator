#!/usr/bin/env python3
"""Generate the Lean replay for the centred order-ten N10 certificate.

The quadrature data are produced by
``theta-tenth-bounds-2026-09-17-generate.py``.  This generator only emits the
small final bridge: conservative theta boxes, the six cosine-moment boxes,
and the multivariate Taylor expansion of N10 around the box centres.  The
result is intended to be checked by Lean; the planning screen is not used as
an axiom.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import comb
from pathlib import Path


D = 10**15

# Lower bounds use the already-proved first-mode lower estimate.  Upper bounds
# use the formally replayed first+second-mode compact estimates plus the sharp
# exterior remainder from CompletedNativeThetaTenthSupport.
A_BOX = {
    0: (11516544931740, 11517046272860),
    2: (247316428382, 247328041335),
    4: (20000021893, 20001454250),
    6: (2876933922, 2877230214),
    8: (589716911, 589803742),
    10: (155192558, 155227863),
}

# N10 in the cosine-moment variables, as (coefficient, exponent map).
N10_SPECS = (
    (105, {0: 2, 1: 1, 3: 1, 5: 1}),
    (-180, {0: 2, 1: 1, 4: 2}),
    (-350, {0: 2, 2: 2, 5: 1}),
    (2520, {0: 2, 2: 1, 3: 1, 4: 1}),
    (-2646, {0: 2, 3: 3}),
    (525, {0: 1, 1: 2, 2: 1, 5: 1}),
    (-2205, {0: 1, 1: 2, 3: 1, 4: 1}),
    (-9450, {0: 1, 1: 1, 2: 2, 4: 1}),
    (26460, {0: 1, 1: 1, 2: 1, 3: 2}),
    (-14700, {0: 1, 2: 3, 3: 1}),
    (14175, {1: 3, 2: 1, 4: 1}),
    (-35280, {1: 3, 3: 2}),
    (22050, {1: 2, 2: 2, 3: 1}),
)


def q(x: Q) -> str:
    return f"({x.numerator}/{x.denominator}:ℝ)"


def d(num: int) -> str:
    return f"({num}/{D}:ℝ)"


def add_polynomials(left: dict[tuple[int, ...], Q],
                    right: dict[tuple[int, ...], Q]) -> dict[tuple[int, ...], Q]:
    out = dict(left)
    for key, value in right.items():
        out[key] = out.get(key, Q()) + value
    return out


def centred_expansion() -> tuple[list[tuple[tuple[int, ...], Q]], list[Q], list[Q]]:
    mu = [(Q(lo, D), Q(hi, D)) for lo, hi in (
        (497120738431785, 497120863767065),
        (22971257853146, 22972263438625),
        (2962796777021, 2962936490547),
        (599281349236, 599324394020),
        (160960848696, 160977462757),
        (53035715024, 53043538641),
    )]
    centres = [(lo + hi) / 2 for lo, hi in mu]
    radii = [(hi - lo) / 2 for lo, hi in mu]
    zero = (0, 0, 0, 0, 0, 0)
    total: dict[tuple[int, ...], Q] = {}
    for coefficient, factors in N10_SPECS:
        polynomial: dict[tuple[int, ...], Q] = {zero: Q(coefficient)}
        for index, exponent in factors.items():
            factor: dict[tuple[int, ...], Q] = {}
            for k in range(exponent + 1):
                key = tuple(k if coordinate == index else 0 for coordinate in range(6))
                factor[key] = Q(comb(exponent, k)) * centres[index] ** (exponent - k)
            polynomial = add_polynomials(
                {key: value for key, value in ()},  # keep the operation explicit
                polynomial,
            ) if False else polynomial
            product: dict[tuple[int, ...], Q] = {}
            for left_key, left_value in polynomial.items():
                for right_key, right_value in factor.items():
                    key = tuple(left_key[i] + right_key[i] for i in range(6))
                    product[key] = product.get(key, Q()) + left_value * right_value
            polynomial = product
        total = add_polynomials(total, polynomial)
    terms = [(key, value) for key, value in sorted(total.items()) if value]
    assert len(terms) == 120
    assert terms[0][0] == zero
    return terms[1:], centres, radii


def exponents(key: tuple[int, ...]) -> str:
    return ", ".join(str(x) for x in key)


def product_factors(names: list[str], key: tuple[int, ...]) -> str:
    out = ""
    for name, exponent in zip(names, key):
        if exponent:
            out += f" * {name}^{exponent}"
    return out


def term_expr(key: tuple[int, ...], coefficient: Q) -> str:
    deviations = [f"(m{i} - tenthN10Center{i})" for i in range(6)]
    return f"{q(coefficient)}{product_factors(deviations, key)}"


def bound_expr(key: tuple[int, ...], coefficient: Q) -> str:
    radii = [f"tenthN10Radius{i}" for i in range(6)]
    return f"{q(abs(coefficient))}{product_factors(radii, key)}"


def centre_defs(centres: list[Q], radii: list[Q]) -> str:
    out = []
    for i, value in enumerate(centres):
        out.append(f"private def tenthN10Center{i} : ℝ := {q(value)}")
    for i, value in enumerate(radii):
        out.append(f"private def tenthN10Radius{i} : ℝ := {q(value)}")
    return "\n".join(out) + "\n"


def theta_box_theorem(power: int, lower: int, upper: int) -> str:
    return f'''theorem completedNativeThetaTailMoment_{power}_tenth_certified_bounds :
    {d(lower)} ≤ completedNativeThetaTailMoment {power} ∧
      completedNativeThetaTailMoment {power} ≤ {d(upper)} := by
  have hlow := completedNativeThetaTailMoment_finite_lower {power}
  have hfirstlo := thetaTenth_first_integral_lower_{power}
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    {power} (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_{power}
  have hsecondhi := thetaTenth_second_integral_upper_{power}
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

'''


def moment_box_theorems() -> str:
    return '''theorem completedNativeXiCosineMoment_zero_tenth_certified_bounds :
    (497120738431785/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 0 ∧
      completedNativeXiCosineMoment 0 ≤ (497120863767065/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  have h := completedNativeThetaTailMoment_0_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_one_tenth_certified_bounds :
    (22971257853146/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 1 ∧
      completedNativeXiCosineMoment 1 ≤ (22972263438625/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_one_eq_thetaTailMoments]
  have h0 := completedNativeThetaTailMoment_0_tenth_certified_bounds
  have h2 := completedNativeThetaTailMoment_2_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_two_tenth_certified_bounds :
    (2962796777021/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 2 ∧
      completedNativeXiCosineMoment 2 ≤ (2962936490547/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  have h2 := completedNativeThetaTailMoment_2_tenth_certified_bounds
  have h4 := completedNativeThetaTailMoment_4_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_three_tenth_certified_bounds :
    (599281349236/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 3 ∧
      completedNativeXiCosineMoment 3 ≤ (599324394020/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_three_eq_thetaTailMoments]
  have h4 := completedNativeThetaTailMoment_4_tenth_certified_bounds
  have h6 := completedNativeThetaTailMoment_6_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_four_tenth_certified_bounds :
    (160960848696/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 4 ∧
      completedNativeXiCosineMoment 4 ≤ (160977462757/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_four_eq_thetaTailMoments]
  have h6 := completedNativeThetaTailMoment_6_tenth_certified_bounds
  have h8 := completedNativeThetaTailMoment_8_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_five_tenth_certified_bounds :
    (53035715024/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 5 ∧
      completedNativeXiCosineMoment 5 ≤ (53043538641/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_five_eq_thetaTailMoments]
  have h8 := completedNativeThetaTailMoment_8_tenth_certified_bounds
  have h10 := completedNativeThetaTailMoment_10_tenth_certified_bounds
  constructor <;> linarith

'''


def abs_lemma() -> str:
    return '''private lemma abs_centered_product_le
    (c d0 d1 d2 d3 d4 d5 r0 r1 r2 r3 r4 r5 : ℝ)
    (e0 e1 e2 e3 e4 e5 : ℕ)
    (hd0 : |d0| ≤ r0) (hd1 : |d1| ≤ r1) (hd2 : |d2| ≤ r2)
    (hd3 : |d3| ≤ r3) (hd4 : |d4| ≤ r4) (hd5 : |d5| ≤ r5)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hr3 : 0 ≤ r3) (hr4 : 0 ≤ r4) (hr5 : 0 ≤ r5) :
    |c * d0^e0 * d1^e1 * d2^e2 * d3^e3 * d4^e4 * d5^e5| ≤
      |c| * r0^e0 * r1^e1 * r2^e2 * r3^e3 * r4^e4 * r5^e5 := by
  simp only [abs_mul, abs_pow]
  gcongr

'''


def term_vector(terms: list[tuple[tuple[int, ...], Q]]) -> str:
    entries = [term_expr(key, coefficient) for key, coefficient in terms]
    return "private def tenthN10DeviationTerms (m0 m1 m2 m3 m4 m5 : ℝ) : Fin 119 → ℝ :=\n  ![\n    " + ",\n    ".join(entries) + "\n  ]\n\n"


def bound_vector(terms: list[tuple[tuple[int, ...], Q]]) -> str:
    entries = [bound_expr(key, coefficient) for key, coefficient in terms]
    return "private def tenthN10DeviationBounds : Fin 119 → ℝ :=\n  ![\n    " + ",\n    ".join(entries) + "\n  ]\n\n"


def term_proofs(terms: list[tuple[tuple[int, ...], Q]]) -> str:
    out = ["    fin_cases i"]
    for key, coefficient in terms:
        args = [
            f"(c := {q(coefficient)})",
            *[f"(d{i} := completedNativeXiCosineMoment {i} - tenthN10Center{i})"
              for i in range(6)],
            *[f"(r{i} := tenthN10Radius{i})" for i in range(6)],
            *[f"(e{i} := {key[i]})" for i in range(6)],
            *[f"(hd{i} := hd{i})" for i in range(6)],
            *[f"(hr{i} := hr{i})" for i in range(6)],
        ]
        out.append(
            "    · convert (abs_centered_product_le\n"
            + "      " + " ".join(args)
            + ") using 1 <;>\n"
            + "      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]"
        )
    return "\n".join(out) + "\n"


def main() -> None:
    terms, centres, radii = centred_expansion()
    project = Path(__file__).resolve().parents[1]
    output = project / "CarrySelfAdjointOperator/CompletedNativeTenthOrderHankelPositivity.lean"
    text = '''import CarrySelfAdjointOperator.ThetaTenthMomentCertificateData.CompletedNativeThetaTenthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeTenthOrderHankelMomentForm
import Mathlib.Tactic

namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192

/- The following six theta bounds are conservative: the lower side uses only
the already-proved first-mode lower estimate, while the upper side uses the
two-mode/certified-exterior replay. -/
'''
    for power, (lower, upper) in A_BOX.items():
        text += theta_box_theorem(power, lower, upper)
    text += moment_box_theorems()
    text += centre_defs(centres, radii)
    text += '''private def tenthN10Center : ℝ :=
  canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
    tenthN10Center0 tenthN10Center1 tenthN10Center2
    tenthN10Center3 tenthN10Center4 tenthN10Center5

'''
    text += term_vector(terms)
    text += bound_vector(terms)
    text += '''private def tenthN10Deviation (m0 m1 m2 m3 m4 m5 : ℝ) : ℝ :=
  ∑ i : Fin 119, tenthN10DeviationTerms m0 m1 m2 m3 m4 m5 i

private def tenthN10Error : ℝ :=
  ∑ i : Fin 119, tenthN10DeviationBounds i

'''
    text += abs_lemma()
    text += '''theorem tenthN10_centered_identity (m0 m1 m2 m3 m4 m5 : ℝ) :
    canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
        m0 m1 m2 m3 m4 m5 =
      tenthN10Center + tenthN10Deviation m0 m1 m2 m3 m4 m5 := by
  simp [canonicalCompletedNativeHankelThreeXiTenthMomentNumerator,
    tenthN10Center, tenthN10Center0, tenthN10Center1, tenthN10Center2,
    tenthN10Center3, tenthN10Center4, tenthN10Center5,
    tenthN10Deviation, tenthN10DeviationTerms,
    Fin.sum_univ_succ]
  ring

theorem canonicalCompletedNativeHankelThreeXiTenthMomentNumerator_ge_box_margin :
    (1/1000000000000000:ℝ) ≤
      canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
        (completedNativeXiCosineMoment 0)
        (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2)
        (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4)
        (completedNativeXiCosineMoment 5) := by
  have h0 := completedNativeXiCosineMoment_zero_tenth_certified_bounds
  have h1 := completedNativeXiCosineMoment_one_tenth_certified_bounds
  have h2 := completedNativeXiCosineMoment_two_tenth_certified_bounds
  have h3 := completedNativeXiCosineMoment_three_tenth_certified_bounds
  have h4 := completedNativeXiCosineMoment_four_tenth_certified_bounds
  have h5 := completedNativeXiCosineMoment_five_tenth_certified_bounds
  have hd0 : |completedNativeXiCosineMoment 0 - tenthN10Center0| ≤
      tenthN10Radius0 := by
    rw [abs_le]
    constructor <;> linarith [h0.1, h0.2]
  have hd1 : |completedNativeXiCosineMoment 1 - tenthN10Center1| ≤
      tenthN10Radius1 := by
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hd2 : |completedNativeXiCosineMoment 2 - tenthN10Center2| ≤
      tenthN10Radius2 := by
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have hd3 : |completedNativeXiCosineMoment 3 - tenthN10Center3| ≤
      tenthN10Radius3 := by
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]
  have hd4 : |completedNativeXiCosineMoment 4 - tenthN10Center4| ≤
      tenthN10Radius4 := by
    rw [abs_le]
    constructor <;> linarith [h4.1, h4.2]
  have hd5 : |completedNativeXiCosineMoment 5 - tenthN10Center5| ≤
      tenthN10Radius5 := by
    rw [abs_le]
    constructor <;> linarith [h5.1, h5.2]
  have hr0 : 0 ≤ tenthN10Radius0 := by norm_num [tenthN10Radius0]
  have hr1 : 0 ≤ tenthN10Radius1 := by norm_num [tenthN10Radius1]
  have hr2 : 0 ≤ tenthN10Radius2 := by norm_num [tenthN10Radius2]
  have hr3 : 0 ≤ tenthN10Radius3 := by norm_num [tenthN10Radius3]
  have hr4 : 0 ≤ tenthN10Radius4 := by norm_num [tenthN10Radius4]
  have hr5 : 0 ≤ tenthN10Radius5 := by norm_num [tenthN10Radius5]
  have hterm : ∀ i : Fin 119,
      |tenthN10DeviationTerms
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) i| ≤
        tenthN10DeviationBounds i := by
    intro i
'''
    text += term_proofs(terms)
    text += '''  have htriangle :
      |tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5)| ≤
        ∑ i : Fin 119,
          |tenthN10DeviationTerms
            (completedNativeXiCosineMoment 0)
            (completedNativeXiCosineMoment 1)
            (completedNativeXiCosineMoment 2)
            (completedNativeXiCosineMoment 3)
            (completedNativeXiCosineMoment 4)
            (completedNativeXiCosineMoment 5) i| := by
    unfold tenthN10Deviation
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum :
      (∑ i : Fin 119,
        |tenthN10DeviationTerms
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) i|) ≤
        ∑ i : Fin 119, tenthN10DeviationBounds i := by
    exact Finset.sum_le_sum (fun i _hi => hterm i)
  have herror :
      |tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5)| ≤ tenthN10Error := by
    calc
      _ ≤ ∑ i : Fin 119,
          |tenthN10DeviationTerms
            (completedNativeXiCosineMoment 0)
            (completedNativeXiCosineMoment 1)
            (completedNativeXiCosineMoment 2)
            (completedNativeXiCosineMoment 3)
            (completedNativeXiCosineMoment 4)
            (completedNativeXiCosineMoment 5) i| := htriangle
      _ ≤ ∑ i : Fin 119, tenthN10DeviationBounds i := hsum
      _ = tenthN10Error := rfl
  have hcenter : (23/100000000000000:ℝ) ≤ tenthN10Center := by
    norm_num [tenthN10Center, tenthN10Center0, tenthN10Center1,
      tenthN10Center2, tenthN10Center3, tenthN10Center4, tenthN10Center5,
      canonicalCompletedNativeHankelThreeXiTenthMomentNumerator]
  have herr : tenthN10Error ≤ (223/1000000000000000:ℝ) := by
    norm_num [tenthN10Error, tenthN10DeviationBounds,
      tenthN10Radius0, tenthN10Radius1, tenthN10Radius2,
      tenthN10Radius3, tenthN10Radius4, tenthN10Radius5,
      Fin.sum_univ_succ]
  have hdevlow :
      -tenthN10Error ≤ tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) :=
    (abs_le.mp herror).1
  have hid := tenthN10_centered_identity
    (completedNativeXiCosineMoment 0)
    (completedNativeXiCosineMoment 1)
    (completedNativeXiCosineMoment 2)
    (completedNativeXiCosineMoment 3)
    (completedNativeXiCosineMoment 4)
    (completedNativeXiCosineMoment 5)
  calc
    (1/1000000000000000:ℝ) ≤ tenthN10Center - tenthN10Error := by
      linarith
    _ ≤ tenthN10Center + tenthN10Deviation
        (completedNativeXiCosineMoment 0)
        (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2)
        (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4)
        (completedNativeXiCosineMoment 5) := by
      linarith
    _ = _ := hid.symm

theorem canonicalCompletedNativeHankel_three_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det := by
  rw [canonicalCompletedNativeHankel_three_det_eq_xiTenthMomentRatio]
  have hn := canonicalCompletedNativeHankelThreeXiTenthMomentNumerator_ge_box_margin
  have hm := completedNativeXiCosineMoment_pos 0
  have hd : 0 < 36578304000 * completedNativeXiCosineMoment 0 ^ 5 := by
    positivity
  exact div_pos (by linarith) hd

end
end CarrySelfAdjointOperator
'''
    output.write_text(text, encoding="utf-8")
    print(output)
    print(f"centred terms={len(terms)}")


if __name__ == "__main__":
    main()
