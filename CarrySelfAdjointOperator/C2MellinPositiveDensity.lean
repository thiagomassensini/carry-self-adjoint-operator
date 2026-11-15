import CarrySelfAdjointOperator.CompletedNativeC2ExactTailTransport
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

open Set
open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The positive C2 cell density from the source-first Mellin representation.
The seed `exp (-x)` is kept separate in `nativeC2MellinDensity`. -/
def nativeC2MellinOmega0 (x : ℝ) : ℝ :=
  Real.exp (-x) ^ 3 * (1 - Real.exp (-x)) /
    ((1 + Real.exp (-x)) * (1 + Real.exp (-x) ^ 2))

/-- The positive source density: the original seed plus the closed-form
`omega0` term whose geometric expansion is to be identified with the cells. -/
def nativeC2MellinDensity (x : ℝ) : ℝ :=
  Real.exp (-x) + nativeC2MellinOmega0 x

/-- The positive tail density proposed after cutoff `M`. -/
def nativeC2MellinTailDensity (M : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((4 : ℝ) * (M : ℝ) * x)) * nativeC2MellinOmega0 x

/-- The positive head density proposed at cutoff `M`. -/
def nativeC2MellinHeadDensity (M : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) +
    (1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x))) * nativeC2MellinOmega0 x

theorem nativeC2Mellin_exp_neg_pos_lt_one {x : ℝ} (hx : 0 < x) :
    0 < Real.exp (-x) ∧ Real.exp (-x) < 1 := by
  constructor
  · exact Real.exp_pos _
  · exact Real.exp_lt_one_iff.mpr (by linarith)

/-- The quotient definition of `omega0` agrees with its hyperbolic-sine form. -/
theorem nativeC2MellinOmega0_eq_exp_sinh {x : ℝ} (hx : 0 < x) :
    nativeC2MellinOmega0 x =
      Real.exp (-4 * x) * (4 * Real.sinh (x / 2) ^ 2) /
        (1 - Real.exp (-4 * x)) := by
  let q := Real.exp (-x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsinh : Real.sinh (x / 2) =
      (Real.exp (x / 2) - Real.exp (-(x / 2))) / 2 := by
    rw [← Complex.sinh_ofReal_re]
    have h : Complex.sinh ((x / 2 : ℝ) : ℂ) =
        (((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2 : ℝ) : ℂ) := by
      simp [Complex.sinh, Complex.ofReal_exp]
    exact congrArg Complex.re h
  have hexpHalf : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hsqPos : Real.exp (x / 2) ^ 2 = Real.exp x := by
    calc
      Real.exp (x / 2) ^ 2 = Real.exp (x / 2) * Real.exp (x / 2) := by ring
      _ = Real.exp x := by rw [← Real.exp_add]; congr 1; ring
  have hsqNeg : Real.exp (-(x / 2)) ^ 2 = q := by
    calc
      Real.exp (-(x / 2)) ^ 2 =
          Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by ring
      _ = q := by
        rw [← Real.exp_add]
        dsimp [q]
        congr 1; ring
  have hqInv : Real.exp x = q⁻¹ := by
    field_simp [ne_of_gt hq0]
    dsimp [q]
    rw [← Real.exp_add]
    norm_num
  have hq4 : Real.exp (-4 * x) = q ^ 4 := by
    calc
      Real.exp (-4 * x) = Real.exp (4 * (-x)) := by congr 1; ring
      _ = Real.exp (-x) ^ 4 := Real.exp_nat_mul _ _
      _ = q ^ 4 := rfl
  have hkernel : 4 * Real.sinh (x / 2) ^ 2 = Real.exp x - 2 + q := by
    rw [hsinh]
    calc
      4 * ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) ^ 2 =
          Real.exp (x / 2) ^ 2 - 2 *
            (Real.exp (x / 2) * Real.exp (-(x / 2))) +
            Real.exp (-(x / 2)) ^ 2 := by ring
      _ = Real.exp x - 2 + q := by rw [hexpHalf, hsqPos, hsqNeg]; ring
  have hden : 0 < 1 - q ^ 4 := by
    have hfactor : 1 - q ^ 4 = (1 - q) * (1 + q) * (1 + q ^ 2) := by ring
    rw [hfactor]
    positivity
  rw [nativeC2MellinOmega0]
  simp only [show Real.exp (-x) = q by rfl]
  rw [hq4, hkernel, hqInv]
  field_simp [ne_of_gt hq0, ne_of_gt hq1, ne_of_gt hden]
  ring

theorem nativeC2MellinOmega0_pos {x : ℝ} (hx : 0 < x) :
    0 < nativeC2MellinOmega0 x := by
  unfold nativeC2MellinOmega0
  rcases nativeC2Mellin_exp_neg_pos_lt_one hx with ⟨hq0, hq1⟩
  positivity

theorem nativeC2MellinOmega0_le_exp_neg {x : ℝ} (hx : 0 < x) :
    nativeC2MellinOmega0 x ≤ Real.exp (-x) := by
  let q := Real.exp (-x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqle : q ≤ 1 := hq1.le
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hnum : q ^ 3 * (1 - q) ≤ q := by
    calc
      q ^ 3 * (1 - q) ≤ q ^ 3 :=
        mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ q := by
        calc
          q ^ 3 = q ^ 2 * q := by ring
          _ ≤ 1 * q := mul_le_mul_of_nonneg_right hq2 hq0.le
          _ = q := by ring
  have hden : 1 ≤ (1 + q) * (1 + q ^ 2) := by nlinarith
  have hden0 : 0 < (1 + q) * (1 + q ^ 2) := by positivity
  rw [nativeC2MellinOmega0, show Real.exp (-x) = q by rfl]
  rw [div_le_iff₀ hden0]
  have hdenmul : q ≤ q * ((1 + q) * (1 + q ^ 2)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hden hq0.le
  exact hnum.trans hdenmul

theorem nativeC2MellinDensity_pos {x : ℝ} (hx : 0 < x) :
    0 < nativeC2MellinDensity x := by
  unfold nativeC2MellinDensity
  exact add_pos (Real.exp_pos _) (nativeC2MellinOmega0_pos hx)

theorem nativeC2MellinDensity_le_two_exp_neg {x : ℝ} (hx : 0 < x) :
    nativeC2MellinDensity x ≤ 2 * Real.exp (-x) := by
  unfold nativeC2MellinDensity
  have h := nativeC2MellinOmega0_le_exp_neg hx
  linarith

/-- Exact head-tail repartition at the level of densities. -/
theorem nativeC2MellinHead_add_tail_eq_density (M : ℕ) (x : ℝ) :
    nativeC2MellinHeadDensity M x + nativeC2MellinTailDensity M x =
      nativeC2MellinDensity x := by
  unfold nativeC2MellinHeadDensity nativeC2MellinTailDensity
    nativeC2MellinDensity
  ring

theorem nativeC2MellinTailDensity_nonneg (M : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ nativeC2MellinTailDensity M x := by
  unfold nativeC2MellinTailDensity
  exact mul_nonneg (Real.exp_pos _).le (nativeC2MellinOmega0_pos hx).le

theorem nativeC2MellinHeadDensity_pos (M : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < nativeC2MellinHeadDensity M x := by
  unfold nativeC2MellinHeadDensity
  have hMx : 0 ≤ (4 : ℝ) * (M : ℝ) * x := by positivity
  have hdecay : Real.exp (-((4 : ℝ) * (M : ℝ) * x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hcoeff : 0 ≤ 1 - Real.exp (-((4 : ℝ) * (M : ℝ) * x)) := by linarith
  exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (mul_nonneg hcoeff
    (nativeC2MellinOmega0_pos hx).le)

/-- Euler's Mellin transform for one exponential rate, in the exact real form
used to transform each C2 seed or bracket leg. -/
theorem nativeC2Mellin_exponential_mellin
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * Real.exp (-(r * x))) =
      (1 / r) ^ s * Real.Gamma s := by
  exact Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr

/-- The real-source Mellin integral. The source is explicitly the package's
`exp(-x) + omega0(x)` density. -/
def nativeC2MellinSourceIntegral (s : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (s - 1) * nativeC2MellinDensity x

/-- The order-`r` logarithmic Mellin moment of the positive source. -/
def nativeC2MellinLogMoment (s : ℝ) (r : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ),
    x ^ (s - 1) * (Real.log x) ^ r * nativeC2MellinDensity x

/-- Raw Mellin-log moments normalized by the source mass, with `m₀ = 1` by
definition as in the cumulant recurrence. -/
def nativeC2MellinNormalizedMoment (s : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 1 else
    nativeC2MellinLogMoment s r / nativeC2MellinSourceIntegral s

@[simp] theorem nativeC2MellinNormalizedMoment_zero (s : ℝ) :
    nativeC2MellinNormalizedMoment s 0 = 1 := by
  simp [nativeC2MellinNormalizedMoment]

/-- Precise differentiation-under-the-integral obligation for every fixed
logarithmic-moment order. -/
def nativeC2MellinIteratedDerivativeObligation (s : ℝ) : Prop :=
  ∀ r : ℕ,
    iteratedDeriv r nativeC2MellinSourceIntegral s = nativeC2MellinLogMoment s r

/-- The original C2 infinite bracket chart, retained as the Mellin target.
This is an alias for the repository's source chart, not an integral-defined
replacement. -/
def nativeC2MellinOriginalV (s : ℂ) : ℂ := bracketCharacteristic 2 s

/-- Exact full-source Gamma identification still required to finish the
integral-to-series step.  The right-hand side is the original C2 chart. -/
def nativeC2MellinGammaIdentificationObligation (s : ℝ) : Prop :=
  0 < s → s < 1 →
    nativeC2MellinSourceIntegral s =
      Real.Gamma s * (nativeC2MellinOriginalV (s : ℂ)).re

/-- Cutoff form of the head identification obligation, stated against the
repository's original finite C2 chart. -/
def nativeC2MellinHeadGammaIdentificationObligation (M : ℕ) (s : ℝ) : Prop :=
  0 < s →
    (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * nativeC2MellinHeadDensity M x) =
      Real.Gamma s * (finiteBracketCharacteristic 2 M (s : ℂ)).re

/-- Cutoff form of the tail identification obligation, stated against the
exact omitted-center tail already defined in the repository. -/
def nativeC2MellinTailGammaIdentificationObligation (M : ℕ) (s : ℝ) : Prop :=
  0 < s → s < 1 →
    (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * nativeC2MellinTailDensity M x) =
      Real.Gamma s * (nativeC2ExactCenterTail M (s : ℂ)).re

end

end CarrySelfAdjointOperator
