import CarrySelfAdjointOperator.CompletedNativeCentralCoisometricDefectFlatness
import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
import CarrySelfAdjointOperator.CompletedC3FourCornerTaylorGram
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Auto
import Mathlib.Tactic

/-!
# The first polarized radial Herglotz section

The one-point Herglotz section only sees the central ruler `h₀`.  On the
first genuinely polarized section, sampled at `i h` and `2 i h`, the reduced
even-coordinate germ gives the exact matrix

`!![L(-h²) + conj L(-h²), 2/3 * (2 L(-4h²) + conj L(-h²));
    2/3 * (L(-h²) + 2 conj L(-4h²)), L(-4h²) + conj L(-4h²)]`.

Its determinant vanishes at the center and has first `t = h²` derivative
`4 h₀ h₁`.  Thus strict positivity of the first two canonical moments closes
the two-point radial Herglotz gate.  A later section connects `h₁ > 0` to the
first odd enriched TFVD diagonal.
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace CarrySelfAdjointOperator

open Filter

noncomputable section

-- Keep real differentiation of complex-valued radial functions on the
-- canonical restriction-of-scalars normed-space instance used by
-- `HasDerivAt.comp_ofReal` and `Complex.conjCLE`.
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal

/-! ## A two-by-two complex Schur test -/

/-- A Hermitian two-by-two matrix is positive semidefinite when its first
diagonal is strictly positive and its scalar Schur complement is
nonnegative. -/
theorem complexFinTwo_posSemidef_of_schur
    (a b d : ℂ) (ha : 0 < a)
    (hschur : 0 ≤ d - conj b * a⁻¹ * b) :
    (!![a, b; conj b, d] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
  let A : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal (fun _ ↦ a)
  let B : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ ↦ b
  let D : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal (fun _ ↦ d)
  have hA : A.PosDef := by
    exact Matrix.PosDef.diagonal (fun _ ↦ ha)
  letI : Invertible A := hA.isUnit.invertible
  have hcomplement : (D - star B * A⁻¹ * B).PosSemidef := by
    have heq : D - star B * A⁻¹ * B =
        Matrix.diagonal (fun _ : Fin 1 ↦ d - conj b * a⁻¹ * b) := by
      ext i j
      fin_cases i
      fin_cases j
      simp [A, B, D, Matrix.mul_apply]
    rw [heq, Matrix.posSemidef_diagonal_iff]
    exact fun _ ↦ hschur
  have hblock : (Matrix.fromBlocks A B (star B) D).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hcomplement
  let e : (Fin 1 ⊕ Fin 1) ≃ Fin 2 := finSumFinEquiv
  have hreindexed := hblock.submatrix e.symm
  convert hreindexed using 1
  ext i j
  fin_cases i <;> fin_cases j
  · change a = A 0 0
    simp [A]
  · change b = B 0 0
    rfl
  · change conj b = (star B) 0 0
    rfl
  · change d = D 0 0
    simp [D]

/-- Determinant form of the two-by-two complex Schur test. -/
theorem complexFinTwo_posSemidef_of_det
    (a b d : ℂ) (ha : 0 < a)
    (hdet : 0 ≤ a * d - b * conj b) :
    (!![a, b; conj b, d] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
  apply complexFinTwo_posSemidef_of_schur a b d ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    0 ≤ a⁻¹ * (a * d - b * conj b) :=
      mul_nonneg (inv_nonneg.mpr ha.le) hdet
    _ = d - conj b * a⁻¹ * b := by
      field_simp [ha0]

/-! ## Reduced two-point germ -/

/-- The reduced logarithmic derivative at the first squared radial point. -/
def completedNativeReducedRadialHerglotzFirst (t : ℝ) : ℂ :=
  completedNativeLogDerivative (-(t : ℂ))

/-- The reduced logarithmic derivative at the second squared radial point. -/
def completedNativeReducedRadialHerglotzSecond (t : ℝ) : ℂ :=
  completedNativeLogDerivative (-((t : ℂ) * 4))

/-- First diagonal of the reduced two-point Herglotz matrix. -/
def completedNativeReducedRadialHerglotzFirstDiagonal (t : ℝ) : ℂ :=
  completedNativeReducedRadialHerglotzFirst t +
    conj (completedNativeReducedRadialHerglotzFirst t)

/-- Polarized off-diagonal of the reduced two-point Herglotz matrix. -/
def completedNativeReducedRadialHerglotzOffDiagonal (t : ℝ) : ℂ :=
  (2 / 3 : ℂ) *
    (2 * completedNativeReducedRadialHerglotzSecond t +
      conj (completedNativeReducedRadialHerglotzFirst t))

/-- Second diagonal of the reduced two-point Herglotz matrix. -/
def completedNativeReducedRadialHerglotzSecondDiagonal (t : ℝ) : ℂ :=
  completedNativeReducedRadialHerglotzSecond t +
    conj (completedNativeReducedRadialHerglotzSecond t)

/-- The exact reduced two-point radial Herglotz matrix. -/
def completedNativeReducedRadialHerglotzTwoMatrix
    (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![completedNativeReducedRadialHerglotzFirstDiagonal t,
      completedNativeReducedRadialHerglotzOffDiagonal t;
    conj (completedNativeReducedRadialHerglotzOffDiagonal t),
      completedNativeReducedRadialHerglotzSecondDiagonal t]

/-- Determinant of the reduced two-point radial Herglotz matrix. -/
def completedNativeReducedRadialHerglotzTwoDeterminant (t : ℝ) : ℂ :=
  completedNativeReducedRadialHerglotzFirstDiagonal t *
      completedNativeReducedRadialHerglotzSecondDiagonal t -
    completedNativeReducedRadialHerglotzOffDiagonal t *
      conj (completedNativeReducedRadialHerglotzOffDiagonal t)

@[simp] theorem completedNativeLogDerivative_zero_eq_moment_zero :
    completedNativeLogDerivative 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have h := completedNativeLogDerivative_iteratedDeriv_eq 0
  rw [completedNativeLogDerivativeTaylorCoefficient_eq_canonical] at h
  simpa using h

theorem hasDerivAt_completedNativeLogDerivative_zero_moment_one :
    HasDerivAt completedNativeLogDerivative
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) 0 := by
  have hbase := completedNativeLogDerivative_analyticAt.differentiableAt.hasDerivAt
  have hcoefficient := completedNativeLogDerivative_iteratedDeriv_eq 1
  rw [completedNativeLogDerivativeTaylorCoefficient_eq_canonical] at hcoefficient
  have hderiv : deriv completedNativeLogDerivative 0 =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
    simpa [iteratedDeriv_one] using hcoefficient
  simpa [hderiv] using hbase

theorem hasDerivAt_completedNativeReducedRadialHerglotzFirst_zero :
    HasDerivAt completedNativeReducedRadialHerglotzFirst
      (-(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) 0 := by
  have hinner : HasDerivAt (-id : ℂ → ℂ) (-1) (0 : ℂ) :=
    (hasDerivAt_id (0 : ℂ)).neg
  have houter : HasDerivAt completedNativeLogDerivative
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)
      ((-id : ℂ → ℂ) 0) := by
    simpa using hasDerivAt_completedNativeLogDerivative_zero_moment_one
  have hcomp : HasDerivAt
      (completedNativeLogDerivative ∘ (-id : ℂ → ℂ))
      ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) * (-1)) 0 :=
    houter.comp 0 hinner
  change HasDerivAt
    (fun y : ℝ ↦ completedNativeLogDerivative (-(y : ℂ))) _ 0
  simpa using hcomp.comp_ofReal

theorem hasDerivAt_completedNativeReducedRadialHerglotzSecond_zero :
    HasDerivAt completedNativeReducedRadialHerglotzSecond
      (-4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) 0 := by
  let scale : ℂ → ℂ := fun z ↦ -(z * 4)
  have hinner : HasDerivAt scale (-4) (0 : ℂ) := by
    have hraw := ((hasDerivAt_id (0 : ℂ)).mul_const 4).neg
    convert hraw using 1 <;> try rfl
    ring
  have houter : HasDerivAt completedNativeLogDerivative
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) (scale 0) := by
    simpa [scale] using hasDerivAt_completedNativeLogDerivative_zero_moment_one
  have hcomp : HasDerivAt (completedNativeLogDerivative ∘ scale)
      ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) * (-4)) 0 :=
    houter.comp 0 hinner
  change HasDerivAt
    (fun y : ℝ ↦ completedNativeLogDerivative (-((y : ℂ) * 4))) _ 0
  convert hcomp.comp_ofReal using 1 <;> try rfl
  ring

/-- Conjugation is real differentiable along any real parameter. -/
theorem hasDerivAt_complexConj
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ conj (f t)) (conj f') x := by
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hf.hasFDerivAt
  simpa [Function.comp_def, Complex.conjCLE_apply] using hc.hasDerivAt

@[simp] theorem completedNativeReducedRadialHerglotzFirst_zero :
    completedNativeReducedRadialHerglotzFirst 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp [completedNativeReducedRadialHerglotzFirst]

@[simp] theorem completedNativeReducedRadialHerglotzSecond_zero :
    completedNativeReducedRadialHerglotzSecond 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp [completedNativeReducedRadialHerglotzSecond]

theorem hasDerivAt_completedNativeReducedRadialHerglotzFirstDiagonal_zero :
    HasDerivAt completedNativeReducedRadialHerglotzFirstDiagonal
      (-2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) 0 := by
  have hfirst := hasDerivAt_completedNativeReducedRadialHerglotzFirst_zero
  have h := hfirst.add (hasDerivAt_complexConj hfirst)
  have hcoefficient :
      (-2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) =
        -(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) +
          conj (-(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) := by
    rw [map_neg, Complex.conj_ofReal]
    ring
  rw [hcoefficient]
  convert h using 1 <;> rfl

theorem hasDerivAt_completedNativeReducedRadialHerglotzSecondDiagonal_zero :
    HasDerivAt completedNativeReducedRadialHerglotzSecondDiagonal
      (-8 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) 0 := by
  have hsecond := hasDerivAt_completedNativeReducedRadialHerglotzSecond_zero
  have h := hsecond.add (hasDerivAt_complexConj hsecond)
  have hcoefficient :
      (-8 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) =
        -4 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) +
          conj (-4 *
            (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) := by
    rw [map_mul, map_neg, map_ofNat, Complex.conj_ofReal]
    ring
  rw [hcoefficient]
  convert h using 1 <;> rfl

theorem hasDerivAt_completedNativeReducedRadialHerglotzOffDiagonal_zero :
    HasDerivAt completedNativeReducedRadialHerglotzOffDiagonal
      (-6 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) 0 := by
  have hfirst := hasDerivAt_completedNativeReducedRadialHerglotzFirst_zero
  have hsecond := hasDerivAt_completedNativeReducedRadialHerglotzSecond_zero
  have h := ((hsecond.const_mul 2).add
    (hasDerivAt_complexConj hfirst)).const_mul (2 / 3 : ℂ)
  have hcoefficient :
      (-6 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) =
        (2 / 3 : ℂ) *
          (2 * (-4 *
              (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) +
            conj (-(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
    rw [map_neg, Complex.conj_ofReal]
    ring
  rw [hcoefficient]
  convert h using 1 <;> rfl

@[simp] theorem completedNativeReducedRadialHerglotzFirstDiagonal_zero :
    completedNativeReducedRadialHerglotzFirstDiagonal 0 =
      2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp [completedNativeReducedRadialHerglotzFirstDiagonal]
  ring

@[simp] theorem completedNativeReducedRadialHerglotzSecondDiagonal_zero :
    completedNativeReducedRadialHerglotzSecondDiagonal 0 =
      2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp [completedNativeReducedRadialHerglotzSecondDiagonal]
  ring

@[simp] theorem completedNativeReducedRadialHerglotzOffDiagonal_zero :
    completedNativeReducedRadialHerglotzOffDiagonal 0 =
      2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp [completedNativeReducedRadialHerglotzOffDiagonal]
  ring

@[simp] theorem completedNativeReducedRadialHerglotzTwoDeterminant_zero :
    completedNativeReducedRadialHerglotzTwoDeterminant 0 = 0 := by
  simp [completedNativeReducedRadialHerglotzTwoDeterminant]
  rw [map_ofNat]
  ring

/-- The first nonzero determinant coefficient is exactly `4 h₀ h₁`. -/
theorem hasDerivAt_completedNativeReducedRadialHerglotzTwoDeterminant_zero :
    HasDerivAt completedNativeReducedRadialHerglotzTwoDeterminant
      (4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
        canonicalCompletedNativeLogDerivativeMoment 1) 0 := by
  have hfirst :=
    hasDerivAt_completedNativeReducedRadialHerglotzFirstDiagonal_zero
  have hsecond :=
    hasDerivAt_completedNativeReducedRadialHerglotzSecondDiagonal_zero
  have hoff :=
    hasDerivAt_completedNativeReducedRadialHerglotzOffDiagonal_zero
  have h := (hfirst.mul hsecond).sub
    (hoff.mul (hasDerivAt_complexConj hoff))
  have hcoefficient :
      4 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) *
          canonicalCompletedNativeLogDerivativeMoment 1 =
        (-2 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) *
            completedNativeReducedRadialHerglotzSecondDiagonal 0 +
          completedNativeReducedRadialHerglotzFirstDiagonal 0 *
              (-8 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) -
        ((-6 * (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) *
              conj (completedNativeReducedRadialHerglotzOffDiagonal 0) +
          completedNativeReducedRadialHerglotzOffDiagonal 0 *
              conj (-6 *
                (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ))) := by
    rw [completedNativeReducedRadialHerglotzFirstDiagonal_zero,
      completedNativeReducedRadialHerglotzSecondDiagonal_zero,
      completedNativeReducedRadialHerglotzOffDiagonal_zero]
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal]
    ring
  rw [hcoefficient]
  convert h using 1 <;> rfl

/-! ## Positivity of the reduced section -/

/-- The reduced determinant is real because it is the determinant of a
Hermitian two-by-two matrix. -/
theorem completedNativeReducedRadialHerglotzTwoDeterminant_eq_ofReal_re
    (t : ℝ) :
    completedNativeReducedRadialHerglotzTwoDeterminant t =
      ((completedNativeReducedRadialHerglotzTwoDeterminant t).re : ℂ) := by
  symm
  rw [← Complex.conj_eq_iff_re]
  unfold completedNativeReducedRadialHerglotzTwoDeterminant
    completedNativeReducedRadialHerglotzFirstDiagonal
    completedNativeReducedRadialHerglotzSecondDiagonal
  simp only [map_sub, map_mul, map_add, starRingEnd_self_apply]
  ring

/-- Real determinant used for the one-sided radial sign argument. -/
def completedNativeReducedRadialHerglotzTwoRealDeterminant (t : ℝ) : ℝ :=
  (completedNativeReducedRadialHerglotzTwoDeterminant t).re

@[simp] theorem completedNativeReducedRadialHerglotzTwoRealDeterminant_zero :
    completedNativeReducedRadialHerglotzTwoRealDeterminant 0 = 0 := by
  simp [completedNativeReducedRadialHerglotzTwoRealDeterminant]

theorem
    hasDerivAt_completedNativeReducedRadialHerglotzTwoRealDeterminant_zero :
    HasDerivAt completedNativeReducedRadialHerglotzTwoRealDeterminant
      (4 * canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 1) 0 := by
  have hcomplex :=
    hasDerivAt_completedNativeReducedRadialHerglotzTwoDeterminant_zero
  have hre := Complex.reCLM.hasFDerivAt.comp 0 hcomplex.hasFDerivAt
  change HasDerivAt
    (fun t : ℝ ↦ (completedNativeReducedRadialHerglotzTwoDeterminant t).re)
    _ 0
  convert hre.hasDerivAt using 1 <;> try rfl
  norm_num [Complex.mul_re]

/-- Squared real step corresponding to the radial substitution `t = h²`. -/
def canonicalCompletedNativeRadialHerglotzSquaredStep (k : ℕ) : ℝ :=
  canonicalGreenJetRealStep k ^ 2

theorem canonicalGreenJetRealStep_tendsto_zero :
    Tendsto canonicalGreenJetRealStep atTop (nhds 0) := by
  change Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem canonicalCompletedNativeRadialHerglotzSquaredStep_tendsto_zero :
    Tendsto canonicalCompletedNativeRadialHerglotzSquaredStep atTop
      (nhds 0) := by
  change Tendsto (fun k : ℕ ↦ canonicalGreenJetRealStep k ^ 2)
    atTop (nhds 0)
  simpa using canonicalGreenJetRealStep_tendsto_zero.pow 2

theorem canonicalCompletedNativeRadialHerglotzSquaredStep_pos (k : ℕ) :
    0 < canonicalCompletedNativeRadialHerglotzSquaredStep k := by
  unfold canonicalCompletedNativeRadialHerglotzSquaredStep
    canonicalGreenJetRealStep
  positivity

/-- The normalized reduced determinant converges to its first polarized
coefficient `4 h₀ h₁`. -/
theorem
    completedNativeReducedRadialHerglotzTwoRealDeterminant_div_squaredStep_tendsto :
    Tendsto
      (fun k : ℕ ↦
        completedNativeReducedRadialHerglotzTwoRealDeterminant
            (canonicalCompletedNativeRadialHerglotzSquaredStep k) /
          canonicalCompletedNativeRadialHerglotzSquaredStep k)
      atTop
      (nhds (4 * canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 1)) := by
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp
    hasDerivAt_completedNativeReducedRadialHerglotzTwoRealDeterminant_zero
  have hnonzero : ∀ᶠ k : ℕ in atTop,
      canonicalCompletedNativeRadialHerglotzSquaredStep k ∈
        ({0} : Set ℝ)ᶜ := by
    filter_upwards [] with k
    exact (canonicalCompletedNativeRadialHerglotzSquaredStep_pos k).ne'
  have hwithin : Tendsto canonicalCompletedNativeRadialHerglotzSquaredStep
      atTop (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨canonicalCompletedNativeRadialHerglotzSquaredStep_tendsto_zero,
        hnonzero⟩
  have hcomp := hslope.comp hwithin
  apply hcomp.congr'
  filter_upwards [] with k
  simp only [Function.comp_apply, zero_add,
    completedNativeReducedRadialHerglotzTwoRealDeterminant_zero, sub_zero,
    smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- Positive first two canonical moments make the reduced two-point
Herglotz matrix positive semidefinite on every sufficiently small canonical
radial step. -/
theorem
    completedNativeReducedRadialHerglotzTwoMatrix_eventually_posSemidef_of_moments
    (hmomentZero : 0 < canonicalCompletedNativeLogDerivativeMoment 0)
    (hmomentOne : 0 < canonicalCompletedNativeLogDerivativeMoment 1) :
    ∀ᶠ k : ℕ in atTop,
      (completedNativeReducedRadialHerglotzTwoMatrix
        (canonicalCompletedNativeRadialHerglotzSquaredStep k)).PosSemidef := by
  have hdetQuotient : ∀ᶠ k : ℕ in atTop,
      0 < completedNativeReducedRadialHerglotzTwoRealDeterminant
            (canonicalCompletedNativeRadialHerglotzSquaredStep k) /
          canonicalCompletedNativeRadialHerglotzSquaredStep k :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds
      completedNativeReducedRadialHerglotzTwoRealDeterminant_div_squaredStep_tendsto
      (by positivity)
  have hfirstTendsto : Tendsto
      (fun k : ℕ ↦
        (completedNativeReducedRadialHerglotzFirstDiagonal
          (canonicalCompletedNativeRadialHerglotzSquaredStep k)).re)
      atTop (nhds (2 * canonicalCompletedNativeLogDerivativeMoment 0)) := by
    have hcontinuous :=
      hasDerivAt_completedNativeReducedRadialHerglotzFirstDiagonal_zero.continuousAt
    have hre := (Complex.continuous_re.tendsto
      (completedNativeReducedRadialHerglotzFirstDiagonal 0)).comp
        hcontinuous
    have hcomposed := hre.comp
      canonicalCompletedNativeRadialHerglotzSquaredStep_tendsto_zero
    simpa [Function.comp_def] using hcomposed
  have hfirstPositive : ∀ᶠ k : ℕ in atTop,
      0 < (completedNativeReducedRadialHerglotzFirstDiagonal
        (canonicalCompletedNativeRadialHerglotzSquaredStep k)).re :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hfirstTendsto
      (by positivity)
  filter_upwards [hdetQuotient, hfirstPositive] with k hkDet hkFirst
  have hstep := canonicalCompletedNativeRadialHerglotzSquaredStep_pos k
  have hdetReal :
      0 < completedNativeReducedRadialHerglotzTwoRealDeterminant
        (canonicalCompletedNativeRadialHerglotzSquaredStep k) := by
    rcases div_pos_iff.mp hkDet with hpositive | hnegative
    · exact hpositive.1
    · exact False.elim ((not_lt_of_ge hstep.le) hnegative.2)
  apply complexFinTwo_posSemidef_of_det
  · rw [Complex.pos_iff]
    exact ⟨hkFirst, by
      simp [completedNativeReducedRadialHerglotzFirstDiagonal]⟩
  · change 0 ≤ completedNativeReducedRadialHerglotzTwoDeterminant
      (canonicalCompletedNativeRadialHerglotzSquaredStep k)
    rw [completedNativeReducedRadialHerglotzTwoDeterminant_eq_ofReal_re]
    exact Complex.zero_le_real.mpr hdetReal.le

/-! ## Identification with the literal radial Herglotz sample -/

/-- On the canonical two-point radial section, the literal Herglotz kernel
is eventually exactly the reduced matrix above. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_eq_reduced :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedNativeRadialHerglotzSampleMatrix k 2 =
        completedNativeReducedRadialHerglotzTwoMatrix
          (canonicalCompletedNativeRadialHerglotzSquaredStep k) := by
  have hfirst : ∀ᶠ k : ℕ in atTop,
      completedNativeOperatorLogDerivative
          (canonicalCompletedC3RadialTiltPoint k 0) =
        2 * canonicalCompletedC3RadialTiltPoint k 0 *
          completedNativeLogDerivative
            (canonicalCompletedC3RadialTiltPoint k 0 ^ 2) := by
    exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0).eventually
      completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate
  have hsecond : ∀ᶠ k : ℕ in atTop,
      completedNativeOperatorLogDerivative
          (canonicalCompletedC3RadialTiltPoint k 1) =
        2 * canonicalCompletedC3RadialTiltPoint k 1 *
          completedNativeLogDerivative
            (canonicalCompletedC3RadialTiltPoint k 1 ^ 2) := by
    exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero 1).eventually
      completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate
  filter_upwards [hfirst, hsecond] with k hkFirst hkSecond
  have hstep : canonicalGreenJetStep k ≠ 0 := by
    unfold canonicalGreenJetStep
    apply inv_ne_zero
    exact_mod_cast (by positivity : (k : ℝ) + 1 ≠ 0)
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [canonicalCompletedNativeRadialHerglotzSampleMatrix,
      Matrix.of_apply, completedNativeLogDerivativeHerglotzKernel,
      completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative]
    rw [hkFirst]
    simp [completedNativeReducedRadialHerglotzTwoMatrix,
      canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep,
      canonicalCompletedNativeRadialHerglotzSquaredStep,
      completedNativeReducedRadialHerglotzFirstDiagonal,
      completedNativeReducedRadialHerglotzFirst,
      ← canonicalGreenJetRealStep_coe, pow_two, map_ofNat]
    field_simp [hstep]
    ring_nf
    rw [Complex.I_sq]
    simp only [neg_mul, one_mul]
  · simp only [canonicalCompletedNativeRadialHerglotzSampleMatrix,
      Matrix.of_apply, completedNativeLogDerivativeHerglotzKernel,
      completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative]
    rw [hkSecond, hkFirst]
    simp [completedNativeReducedRadialHerglotzTwoMatrix,
      canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep,
      canonicalCompletedNativeRadialHerglotzSquaredStep,
      completedNativeReducedRadialHerglotzOffDiagonal,
      completedNativeReducedRadialHerglotzFirst,
      completedNativeReducedRadialHerglotzSecond,
      ← canonicalGreenJetRealStep_coe, pow_two, map_ofNat]
    field_simp [hstep]
    ring_nf
    rw [Complex.I_sq]
    simp only [neg_mul, one_mul]
  · simp only [canonicalCompletedNativeRadialHerglotzSampleMatrix,
      Matrix.of_apply, completedNativeLogDerivativeHerglotzKernel,
      completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative]
    rw [hkFirst, hkSecond]
    simp [completedNativeReducedRadialHerglotzTwoMatrix,
      canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep,
      canonicalCompletedNativeRadialHerglotzSquaredStep,
      completedNativeReducedRadialHerglotzOffDiagonal,
      completedNativeReducedRadialHerglotzFirst,
      completedNativeReducedRadialHerglotzSecond,
      ← canonicalGreenJetRealStep_coe, pow_two, map_ofNat]
    field_simp [hstep]
    ring_nf
    rw [Complex.I_sq]
    simp only [neg_mul, one_mul]
    ring
  · simp only [canonicalCompletedNativeRadialHerglotzSampleMatrix,
      Matrix.of_apply, completedNativeLogDerivativeHerglotzKernel,
      completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative]
    rw [hkSecond]
    simp [completedNativeReducedRadialHerglotzTwoMatrix,
      canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep,
      canonicalCompletedNativeRadialHerglotzSquaredStep,
      completedNativeReducedRadialHerglotzSecondDiagonal,
      completedNativeReducedRadialHerglotzSecond,
      ← canonicalGreenJetRealStep_coe, pow_two, map_ofNat]
    field_simp [hstep]
    ring_nf
    rw [Complex.I_sq]
    simp only [neg_mul, one_mul]

/-- Positive `h₀` and `h₁` close the literal two-point radial Herglotz
section. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_moments
    (hmomentZero : 0 < canonicalCompletedNativeLogDerivativeMoment 0)
    (hmomentOne : 0 < canonicalCompletedNativeLogDerivativeMoment 1) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  filter_upwards [
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_eq_reduced,
    completedNativeReducedRadialHerglotzTwoMatrix_eventually_posSemidef_of_moments
      hmomentZero hmomentOne] with k hk hpos
  rw [hk]
  exact hpos

/-! ## The first concrete TFVD polarized gate -/

/-- The first genuinely polarized obligation: the positive odd TFVD
diagonal at raw Taylor order one must equal the analytic moment `h₁`. -/
def CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification : Prop :=
  (inner ℂ
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)).re =
      canonicalCompletedNativeLogDerivativeMoment 1

/-- The first odd enriched TFVD Gram diagonal is strictly positive before
any moment identification is imposed. -/
theorem canonicalCompletedNativeTfvdFirstOddDiagonal_pos :
    0 < (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)).re := by
  have hdiag :=
    (canonicalCompletedNativeTfvdEnrichedTaylorOddGram_posDef 1).diag_pos
      (i := (0 : Fin 1))
  simpa [canonicalCompletedNativeTfvdEnrichedTaylorOddGram] using hdiag

/-- Consequently the single first-odd diagonal identification already
forces strict positivity of `h₁`. -/
theorem canonicalCompletedNativeLogDerivativeMoment_one_pos_of_tfvdFirstOddDiagonal
    (hidentified :
      CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification) :
    0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [← hidentified]
  exact canonicalCompletedNativeTfvdFirstOddDiagonal_pos

/-- Four-corner spelling of the same gate: the real first-odd finite
prefixes then converge to `h₁`. -/
theorem nativeGpreFourCornerEnrichedTaylorPrefix_one_one_re_tendsto_moment_one
    (hidentified :
      CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification) :
    Tendsto
      (fun M : ℕ ↦
        (nativeGpreFourCornerEnrichedTaylorPrefix M 1 1).re)
      atTop (nhds (canonicalCompletedNativeLogDerivativeMoment 1)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (nativeGpreFourCornerEnrichedTaylorPrefix_tendsto_completed 1 1)
  change Tendsto
    (fun M : ℕ ↦ (nativeGpreFourCornerEnrichedTaylorPrefix M 1 1).re)
    atTop
    (nhds ((inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 1)).re)) at h
  rw [hidentified] at h
  exact h

/-- Central coisometric flatness supplies `h₀ > 0`; the first odd TFVD
diagonal identification supplies `h₁ > 0`.  Together they prove the literal
two-point Herglotz section. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_centralFlat_and_tfvdFirstOddDiagonal
    (hflat : deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0)
    (hidentified :
      CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  apply
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_moments
  · exact canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_transverseCurvature
      (deriv_canonicalCompletedC3CentralCoisometricEnergyDefect_zero_eq_zero_iff.mp
        hflat)
  · exact
      canonicalCompletedNativeLogDerivativeMoment_one_pos_of_tfvdFirstOddDiagonal
        hidentified

/-- The same two scalar geometric gates therefore close the two-point
chiral Pick section through the exact Cayley--Herglotz congruence. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_centralFlat_and_tfvdFirstOddDiagonal
    (hflat : deriv canonicalCompletedC3CentralCoisometricEnergyDefect 0 = 0)
    (hidentified :
      CanonicalCompletedNativeTfvdFirstOddDiagonalMomentIdentification) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef := by
  have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin 2,
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [
      (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
        completedNativeChiralPickFactorization_eventually_regular] with k hk
    exact ⟨hk.2.1, hk.2.2⟩
  filter_upwards [
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_centralFlat_and_tfvdFirstOddDiagonal
      hflat hidentified,
    hregular] with k hHerglotz hreg
  exact
    (canonicalCompletedNativeRadialChiralPickSampleMatrix_posSemidef_iff_herglotz
      k 2 hreg).mpr hHerglotz

end

end CarrySelfAdjointOperator
