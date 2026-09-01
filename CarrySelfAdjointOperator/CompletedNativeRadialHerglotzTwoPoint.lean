import CarrySelfAdjointOperator.CompletedNativeCentralCoisometricDefectFlatness
import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
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

end

end CarrySelfAdjointOperator
