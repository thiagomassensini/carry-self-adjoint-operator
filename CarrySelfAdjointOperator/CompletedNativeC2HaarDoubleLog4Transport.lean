import CarrySelfAdjointOperator.CameraReturnVarianceEnergyBalance
import CPFormal.Analytic.CpNativeCarryFiniteCameraAlgebra
import Mathlib.Tactic

/-!
# C2/Haar transport at the double `log 4` sector

This module records the coordinate content of the C2 bilateral--Haar
comparison.  The exceptional C2 camera and C4 have the same physical slope,
`4`; their two-dimensional sector may therefore be sheared without mixing
physical clocks.  In the six-camera order `(2,3,4,5,6,7)`, the Haar coordinate
is `h₂ = (3/2)c₂ - (1/2)c₄`.

The historical finite-cutoff comparison has one endpoint term unless its
physical horizon is transported.  The current native API contains the
bilateral six-camera family, but no separately typed finite Haar family with
its matched horizon.  Thus this file proves the exact finite linear algebra
and names the missing all-moment/POVM statement as a seam.  It does not invent
a Haar POVM, infer the seam from height moments, or assert Pick positivity.

The upstream C2 chart is also explicitly distinct from a geometric four-leg
C4: it is a radius-one chart whose native width/period parameter is four.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Finite NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false

/-- C4 lies in the same physical slope-four sector as the exceptional C2
camera. -/
@[simp] theorem cameraSlope_four_eq_four : cameraSlope 4 = 4 := by
  norm_num [cameraSlope]

/-- Upstream C2 has the width label four but remains a radius-one chart; this
is not an identification with a geometric four-leg C4. -/
theorem nativeCarryC2_is_width_four_not_geometricC4
    (M : ℕ) (f : ℤ → ℝ) :
    CPFormal.Analytic.Cp.nativeCarryAlignedC2Chart M f =
      CPFormal.Analytic.Cp.nativeCarryFiniteSaturatedChart 4 M f ∧
    CPFormal.Genuine.Cp.halfRange 4 = 1 := by
  exact ⟨CPFormal.Analytic.Cp.nativeCarryAlignedC2Chart_eq_width_four M f,
    CPFormal.Analytic.Cp.nativeCarryWidthFour_halfRange_eq_one⟩

/-- The Haar/parity coordinate in the C2--C4 slope-four sector. -/
def c2HaarCoordinate (c : Fin 6 → ℝ) : ℝ :=
  (3 / 2 : ℝ) * c 0 - (1 / 2 : ℝ) * c 2

/-- An untuned complementary coordinate.  Retaining C4 makes the C2--C4
coordinate change invertible. -/
def c2HaarComplement (c : Fin 6 → ℝ) : ℝ := c 2

/-- Full coordinate change, preserving the other four camera directions. -/
def c2HaarCoordinateChange (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c2HaarCoordinate c, c 1, c2HaarComplement c, c 3, c 4, c 5]

/-- Explicit inverse of `c2HaarCoordinateChange`. -/
def c2HaarCoordinateChangeInv (d : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(2 / 3 : ℝ) * d 0 + (1 / 3 : ℝ) * d 2, d 1, d 2, d 3, d 4, d 5]

/-- The shear is invertible in the full six-camera coordinate space. -/
theorem c2HaarCoordinateChangeInv_apply_change (c : Fin 6 → ℝ) :
    c2HaarCoordinateChangeInv (c2HaarCoordinateChange c) = c := by
  funext i
  fin_cases i <;>
    simp [c2HaarCoordinateChangeInv, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement]; ring

/-- The inverse shear has no hidden kernel. -/
theorem c2HaarCoordinateChange_apply_inv (d : Fin 6 → ℝ) :
    c2HaarCoordinateChange (c2HaarCoordinateChangeInv d) = d := by
  funext i
  fin_cases i <;>
    simp [c2HaarCoordinateChangeInv, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement]; ring

/-- The 3--4--6 coordinates after replacing C2 by Haar.  Their order is
`(h₂,c₃,c₆)`. -/
def c2HaarThreeFourSixCoordinates (c : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![c2HaarCoordinate c, c 1, c 4]

/-- Mixed-return functional represented by the existing raw six-camera ray. -/
def sixCameraMixedReturnFunctional (c : Fin 6 → ℝ) : ℝ :=
  sixCameraMixedReturnRay ⬝ᵥ c

/-- The C2/C4 contribution of the mixed-return ray is exactly `-4 h₂`.
This is an identity of sourced camera directions, not a fit to target moments. -/
theorem sixCameraMixedReturn_c2c4_eq_haar (c : Fin 6 → ℝ) :
    -6 * c 0 + 2 * c 2 = -4 * c2HaarCoordinate c := by
  simp [c2HaarCoordinate]
  ring

/-- In the `(h₂,c₃,c₆)` quotient of the supported mixed-return direction,
the raw ray `(-6,-3,2,0,3,0)` becomes `(-4,-3,3)`. -/
theorem sixCameraMixedReturnFunctional_eq_haar_threeFourSix (c : Fin 6 → ℝ) :
    sixCameraMixedReturnFunctional c =
      -4 * c2HaarThreeFourSixCoordinates c 0 -
        3 * c2HaarThreeFourSixCoordinates c 1 +
        3 * c2HaarThreeFourSixCoordinates c 2 := by
  simp [sixCameraMixedReturnFunctional, sixCameraMixedReturnRay,
    c2HaarThreeFourSixCoordinates, dotProduct, Fin.sum_univ_succ,
    c2HaarCoordinate]
  ring

/-- Matrix of the full C2/Haar coordinate shear. -/
def c2HaarCoordinateMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![3 / 2, 0, -1 / 2, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Matrix of the explicit inverse shear. -/
def c2HaarCoordinateMatrixInv : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2 / 3, 0, 1 / 3, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Function and matrix presentations of the shear agree. -/
theorem c2HaarCoordinateMatrix_mulVec (c : Fin 6 → ℝ) :
    c2HaarCoordinateMatrix *ᵥ c = c2HaarCoordinateChange c := by
  ext i
  fin_cases i
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    change c 3 = c 3
    rfl
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    change c 4 = c 4
    rfl
  · norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateChange,
      c2HaarCoordinate, c2HaarComplement, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    change c 5 = c 5
    rfl

/-- Function and matrix presentations of the inverse shear agree. -/
theorem c2HaarCoordinateMatrixInv_mulVec (c : Fin 6 → ℝ) :
    c2HaarCoordinateMatrixInv *ᵥ c = c2HaarCoordinateChangeInv c := by
  ext i
  fin_cases i
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    change c 3 = c 3
    rfl
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    change c 4 = c 4
    rfl
  · norm_num [c2HaarCoordinateMatrixInv, c2HaarCoordinateChangeInv,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    change c 5 = c 5
    rfl

/-- Exact right inverse at matrix level. -/
theorem c2HaarCoordinateMatrix_mul_inv :
    c2HaarCoordinateMatrix * c2HaarCoordinateMatrixInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateMatrixInv,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Exact left inverse at matrix level. -/
theorem c2HaarCoordinateMatrixInv_mul :
    c2HaarCoordinateMatrixInv * c2HaarCoordinateMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [c2HaarCoordinateMatrix, c2HaarCoordinateMatrixInv,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The physical logarithmic slope matrix commutes with the C2/Haar shear.
This is why the shear remains inside the double `log 4` sector. -/
theorem c2HaarCoordinateMatrix_commutes_logSlope :
    c2HaarCoordinateMatrix * cameraLogSlopeDiagonal sixCamera =
      cameraLogSlopeDiagonal sixCamera * c2HaarCoordinateMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c2HaarCoordinateMatrix, cameraLogSlopeDiagonal, sixCamera,
      cameraSlope]
  all_goals ring

/-- Congruence transport of a raw matrix-valued moment. -/
def c2HaarCongruence (M : Matrix (Fin 6) (Fin 6) ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  c2HaarCoordinateMatrix * M * c2HaarCoordinateMatrixᵀ

/-- The quadratic form of a congruently transported moment is exactly the old
quadratic form on the transposed transported coefficients. -/
theorem c2HaarCongruence_quadraticForm
    (M : Matrix (Fin 6) (Fin 6) ℝ) (u : Fin 6 → ℝ) :
    u ⬝ᵥ (c2HaarCongruence M *ᵥ u) =
      (c2HaarCoordinateMatrixᵀ *ᵥ u) ⬝ᵥ
        (M *ᵥ (c2HaarCoordinateMatrixᵀ *ᵥ u)) := by
  change u ⬝ᵥ ((c2HaarCoordinateMatrix * M * c2HaarCoordinateMatrixᵀ) *ᵥ u) =
    (c2HaarCoordinateMatrixᵀ *ᵥ u) ⬝ᵥ
      (M *ᵥ (c2HaarCoordinateMatrixᵀ *ᵥ u))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [← Matrix.transpose_transpose c2HaarCoordinateMatrix]
  rw [Matrix.dotProduct_transpose_mulVec
    (A := c2HaarCoordinateMatrixᵀ)]
  exact dotProduct_comm _ _

/-- Precise missing bridge from the finite matched-horizon C2/Haar comparison
to a native all-order operator-valued measure.  An inhabitant must supply a
separate Haar family and prove its congruence at every moment order. -/
def C2HaarMatchedPhysicalHorizonMomentTransport
    (bilateral haar : ℕ → Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  ∀ n : ℕ, haar n = c2HaarCongruence (bilateral n)

/-- A matched-horizon transport, once supplied by geometry, gives the
advertised congruence uniformly in moment order. -/
theorem C2HaarMatchedPhysicalHorizonMomentTransport.all_orders
    {bilateral haar : ℕ → Matrix (Fin 6) (Fin 6) ℝ}
    (htransport : C2HaarMatchedPhysicalHorizonMomentTransport bilateral haar)
    (n : ℕ) : haar n = c2HaarCongruence (bilateral n) :=
  htransport n

end
end CarrySelfAdjointOperator
