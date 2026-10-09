import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenMarginLoss
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Source-derived first-correction pencil

Coordinates are ordered (x0,x2,x4,x6,x1,x3,x5). Both matrices are expansions
of the existing source forms; neither defines a new metric or source state.
The determinant tests the correction relative to the certified boundary energy.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384

/-- The existing boundary energy in parity order, with every cross retained. -/
def nativeSourceSevenBoundaryMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  let c := nativeSourceOddBoundaryCoefficient
  !![2*c 0, -2*c 1, 2*c 2, -2*c 3, 0, 0, 0;
     -2*c 1, 2*c 2, -2*c 3, 2*c 4, 0, 0, 0;
     2*c 2, -2*c 3, 2*c 4, -2*c 5, 0, 0, 0;
     -2*c 3, 2*c 4, -2*c 5, 2*c 6, 0, 0, 0;
     0, 0, 0, 0, 2*c 1, -2*c 2, 2*c 3;
     0, 0, 0, 0, -2*c 2, 2*c 3, -2*c 4;
     0, 0, 0, 0, 2*c 3, -2*c 4, 2*c 5]

/-- The actual derivative of full storage, in the same parity order. -/
def radialSevenFirstCorrectionMatrix : Matrix (Fin 7) (Fin 7) ℝ :=
  let c := nativeSourceOddBoundaryCoefficient
  !![0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, -56*c 4, 56*c 5, -56*c 6;
     0, 0, 0, -56*c 4, 0, 0, 0;
     0, 0, 0, 56*c 5, 0, 0, 0;
     0, 0, 0, -56*c 6, 0, 0, 0]

def radialSevenParityCoordinates (x : Fin 7 → ℂ) : Fin 7 → ℂ :=
  ![x 0,x 2,x 4,x 6,x 1,x 3,x 5]

/-- Audit of the matrix expansion against the original complex source form. -/
theorem nativeSourceSevenBoundaryMatrix_quadratic (x : Fin 7 → ℂ) :
    (∑ i : Fin 7, ∑ j : Fin 7, (nativeSourceSevenBoundaryMatrix i j : ℂ) *
      conj (radialSevenParityCoordinates x i) * radialSevenParityCoordinates x j).re =
      nativeSourceSevenBoundaryEnergy x := by
  simp [nativeSourceSevenBoundaryMatrix, radialSevenParityCoordinates,
    Fin.sum_univ_succ, nativeSourceSevenBoundaryEnergy,
    nativeSourceSevenEvenBoundaryEnergy, nativeSourceFiveEvenBoundaryEnergy,
    nativeSourceSixOddBoundaryEnergy, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im]
  ring

theorem radialSevenFirstCorrectionMatrix_quadratic (x : Fin 7 → ℂ) :
    (∑ i : Fin 7, ∑ j : Fin 7, (radialSevenFirstCorrectionMatrix i j : ℂ) *
      conj (radialSevenParityCoordinates x i) * radialSevenParityCoordinates x j).re =
      radialSevenBoundaryFirstCorrection x := by
  simp [radialSevenFirstCorrectionMatrix, radialSevenParityCoordinates,
    Fin.sum_univ_succ, radialSevenBoundaryFirstCorrection, Complex.mul_re,
    Complex.mul_im]
  ring

/-- The odd dual cofactor along the actual coupling (-c4,c5,-c6).
This polynomial is obtained by expansion, without target moments. -/
def radialSevenOddCouplingCofactor : ℝ :=
  let c := nativeSourceOddBoundaryCoefficient
  c 1*c 3*(c 6)^2 - 2*c 1*c 4*c 5*c 6 + c 1*(c 5)^3 -
  (c 2)^2*(c 6)^2 + 2*c 2*c 3*c 5*c 6 + 2*c 2*(c 4)^2*c 6 -
  2*c 2*c 4*(c 5)^2 - 2*(c 3)^2*c 4*c 6 - (c 3)^2*(c 5)^2 +
  3*c 3*(c 4)^2*c 5 - (c 4)^4

/-- Exact generalized characteristic polynomial of the first correction. -/
theorem radialSevenFirstCorrection_pencil_det (t : ℝ) :
    (radialSevenFirstCorrectionMatrix - t • nativeSourceSevenBoundaryMatrix).det =
      128 * t^5 * (784*nativeSourceFiveEvenDiscriminant*radialSevenOddCouplingCofactor -
        nativeSourceSevenEvenDiscriminant*nativeSourceSixOddDiscriminant*t^2) := by
  simp [radialSevenFirstCorrectionMatrix, nativeSourceSevenBoundaryMatrix,
    Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove, nativeSourceFiveEvenDiscriminant,
    nativeSourceSevenEvenDiscriminant, nativeSourceSevenEvenCoupling0,
    nativeSourceSevenEvenCoupling1, nativeSourceSevenEvenCoupling2,
    nativeSourceSixOddDiscriminant, radialSevenOddCouplingCofactor]
  ring
end
end CarrySelfAdjointOperator
