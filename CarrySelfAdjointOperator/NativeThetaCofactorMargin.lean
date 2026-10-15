import CarrySelfAdjointOperator.NativeThetaPrincipalDensityObstruction
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The actual critical source, expressed by cofactors before scalar readout.
The adjugate vector and bordered scalar contain no matrix inverse. Multiplying
by det(H)^2 changes neither the source sign nor the quantitative margin when
H is invertible. No all-order sign is established in this module. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open Matrix Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

def nativeSourcePrefixDet (s n : ℕ) : ℝ := (sourceMomentMatrix m s n).det

def nativeSourceCofactorVector (s n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix m s n).adjugate *ᵥ sourceMomentCoupling m s n))
    (nativeSourcePrefixDet s n)

/-- Source polynomial, retaining every ordered cross of the cofactor vector. -/
def nativeSourceCofactorThetaPolynomial (s n : ℕ) : ℝ[X] :=
  c₀ • nativeThetaQuadraticPolynomial s (n+1) (nativeSourceCofactorVector s n)

def nativeSourceBorderedScalar (s n : ℕ) : ℝ :=
  nativeSourcePrefixDet s n*m (2*n+s) - sourceMomentCoupling m s n ⬝ᵥ
    ((sourceMomentMatrix m s n).adjugate *ᵥ sourceMomentCoupling m s n)

theorem nativeSourcePrefixDet_ne_zero (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) : nativeSourcePrefixDet s n ≠ 0 := by
  exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA))

theorem nativeSourceCofactorVector_eq_scaled (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    nativeSourceCofactorVector s n = nativeSourcePrefixDet s n • nativeSchurCriticalCoefficients s n := by
  let H := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  have hvec : H.det • (H⁻¹ *ᵥ b) = H.adjugate *ᵥ b := by
    rw [Matrix.det_smul_inv_mulVec_eq_cramer H b ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      Matrix.cramer_eq_adjugate_mulVec]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nativeSourceCofactorVector,nativeSchurCriticalCoefficients]
  · have hj := congrFun hvec j
    simpa only [nativeSourceCofactorVector,nativeSchurCriticalCoefficients,
      Fin.snoc_castSucc,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,mul_neg,
      nativeSourcePrefixDet,H,b] using congrArg Neg.neg hj.symm

theorem nativeThetaQuadraticPolynomial_smul (s N : ℕ) (a : ℝ) (v : Fin N → ℝ) :
    nativeThetaQuadraticPolynomial s N (a • v) = a^2 • nativeThetaQuadraticPolynomial s N v := by
  simp only [nativeThetaQuadraticPolynomial,Finset.smul_sum,Pi.smul_apply,
    smul_eq_mul,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem nativeSourceCofactorThetaPolynomial_eq_scaled (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    nativeSourceCofactorThetaPolynomial s n =
      (nativeSourcePrefixDet s n)^2 • nativeSchurThetaPolynomial s n := by
  unfold nativeSourceCofactorThetaPolynomial nativeSchurThetaPolynomial
  rw [nativeSourceCofactorVector_eq_scaled s n hA,nativeThetaQuadraticPolynomial_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- Exact integrated source remainder, no positive measure or changed metric
is introduced by the cofactor expression. -/
theorem nativeSourceCofactorThetaPolynomial_integral (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n) =
      (nativeSourcePrefixDet s n)^2*nativeSourceSchurRemainder s n := by
  rw [nativeSourceCofactorThetaPolynomial_eq_scaled s n hA,map_smul,
    nativeSchurThetaPolynomial_integral]
  rfl

theorem nativeSourceBorderedScalar_eq (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    nativeSourceBorderedScalar s n =
      nativeSourcePrefixDet s n*sourceMomentSchur m s n := by
  let H := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  have hvec : H.det • (H⁻¹ *ᵥ b) = H.adjugate *ᵥ b := by
    rw [Matrix.det_smul_inv_mulVec_eq_cramer H b ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      Matrix.cramer_eq_adjugate_mulVec]
  unfold nativeSourceBorderedScalar sourceMomentSchur
  rw [← hvec, dotProduct_smul]
  simp only [smul_eq_mul]
  dsimp [H,b,nativeSourcePrefixDet]
  ring

/-- The bordered polynomial identity is valid even at singular prefixes. -/
theorem nativeSourceCofactorThetaPolynomial_integral_bordered (s n : ℕ) :
    nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n) =
      c₀*nativeSourcePrefixDet s n*nativeSourceBorderedScalar s n := by
  let H := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let u := H.adjugate *ᵥ b
  let D := H.det
  have hu : H *ᵥ u = D • b := by
    dsimp [u,D]
    rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hq : sourceMomentQuadratic m s n (-u) = D*(b ⬝ᵥ u) := by
    change (-u) ⬝ᵥ (H *ᵥ (-u)) = _
    simp only [Matrix.mulVec_neg,hu,neg_dotProduct,dotProduct_neg,
      dotProduct_smul,smul_eq_mul]
    rw [dotProduct_comm u b]
    ring
  rw [nativeSourceCofactorThetaPolynomial,map_smul,nativeThetaQuadraticPolynomial_integral]
  simp only [smul_eq_mul,nativeSourceCofactorVector]
  rw [sourceMomentQuadratic_snoc]
  change c₀*(sourceMomentQuadratic m s n (-u)+2*D*(b ⬝ᵥ (-u))+m (2*n+s)*D^2) = _
  rw [hq,dotProduct_neg]
  dsimp [nativeSourceBorderedScalar,nativeSourcePrefixDet,D,u,H,b]
  ring

theorem nativeThetaCoefficientMass_smul (a : ℝ) (P : ℝ[X]) :
    nativeThetaCoefficientMass (a • P) = |a| *nativeThetaCoefficientMass P := by
  by_cases ha : a = 0
  · simp [ha,nativeThetaCoefficientMass]
  have hs : (a • P).support = P.support := by
    ext k
    simp [Polynomial.mem_support_iff,ha]
  unfold nativeThetaCoefficientMass
  rw [hs]
  simp only [Polynomial.coeff_smul,smul_eq_mul,abs_mul,Finset.mul_sum]

theorem nativeThetaAdaptiveTarget_smul (n : ℕ) (a : ℝ) (P : ℝ[X]) :
    nativeThetaAdaptiveTarget n (a • P) = |a| *nativeThetaAdaptiveTarget n P := by
  rw [nativeThetaAdaptiveTarget,nativeThetaCoefficientMass_smul,nativeThetaAdaptiveTarget]
  ring

theorem nativeSourceCofactorTarget_eq_scaled (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    nativeThetaAdaptiveTarget n (nativeSourceCofactorThetaPolynomial s n) =
      (nativeSourcePrefixDet s n)^2*nativeThetaAdaptiveTarget n (nativeSchurThetaPolynomial s n) := by
  rw [nativeSourceCofactorThetaPolynomial_eq_scaled s n hA,nativeThetaAdaptiveTarget_smul,
    abs_of_nonneg (sq_nonneg _)]

theorem nativeSourceCofactorTarget_pos (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    0 < nativeThetaAdaptiveTarget n (nativeSourceCofactorThetaPolynomial s n) := by
  rw [nativeSourceCofactorTarget_eq_scaled s n hA]
  exact mul_pos (sq_pos_of_ne_zero (nativeSourcePrefixDet_ne_zero s n hA))
    (nativeSchurThetaAdaptiveTarget_pos s n)

/-- Quantitative SOURCE obligation after the modal error has been bounded.
This is an equivalent algebraic formulation, not a proof of either side. -/
theorem nativeSourceCofactor_margin_iff (s n : ℕ) (a : ℝ)
    (hA : IsUnit (sourceMomentMatrix m s n)) :
    a*nativeThetaAdaptiveTarget n (nativeSourceCofactorThetaPolynomial s n) ≤
        ((4*n+2*s+3 : ℕ) : ℝ)*nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n) ↔
    a*nativeThetaAdaptiveTarget n (nativeSchurThetaPolynomial s n) ≤
        ((4*n+2*s+3 : ℕ) : ℝ)*nativeSourceSchurRemainder s n := by
  rw [nativeSourceCofactorTarget_eq_scaled s n hA,nativeSourceCofactorThetaPolynomial_integral s n hA]
  have hp := sq_pos_of_ne_zero (nativeSourcePrefixDet_ne_zero s n hA)
  rw [show a*((nativeSourcePrefixDet s n)^2*nativeThetaAdaptiveTarget n (nativeSchurThetaPolynomial s n)) =
    (nativeSourcePrefixDet s n)^2*(a*nativeThetaAdaptiveTarget n (nativeSchurThetaPolynomial s n)) by ring,
    show ((4*n+2*s+3 : ℕ) : ℝ)*((nativeSourcePrefixDet s n)^2*nativeSourceSchurRemainder s n) =
      (nativeSourcePrefixDet s n)^2*(((4*n+2*s+3 : ℕ) : ℝ)*nativeSourceSchurRemainder s n) by ring]
  exact mul_le_mul_iff_right₀ hp

end
end CarrySelfAdjointOperator
