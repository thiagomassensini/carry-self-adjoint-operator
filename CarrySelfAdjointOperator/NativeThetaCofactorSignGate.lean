import CarrySelfAdjointOperator.NativeThetaCofactorMargin

/-! Logical strength of the remaining source sign. The cofactor polynomials
are defined without inverse matrices. Their all-order strict integral sign is
EQUIVALENT to the existing Stieltjes gate; this module does not prove that sign.
The confinement theorem below is explicitly conditional on that open gate. -/
namespace CarrySelfAdjointOperator
open Matrix
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

def NativeThetaCofactorSign : Prop :=
  ∀ n : ℕ,
    0 < nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial 0 n) ∧
      0 < nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial 1 n)

theorem nativeSourceCofactor_pos_implies_schur_pos (s n : ℕ)
    (h : 0 < nativeXiPolynomialIntegral (nativeSourceCofactorThetaPolynomial s n)) :
    0 < nativeSourceSchurRemainder s n := by
  have hD : nativeSourcePrefixDet s n ≠ 0 := by
    intro hz
    rw [nativeSourceCofactorThetaPolynomial_integral_bordered,hz,mul_zero,zero_mul] at h
    exact (lt_irrefl _ h)
  have hA : IsUnit (sourceMomentMatrix m s n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hD)
  rw [nativeSourceCofactorThetaPolynomial_integral s n hA] at h
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hD)).mp h

theorem nativeThetaCofactorSign_iff_stieltjes :
    NativeThetaCofactorSign ↔ CanonicalCompletedNativeStieltjesPositivity := by
  constructor
  · intro h
    apply nativeSourceEvenBoundary_positive_iff_stieltjes.mp
    apply nativeSourceBoundary_all_pos_iff_sourceSchur.mpr
    intro n
    exact ⟨nativeSourceCofactor_pos_implies_schur_pos 0 n (h n).1,
      nativeSourceCofactor_pos_implies_schur_pos 1 n (h n).2⟩
  · intro h n
    have hR := nativeSourceBoundary_all_pos_iff_sourceSchur.mp
      (nativeSourceEvenBoundary_positive_iff_stieltjes.mpr h) n
    have hH0 : (sourceMomentMatrix m 0 n).PosDef := by
      change (Matrix.of (fun i j : Fin n => m (i.val+j.val))).PosDef
      exact (h n).1
    have hH1 : (sourceMomentMatrix m 1 n).PosDef := by
      change (Matrix.of (fun i j : Fin n => m (i.val+j.val+1))).PosDef
      exact (h n).2
    constructor
    · rw [nativeSourceCofactorThetaPolynomial_integral 0 n hH0.isUnit]
      exact mul_pos (sq_pos_of_ne_zero (nativeSourcePrefixDet_ne_zero 0 n hH0.isUnit)) hR.1
    · rw [nativeSourceCofactorThetaPolynomial_integral 1 n hH1.isUnit]
      exact mul_pos (sq_pos_of_ne_zero (nativeSourcePrefixDet_ne_zero 1 n hH1.isUnit)) hR.2

/-- No all-order positivity is proved here. This conditional consequence shows
that the remaining source sign has the full existing native confinement force. -/
theorem completedNative_zero_im_eq_zero_of_thetaCofactorSign
    (h : NativeThetaCofactorSign) {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) : z.im = 0 := by
  exact completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (nativeThetaCofactorSign_iff_stieltjes.mp h) hzDomain hzero

end
end CarrySelfAdjointOperator
