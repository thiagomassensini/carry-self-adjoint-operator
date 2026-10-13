import CarrySelfAdjointOperator.NativeGammaMixedMismatchReduction

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ComplexConjugate InnerProductSpace
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem nativeConjugate_offAxis (z : ℂ) (hz : z.im ≠ 0) : (conj z).im ≠ 0 := by
  simpa only [Complex.conj_im, neg_ne_zero] using hz

theorem nativeGammaConjugate_boundaryReadout_zero (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z (conj z) hz
      (nativeConjugate_offAxis z hz) = 0 := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  simp only [sub_self, zero_mul]

theorem nativeGammaConjugate_mixedResponse_zero (z : ℂ) (hz : z.im ≠ 0) :
    conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse (conj z) = 0 := by
  have h := nativeMixedGammaKernel_greenIdentity z (conj z) hz (nativeConjugate_offAxis z hz)
  simpa only [sub_self, zero_mul] using h.symm

theorem nativeGammaConjugate_mixedComplementReadouts_zero (z : ℂ) (hz : z.im ≠ 0) :
    (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients (conj z) 4 *
        (conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse (conj z)) = 0 ∧
    (conj z - conj z) * inner ℂ
        (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState (conj z) (nativeConjugate_offAxis z hz)
          (canonicalC3ReturnSourceRemainder (conj z))) = 0 := by
  rw [nativeGammaConjugate_mixedResponse_zero z hz]
  simp only [mul_zero, sub_self, zero_mul, and_self]

theorem nativeSourceLocusMismatch_conjugateCollision (z : ℂ) (hz : z.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hcs : operatorHeightParameter (conj z) ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z (conj z) hz
      (nativeConjugate_offAxis z hz) =
      -completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion (conj z) z := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_gammaReadout_sub_nativeWronskian
    z (conj z) hz (nativeConjugate_offAxis z hz) hs hcs,
    nativeGammaConjugate_boundaryReadout_zero, zero_sub]

theorem nativeImaginaryCollision_admissible (t : ℝ) (ht : 0 < |t|) (hsmall : |t| < 1/2) :
    (Complex.I * (t : ℂ)).im ≠ 0 ∧ (-Complex.I * (t : ℂ)).im ≠ 0 ∧
    operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
    operatorHeightParameter (-Complex.I * (t : ℂ)) ∈ genuineCriticalStrip := by
  have hne : t ≠ 0 := abs_pos.mp ht
  have hlo := (abs_lt.mp hsmall).1
  have hhi := (abs_lt.mp hsmall).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hne
  · simpa using neg_ne_zero.mpr hne
  · change 0 < (operatorHeightParameter (Complex.I * (t : ℂ))).re ∧
      (operatorHeightParameter (Complex.I * (t : ℂ))).re < 1
    norm_num [operatorHeightParameter, Complex.mul_re, Complex.mul_im]
    constructor <;> linarith
  · change 0 < (operatorHeightParameter (-Complex.I * (t : ℂ))).re ∧
      (operatorHeightParameter (-Complex.I * (t : ℂ))).re < 1
    norm_num [operatorHeightParameter, Complex.mul_re, Complex.mul_im]
    constructor <;> linarith

theorem nativeSourceLocusMismatch_imaginaryCollision (t : ℝ) (ht : 0 < |t|) (hsmall : |t| < 1/2)
    (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch
        (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw =
      -completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion
        (-Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) := by
  have ha := nativeImaginaryCollision_admissible t ht hsmall
  have hconj : conj (Complex.I * (t : ℂ)) = -Complex.I * (t : ℂ) := by simp
  simpa only [hconj] using nativeSourceLocusMismatch_conjugateCollision _ hz ha.2.2.1
    (by simpa only [hconj] using ha.2.2.2)

end
end CarrySelfAdjointOperator.GammaMaterialSewing
