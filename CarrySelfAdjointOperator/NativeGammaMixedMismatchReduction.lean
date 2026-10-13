import CarrySelfAdjointOperator.NativeGammaMixedResponse
import CarrySelfAdjointOperator.NativeGammaMixedOrthogonality
import CarrySelfAdjointOperator.NativeGammaMismatchLedger

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem nativeCanonicalGamma_cameraSix_eq_powers (z : ℂ) :
    nativeCanonicalGammaCoefficients z 4 =
      (3 : ℂ) ^ (-operatorHeightParameter z) - (2 : ℂ) ^ (-operatorHeightParameter z) := by
  rw [nativeCanonicalGammaCoefficients_cameraSix]
  norm_num [positiveDirichletGradient, natDirichletTerm, dirichletTerm]

theorem nativeMixedVector_eq_sqrt_unit : nativeMixedVector =
    (Real.sqrt 278 : ℂ) • nativeMixedUnitVector := by
  have hs : (Real.sqrt 278 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [nativeMixedUnitVector, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem nativeMixedGammaKernel_unnormalized (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    inner ℂ (carryGammaComplexState z hz nativeMixedVector)
      (carryGammaComplexState w hw nativeMixedVector) =
      278 * nativeMixedGammaKernel z w hz hw := by
  have hs : (Real.sqrt 278 : ℂ) ^ 2 = 278 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 278)
  rw [nativeMixedVector_eq_sqrt_unit, carryGammaComplexState_complex_smul,
    carryGammaComplexState_complex_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  change (Real.sqrt 278 : ℂ) * ((Real.sqrt 278 : ℂ) * nativeMixedGammaKernel z w hz hw) = _
  rw [← mul_assoc, ← pow_two, hs]

theorem nativeCanonicalMixedGamma_Gram (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
      (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) =
      (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients w 4 * nativeMixedGammaKernel z w hz hw := by
  rw [← nativeCanonicalMixedSource_eq_original, ← nativeCanonicalMixedSource_eq_original,
    nativeMixedCoefficients, nativeMixedCoefficients, map_smul, map_smul,
    carryGammaComplexState_complex_smul, carryGammaComplexState_complex_smul,
    inner_smul_left, inner_smul_right]
  change conj (_ / 3) * (_ / 3 * inner ℂ (carryGammaComplexState z hz nativeMixedVector)
    (carryGammaComplexState w hw nativeMixedVector)) = _
  rw [nativeMixedGammaKernel_unnormalized]
  simp only [map_div₀, map_ofNat]
  ring

theorem nativeCanonicalGamma_boundary_mixedReduction (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients w 4 *
        (conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse w) +
      (w - conj z) * inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3PolarizedGammaKernel
  rw [nativeCanonicalGamma_mixed_complement_Gram, nativeCanonicalMixedGamma_Gram, mul_add]
  rw [show (w - conj z) * ((278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
      nativeCanonicalGammaCoefficients w 4 * nativeMixedGammaKernel z w hz hw) =
    (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
      nativeCanonicalGammaCoefficients w 4 * ((w - conj z) * nativeMixedGammaKernel z w hz hw) by ring,
    nativeMixedGammaKernel_greenIdentity]

theorem nativeGammaMismatch_mixedComplementReduction (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients w 4 *
        (conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse w) +
      (w - conj z) * inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) -
      completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_gammaReadout_sub_nativeWronskian
    z w hz hw hzStrip hwStrip, nativeCanonicalGamma_boundary_mixedReduction]

theorem nativeGammaMismatch_mixedReduction_materialLedger (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients w 4 *
        (conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse w) +
      (w - conj z) * inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) -
      completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion w z =
      -nativeGammaMetricDefect C z w hz hw - nativeGammaReferenceDefect C k z w -
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialFirstPort C z) (nativeGammaMaterialGraphDefect C k w hw) +
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialGraphDefect C k z hz) (nativeGammaMaterialFirstPort C w) -
      2 * canonicalCompletedC3NativeSourceLocusScalarGreenForm z w := by
  rw [← nativeGammaMismatch_mixedComplementReduction z w hz hw hzStrip hwStrip]
  exact nativeGammaMismatch_materialDefectLedger C k z w hz hw

end
end CarrySelfAdjointOperator.GammaMaterialSewing
