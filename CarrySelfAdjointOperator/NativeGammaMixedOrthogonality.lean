import CarrySelfAdjointOperator.NativeGammaMixedMultiplierOrthogonality
import CarrySelfAdjointOperator.NativeGammaComplexLinearState

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

theorem nativeMixedRay_re : (fun i => (nativeMixedRay i).re) = sixCameraMixedReturnRay := by
  ext i
  fin_cases i <;> rfl

theorem nativeMixedRay_im : (fun i => (nativeMixedRay i).im) = 0 := by
  ext i
  fin_cases i <;> norm_num [nativeMixedRay]

theorem nativeGammaMixedRay_complement_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c : Fin 6 → ℂ) (hc : c 4 = 0) :
    inner ℂ (carryGammaComplexState z hz nativeMixedVector)
      (carryGammaComplexState w hw (nativeSixCameraSynthesis c)) = 0 := by
  have hr : (c 4).re = 0 := by rw [hc]; rfl
  have hi : (c 4).im = 0 := by rw [hc]; rfl
  have ho (a b : BoundedRealNaimarkMultiplier) (f : Fin 6 → ℝ) (hf : f 4 = 0) :
      inner ℝ (boundedRealNaimarkMultiplier a (nativeRealSixNaimarkSynthesis sixCameraMixedReturnRay))
        (boundedRealNaimarkMultiplier b (nativeRealSixNaimarkSynthesis f)) = 0 :=
    nativeMixed_multiplier_orthogonal a b f hf
  have hrr := ho (logarithmicResolventRealMultiplier z hz)
    (logarithmicResolventRealMultiplier w hw) (fun i => (c i).re) hr
  have hri := ho (logarithmicResolventRealMultiplier z hz)
    (logarithmicResolventImaginaryMultiplier w hw) (fun i => (c i).im) hi
  have hir := ho (logarithmicResolventImaginaryMultiplier z hz)
    (logarithmicResolventImaginaryMultiplier w hw) (fun i => (c i).re) hr
  have hii := ho (logarithmicResolventImaginaryMultiplier z hz)
    (logarithmicResolventRealMultiplier w hw) (fun i => (c i).im) hi
  have hrr' := ho (logarithmicResolventRealMultiplier z hz)
    (logarithmicResolventImaginaryMultiplier w hw) (fun i => (c i).re) hr
  have hri' := ho (logarithmicResolventRealMultiplier z hz)
    (logarithmicResolventRealMultiplier w hw) (fun i => (c i).im) hi
  have hir' := ho (logarithmicResolventImaginaryMultiplier z hz)
    (logarithmicResolventRealMultiplier w hw) (fun i => (c i).re) hr
  have hii' := ho (logarithmicResolventImaginaryMultiplier z hz)
    (logarithmicResolventImaginaryMultiplier w hw) (fun i => (c i).im) hi
  simp only [RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner, carryGammaComplexState_re, carryGammaComplexState_im]
  rw [nativeMixedVector, nativeSixCameraSynthesis_naimark_re,
    nativeSixCameraSynthesis_naimark_im, nativeMixedRay_re, nativeMixedRay_im,
    nativeSixCameraSynthesis_naimark_re, nativeSixCameraSynthesis_naimark_im]
  have hzero : nativeRealSixNaimarkSynthesis 0 = 0 := by simp [nativeRealSixNaimarkSynthesis]
  simp only [hzero, map_zero, sub_zero, add_zero]
  simp only [logarithmicResolventRealOperator,
    logarithmicResolventImaginaryOperator, inner_sub_right, inner_add_right,
    hrr, hri, hir, hii, hrr', hri', hir', hii', add_zero, sub_zero,
    Complex.ofReal_zero, mul_zero]

theorem nativeGamma_mixed_complement_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ (carryGammaComplexState z hz (nativeSixCameraSynthesis (nativeMixedCoefficients c)))
      (carryGammaComplexState w hw (nativeSixCameraSynthesis (nativeMixedComplement d))) = 0 := by
  rw [nativeMixedCoefficients, map_smul, carryGammaComplexState_complex_smul, inner_smul_left]
  change conj (c 4 / 3) * inner ℂ (carryGammaComplexState z hz nativeMixedVector) _ = 0
  rw [nativeGammaMixedRay_complement_orthogonal z w hz hw _ (nativeMixedComplement_cameraSix d), mul_zero]

theorem nativeGamma_complement_mixed_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ (carryGammaComplexState z hz (nativeSixCameraSynthesis (nativeMixedComplement c)))
      (carryGammaComplexState w hw (nativeSixCameraSynthesis (nativeMixedCoefficients d))) = 0 := by
  rw [← inner_conj_symm, nativeGamma_mixed_complement_orthogonal, map_zero]

theorem nativeCanonicalGamma_mixed_complement_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) :
    inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) = 0 ∧
    inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) = 0 := by
  rw [← nativeCanonicalMixedSource_eq_original, ← nativeCanonicalComplementSource_eq_original,
    ← nativeCanonicalMixedSource_eq_original, ← nativeCanonicalComplementSource_eq_original]
  exact ⟨nativeGamma_mixed_complement_orthogonal _ _ _ _ _ _,
    nativeGamma_complement_mixed_orthogonal _ _ _ _ _ _⟩

theorem nativeCanonicalGamma_mixed_complement_Gram (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) :
    inner ℂ (canonicalCompletedC3PolarizedGammaState z hz)
      (canonicalCompletedC3PolarizedGammaState w hw) =
    inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) +
    inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) := by
  rw [canonicalC3GammaState_eq_returnPart_add_remainder,
    canonicalC3GammaState_eq_returnPart_add_remainder]
  simp only [inner_add_left, inner_add_right,
    (nativeCanonicalGamma_mixed_complement_orthogonal z w hz hw).1,
    (nativeCanonicalGamma_mixed_complement_orthogonal z w hz hw).2, add_zero, zero_add]

end
end CarrySelfAdjointOperator.GammaMaterialSewing
