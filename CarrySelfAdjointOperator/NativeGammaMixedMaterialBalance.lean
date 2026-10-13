import CarrySelfAdjointOperator.NativeGammaMixedOrthogonality
import CarrySelfAdjointOperator.NativeGammaMaterialHeadTailLedger

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

def nativeGammaSourcePair (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    CarryGammaComplexCamera × CarryGammaComplexCamera :=
  (nativeSixCameraSynthesis c, nativeComplexCauchy z hz (nativeSixCameraSynthesis c))

def nativeGammaMixedPair (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :=
  nativeGammaSourcePair z hz (nativeMixedCoefficients c)

def nativeGammaComplementPair (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :=
  nativeGammaSourcePair z hz (nativeMixedComplement c)

theorem nativeCanonicalGammaMixedPair_literal (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z) =
      (canonicalC3ReturnSourcePart z, nativeComplexCauchy z hz (canonicalC3ReturnSourcePart z)) := by
  unfold nativeGammaMixedPair nativeGammaSourcePair
  rw [nativeCanonicalMixedSource_eq_original]
  rfl

theorem nativeCanonicalGammaComplementPair_literal (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z) =
      (canonicalC3ReturnSourceRemainder z, nativeComplexCauchy z hz (canonicalC3ReturnSourceRemainder z)) := by
  unfold nativeGammaComplementPair nativeGammaSourcePair
  rw [nativeCanonicalComplementSource_eq_original]
  rfl

theorem nativeGammaMixedPairs_roundtrip (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    nativeGammaMixedPair z hz c + nativeGammaComplementPair z hz c = nativeGammaSourcePair z hz c := by
  unfold nativeGammaMixedPair nativeGammaComplementPair nativeGammaSourcePair
  have h := congrArg nativeSixCameraSynthesis (nativeMixedCoefficients_roundtrip c)
  rw [map_add] at h
  apply Prod.ext
  · exact h
  · change _ + _ = _
    rw [← map_add, h]

theorem nativeCanonicalGammaMixedPairs_roundtrip (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z) +
      nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z) = nativeCanonicalGammaPair z hz := by
  rw [nativeGammaMixedPairs_roundtrip]
  simp [nativeGammaSourcePair, nativeCanonicalGammaPair, nativeCanonicalGammaCauchyTrace,
    nativeCanonicalGammaSource_eq_synthesis]

def nativeGammaMaterialAmbientPair (C k : ℕ)
    (p : CarryGammaComplexCamera × CarryGammaComplexCamera) :=
  twoPortSynthesis (materialCameraWindow C) k
    (materialCameraLift C (nativeSixCameraCoordinates p.1))
    (materialCameraLift C (nativeSixCameraCoordinates p.2))

def nativeGammaMaterialAmbientDefect (C k : ℕ)
    (p : CarryGammaComplexCamera × CarryGammaComplexCamera) : Fin (materialCameraWindow C) → ℂ :=
  secondPortDefect (materialCameraWindow C) (radialResponse (materialCameraWindow C) k)
    (materialCameraLift C (nativeSixCameraCoordinates p.1))
    (materialCameraLift C (nativeSixCameraCoordinates p.2))

theorem nativeGammaMaterialAmbientPair_add (C k : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    nativeGammaMaterialAmbientPair C k (p+t) =
      nativeGammaMaterialAmbientPair C k p + nativeGammaMaterialAmbientPair C k t := by
  simp only [nativeGammaMaterialAmbientPair, Prod.fst_add, Prod.snd_add, map_add]
  unfold twoPortSynthesis twoPortReconstruct
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add, smul_sub] <;> module

theorem nativeGammaMaterialAmbientDefect_add (C k : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    nativeGammaMaterialAmbientDefect C k (p+t) =
      nativeGammaMaterialAmbientDefect C k p + nativeGammaMaterialAmbientDefect C k t := by
  ext j
  simp [nativeGammaMaterialAmbientDefect, secondPortDefect, map_add]
  ring

theorem nativeGammaMixedPairs_Green_crossings (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (c d : Fin 6 → ℂ) :
    nativeGammaPairForm (nativeGammaMixedPair z hz c) (nativeGammaComplementPair w hw d) = 0 ∧
    nativeGammaPairForm (nativeGammaComplementPair z hz c) (nativeGammaMixedPair w hw d) = 0 := by
  have h1 := carryGammaComplex_twoParameter_greenIdentity z w hz hw
    (nativeSixCameraSynthesis (nativeMixedCoefficients c))
    (nativeSixCameraSynthesis (nativeMixedComplement d))
  have h2 := carryGammaComplex_twoParameter_greenIdentity z w hz hw
    (nativeSixCameraSynthesis (nativeMixedComplement c))
    (nativeSixCameraSynthesis (nativeMixedCoefficients d))
  rw [nativeGamma_mixed_complement_orthogonal, mul_zero] at h1
  rw [nativeGamma_complement_mixed_orthogonal, mul_zero] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem nativeGammaMixedPairs_materialCrossBalance (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
      (nativeGammaMaterialAmbientPair C k (nativeGammaMixedPair z hz c))
      (nativeGammaMaterialAmbientPair C k (nativeGammaComplementPair w hw d)) +
        gammaMaterialMetricFormDefect C (nativeGammaMixedPair z hz c) (nativeGammaComplementPair w hw d) = 0 ∧
    gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
      (nativeGammaMaterialAmbientPair C k (nativeGammaComplementPair z hz c))
      (nativeGammaMaterialAmbientPair C k (nativeGammaMixedPair w hw d)) +
        gammaMaterialMetricFormDefect C (nativeGammaComplementPair z hz c) (nativeGammaMixedPair w hw d) = 0 := by
  have hp (a : Fin 6 → ℂ) (b : Fin 6 → ℂ)
      (h : nativeGammaPairForm (nativeGammaSourcePair z hz a) (nativeGammaSourcePair w hw b) = 0) :
      gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
        (nativeGammaMaterialAmbientPair C k (nativeGammaSourcePair z hz a))
        (nativeGammaMaterialAmbientPair C k (nativeGammaSourcePair w hw b)) +
          gammaMaterialMetricFormDefect C (nativeGammaSourcePair z hz a) (nativeGammaSourcePair w hw b) = 0 := by
    have hl := nativeGammaPairForm_materialLedger C (nativeGammaSourcePair z hz a)
      (nativeGammaSourcePair w hw b)
    have he : gammaMaterialExteriorForm (nativeGammaSourcePair z hz a) (nativeGammaSourcePair w hw b) = 0 := by
      simp [gammaMaterialExteriorForm, nativeGammaSourcePair, nativeSixCameraExterior_synthesis]
    rw [h, he, add_zero] at hl
    rw [nativeGammaMaterialAmbientPair, nativeGammaMaterialAmbientPair, gammaPhysicalGreenScale_form]
    exact hl.symm
  exact ⟨hp _ _ (nativeGammaMixedPairs_Green_crossings z w hz hw c d).1,
    hp _ _ (nativeGammaMixedPairs_Green_crossings z w hz hw c d).2⟩

def nativeGammaMaterialAmbientGreenHeadTail (C R : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) : ℂ :=
  gammaPhysicalPairHeadTail (materialCameraWindow C) R
      (materialCameraLift C (nativeSixCameraCoordinates p.1))
      (materialCameraLift C (nativeSixCameraCoordinates t.2)) -
    gammaPhysicalPairHeadTail (materialCameraWindow C) R
      (materialCameraLift C (nativeSixCameraCoordinates p.2))
      (materialCameraLift C (nativeSixCameraCoordinates t.1))

theorem nativeGammaMaterialAmbientGreenHeadTail_eq_form (C k R : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    nativeGammaMaterialAmbientGreenHeadTail C R p t =
      gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
        (nativeGammaMaterialAmbientPair C k p) (nativeGammaMaterialAmbientPair C k t) := by
  unfold nativeGammaMaterialAmbientGreenHeadTail nativeGammaMaterialAmbientPair
  rw [gammaPhysicalGreenScale_form, gammaPhysicalPair_headTail _ R, gammaPhysicalPair_headTail _ R]

theorem nativeGammaMixedPairs_materialHeadTailCrossBalance (C R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    nativeGammaMaterialAmbientGreenHeadTail C R
        (nativeGammaMixedPair z hz c) (nativeGammaComplementPair w hw d) +
      gammaMaterialMetricFormDefect C (nativeGammaMixedPair z hz c) (nativeGammaComplementPair w hw d) = 0 ∧
    nativeGammaMaterialAmbientGreenHeadTail C R
        (nativeGammaComplementPair z hz c) (nativeGammaMixedPair w hw d) +
      gammaMaterialMetricFormDefect C (nativeGammaComplementPair z hz c) (nativeGammaMixedPair w hw d) = 0 := by
  rw [nativeGammaMaterialAmbientGreenHeadTail_eq_form C 0 R,
    nativeGammaMaterialAmbientGreenHeadTail_eq_form C 0 R]
  exact nativeGammaMixedPairs_materialCrossBalance C 0 z w hz hw c d

end
end CarrySelfAdjointOperator.GammaMaterialSewing
