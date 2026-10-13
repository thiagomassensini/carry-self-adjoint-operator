import CarrySelfAdjointOperator.NativeGammaMixedMaterialBalance
import CarrySelfAdjointOperator.NativeGammaMixedMismatchReduction
import CarrySelfAdjointOperator.NativeGammaMixedVariance
import CarrySelfAdjointOperator.NativeGammaExteriorGramPositivity
import CarrySelfAdjointOperator.NativeGammaNaimarkHaloEscape
import CarrySelfAdjointOperator.NativeGammaObservableTransportCapstone

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
open PhysicalSewing NativeLaguerre CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem nativeCanonicalGamma_resolventThreeSectorRoundtrip (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaState z hz =
      nativeComplexNaimarkPort (nativeSixCameraSynthesis
        (nativeGammaResponseCoordinates z hz (nativeCanonicalGammaCoefficients z))) +
      nativeComplexNaimarkPort (nativeGammaResponseHalo z hz (nativeCanonicalGammaCoefficients z)) +
      nativeGammaGlobalEscape z hz (nativeCanonicalGammaSource z) := by
  change carryGammaComplexState z hz (nativeCanonicalGammaSource z) = _
  rw [nativeCanonicalGammaSource_eq_synthesis]
  exact nativeGammaResolvent_threeSector_roundtrip z hz _

theorem nativeCanonicalGammaMaterialAmbientPair_literal (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMaterialAmbientPair C k (nativeCanonicalGammaPair z hz) =
      twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz) := by
  simp only [nativeGammaMaterialAmbientPair, nativeCanonicalGammaPair, nativeCanonicalGammaSource_coordinates]
  rfl

theorem nativeCanonicalGammaMaterialMixedPairs_roundtrip (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMaterialAmbientPair C k (nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z)) +
      nativeGammaMaterialAmbientPair C k (nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z)) =
      twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz) := by
  rw [← nativeGammaMaterialAmbientPair_add, nativeCanonicalGammaMixedPairs_roundtrip,
    nativeCanonicalGammaMaterialAmbientPair_literal]

/-- Full original pair, independent Cauchy producers, both mixed crossings,
native exteriors and both physical head/tail terms are retained. -/
theorem nativeGammaMixedTransport_capstone (C k R : ℕ) (hC : 1 ≤ C)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    gammaMaterialReconstruct C k (gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState z hz)) =
      canonicalCompletedC3GammaBoundaryState z hz ∧
    gammaMaterialReconstruct C k (gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState w hw)) =
      canonicalCompletedC3GammaBoundaryState w hw ∧
    nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z) +
      nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z) = nativeCanonicalGammaPair z hz ∧
    nativeGammaMaterialAmbientPair C k (nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z)) +
      nativeGammaMaterialAmbientPair C k (nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z)) =
      twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz) ∧
    ((∀ a, nativeGammaMaterialProbes C k z hz a = 0) ↔ nativeGammaMaterialGraphDefect C k z hz = 0) ∧
    (nativeGammaMaterialAmbientGreenHeadTail C R
      (nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z))
      (nativeGammaComplementPair w hw (nativeCanonicalGammaCoefficients w)) +
        gammaMaterialMetricFormDefect C
          (nativeGammaMixedPair z hz (nativeCanonicalGammaCoefficients z))
          (nativeGammaComplementPair w hw (nativeCanonicalGammaCoefficients w)) = 0 ∧
     nativeGammaMaterialAmbientGreenHeadTail C R
      (nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z))
      (nativeGammaMixedPair w hw (nativeCanonicalGammaCoefficients w)) +
        gammaMaterialMetricFormDefect C
          (nativeGammaComplementPair z hz (nativeCanonicalGammaCoefficients z))
          (nativeGammaMixedPair w hw (nativeCanonicalGammaCoefficients w)) = 0) ∧
    nativeComplexSixCameraNaimarkEscape (carryGammaComplexState z hz (nativeCanonicalGammaSource z)) =
      nativeComplexNaimarkPort (nativeGammaResponseHalo z hz (nativeCanonicalGammaCoefficients z)) +
      nativeGammaGlobalEscape z hz (nativeCanonicalGammaSource z) := by
  refine ⟨canonicalGammaMaterialTransport_reconstruct C k hC z hz,
    canonicalGammaMaterialTransport_reconstruct C k hC w hw,
    nativeCanonicalGammaMixedPairs_roundtrip z hz,
    nativeCanonicalGammaMaterialMixedPairs_roundtrip C k z hz,
    gammaMaterialGraphDefect_faithful C k z hz,
    nativeGammaMixedPairs_materialHeadTailCrossBalance C R z w hz hw _ _, ?_⟩
  rw [nativeCanonicalGammaSource_eq_synthesis]
  exact nativeGammaSixCameraEscape_eq_halo_add_globalEscape z hz _

/-- Applied reduction of the existing mismatch. No exterior, remainder
response or undressed Wronskian is assumed to vanish. -/
theorem nativeGammaMixedResolvent_capstone (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3PolarizedGammaState z hz =
      nativeComplexNaimarkPort (nativeSixCameraSynthesis
        (nativeGammaResponseCoordinates z hz (nativeCanonicalGammaCoefficients z))) +
      nativeComplexNaimarkPort (nativeGammaResponseHalo z hz (nativeCanonicalGammaCoefficients z)) +
      nativeGammaGlobalEscape z hz (nativeCanonicalGammaSource z) ∧
    (inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourcePart z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) = 0 ∧
      inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourcePart w)) = 0) ∧
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      (278/9 : ℂ) * conj (nativeCanonicalGammaCoefficients z 4) *
        nativeCanonicalGammaCoefficients w 4 *
        (conj (nativeMixedCauchyResponse z) - nativeMixedCauchyResponse w) +
      (w - conj z) * inner ℂ (carryGammaComplexState z hz (canonicalC3ReturnSourceRemainder z))
        (carryGammaComplexState w hw (canonicalC3ReturnSourceRemainder w)) -
      completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion w z ∧
    nativeMixedResolventVariance z =
      ‖nativeSixCameraExterior (nativeComplexCauchy z hz nativeMixedUnitVector)‖ ^ 2 +
      ‖nativeGammaGlobalEscape z hz nativeMixedUnitVector‖ ^ 2 ∧
    0 < nativeMixedResolventVariance nativeC9WitnessPoint ∧
    nativeSixCameraExterior (canonicalCompletedC3GammaBoundaryState nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1).2 ≠ 0 :=
  ⟨nativeCanonicalGamma_resolventThreeSectorRoundtrip z hz,
    nativeCanonicalGamma_mixed_complement_orthogonal z w hz hw,
    nativeGammaMismatch_mixedComplementReduction z w hz hw hzStrip hwStrip,
    nativeMixedResolventVariance_exact z hz, nativeMixedResolventVariance_witness_positive,
    originalCanonicalGammaCauchyTrace_hasExterior⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing
