import CarrySelfAdjointOperator.NativeGammaMaterialHeadTailLedger
import CarrySelfAdjointOperator.NativeGammaMaterialPolynomialProvenance
import CarrySelfAdjointOperator.NativeGammaOrientationObstruction
import CarrySelfAdjointOperator.NativeGammaC9Density

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped Matrix InnerProductSpace
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

theorem canonicalGammaMaterialTransport_literal (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState z hz) =
      (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz),
        (0,nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace z hz))) := by
  change gammaMaterialTransport C k (nativeCanonicalGammaPair z hz) = _
  simp only [gammaMaterialTransport, nativeCanonicalGammaPair, nativeCanonicalGammaSource_coordinates,
    nativeCanonicalGammaSource_noExterior]
  rfl

/-- Whole native pair reconstruction precedes every scalar readout. -/
theorem canonicalGammaMaterialTransport_reconstruct (C k : ℕ) (hC : 1 ≤ C)
    (z : ℂ) (hz : z.im ≠ 0) :
    gammaMaterialReconstruct C k
      (gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState z hz)) =
      canonicalCompletedC3GammaBoundaryState z hz :=
  gammaMaterialTransport_roundtrip C k hC _

theorem gammaMaterialFirstPort_SourceJet (C k : ℕ) (z : ℂ) :
    nativeSourceProjectiveBoundaryJetSynthesis (materialCameraWindow C) k
      (physicalEndpointJetInput (2*materialCameraWindow C) k
        (extendMaterial (materialCameraWindow C) (2*materialCameraWindow C) (nativeGammaMaterialFirstPort C z))) =
      finiteProjectiveSource (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z) := by
  rw [physicalEndpointJetInput_wholeSource,
    finiteProjectiveSource_extend _ _ k (by omega)]

theorem gammaMaterialFirstPort_correctedGreen (C k : ℕ) (z : ℂ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    finiteProjectiveSource (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z) =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (finRadialCoefficients (materialCameraWindow C) (nativeGammaMaterialFirstPort C z)) +
        physicalGreenResidualNumerator q k (finRadialCoefficients (materialCameraWindow C) (nativeGammaMaterialFirstPort C z))) := by
  rw [← physicalCompletedFiniteSource_fin]
  exact physicalCompletedFiniteGreen_reconstruct q hq0 hq1 k _

/-- An exterior sector of the form vanishes while its canonical vector is nonzero. -/
theorem canonicalExterior_sectorZero_vectorNonzero :
    gammaMaterialExteriorForm (nativeCanonicalGammaPair nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1)
      (nativeCanonicalGammaPair nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1) = 0 ∧
    nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1) ≠ 0 :=
  ⟨nativeGammaCanonicalExterior_sector_zero _ _ _ _, canonicalGammaCauchyTrace_hasExterior⟩

/-- Applied capstone: literal pair, complete transport, faithful defect probes,
the existing mismatch with its actual orientation, and a nonzero original exterior. -/
theorem nativeGammaObservableTransport_capstone (C k : ℕ) (hC : 1 ≤ C)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    gammaMaterialReconstruct C k (gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState z hz)) =
      canonicalCompletedC3GammaBoundaryState z hz ∧
    gammaMaterialTransport C k (canonicalCompletedC3GammaBoundaryState z hz) =
      (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz), (0,nativeSixCameraExterior (nativeCanonicalGammaCauchyTrace z hz))) ∧
    ((∀ a, nativeGammaMaterialProbes C k z hz a = 0) ↔ nativeGammaMaterialGraphDefect C k z hz = 0) ∧
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      -nativeGammaMetricDefect C z w hz hw - nativeGammaReferenceDefect C k z w -
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialGraphDefect C k w hw) +
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialGraphDefect C k z hz)
        (nativeGammaMaterialFirstPort C w) - 2*canonicalCompletedC3NativeSourceLocusScalarGreenForm z w ∧
    nativeSixCameraExterior (canonicalCompletedC3GammaBoundaryState nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1).2 ≠ 0 :=
  ⟨canonicalGammaMaterialTransport_reconstruct C k hC z hz,
    canonicalGammaMaterialTransport_literal C k z hz,
    gammaMaterialGraphDefect_faithful C k z hz,
    nativeGammaMismatch_materialDefectLedger C k z w hz hw,
    originalCanonicalGammaCauchyTrace_hasExterior⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing
