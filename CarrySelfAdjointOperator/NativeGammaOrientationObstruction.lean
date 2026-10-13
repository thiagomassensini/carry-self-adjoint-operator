import CarrySelfAdjointOperator.NativeGammaMismatchLedger
import CarrySelfAdjointOperator.NativeGammaCanonicalExteriorWitness

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace
open NativeCarrySpectralWeyl.Infinite
noncomputable section
set_option autoImplicit false

theorem nativeGammaPairForm_self_im (p : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    (nativeGammaPairForm p p).im = 2*(inner ℂ p.1 p.2).im := by
  have hr : (inner ℂ p.2 p.1).im = -(inner ℂ p.1 p.2).im := by
    rw [← inner_conj_symm]
    rfl
  unfold nativeGammaPairForm
  rw [Complex.sub_im, hr]
  ring

theorem nativeCanonicalGammaPairForm_witness_ne_zero :
    nativeGammaPairForm (nativeCanonicalGammaPair nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1)
      (nativeCanonicalGammaPair nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1) ≠ 0 := by
  have hp : 0 < nativeC9WitnessPoint.im := by norm_num [nativeC9WitnessPoint]
  have hn := canonicalCompletedC3SixCameraSource_ne_zero nativeC9WitnessPoint_strip
  have hsk := allBasesCauchyBlock_skewQuadratic_neg hp hn
  intro he
  have hi := congrArg Complex.im he
  rw [nativeGammaPairForm_self_im] at hi
  change 2*(RealHilbertComplexification.complexInner
    (nativeCanonicalGammaSource nativeC9WitnessPoint)
    (nativeCanonicalGammaCauchyTrace nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1)).im = 0 at hi
  rw [RealHilbertComplexification.complexInner_im] at hi
  change 2*(inner ℝ (canonicalCompletedC3SixCameraSource nativeC9WitnessPoint).fst
      (allBasesCauchyBlock nativeC9WitnessPoint hp.ne'
        (canonicalCompletedC3SixCameraSource nativeC9WitnessPoint)).snd -
    inner ℝ (canonicalCompletedC3SixCameraSource nativeC9WitnessPoint).snd
      (allBasesCauchyBlock nativeC9WitnessPoint hp.ne'
        (canonicalCompletedC3SixCameraSource nativeC9WitnessPoint)).fst) = 0 at hi
  linarith

/-- The proposed plus ledger is valid exactly when the native pair form vanishes. -/
theorem nativeGammaMismatch_proposedLedger_iff (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      nativeGammaMetricDefect C z w hz hw + nativeGammaReferenceDefect C k z w +
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialFirstPort C z) (nativeGammaMaterialGraphDefect C k w hw) -
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialGraphDefect C k z hz) (nativeGammaMaterialFirstPort C w)) ↔
      nativeGammaPairForm (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw) = 0 := by
  rw [← sub_eq_zero, nativeGammaMismatch_proposedLedgerDifference, mul_eq_zero]
  norm_num

theorem nativeGammaMismatch_proposedLedger_fails_at_witness (C k : ℕ) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch nativeC9WitnessPoint nativeC9WitnessPoint
      nativeC9WitnessPoint_admissible.1 nativeC9WitnessPoint_admissible.1 ≠
    nativeGammaMetricDefect C nativeC9WitnessPoint nativeC9WitnessPoint
        nativeC9WitnessPoint_admissible.1 nativeC9WitnessPoint_admissible.1 +
      nativeGammaReferenceDefect C k nativeC9WitnessPoint nativeC9WitnessPoint +
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialFirstPort C nativeC9WitnessPoint)
        (nativeGammaMaterialGraphDefect C k nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1) -
      NativeLaguerre.matrixPairing (NativeLaguerre.cauchyMatrix (materialCameraWindow C))
        (nativeGammaMaterialGraphDefect C k nativeC9WitnessPoint nativeC9WitnessPoint_admissible.1)
        (nativeGammaMaterialFirstPort C nativeC9WitnessPoint) := by
  intro he
  exact nativeCanonicalGammaPairForm_witness_ne_zero
    ((nativeGammaMismatch_proposedLedger_iff C k _ _ _ _).mp he)

end
end CarrySelfAdjointOperator.GammaMaterialSewing
