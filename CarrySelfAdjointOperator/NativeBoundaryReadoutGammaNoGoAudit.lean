import CarrySelfAdjointOperator.NativeBoundaryReadoutHPIntertwining
import CarrySelfAdjointOperator.C3GammaCameraTraceObstruction

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The literal canonical Gamma/native boundary readout cannot satisfy the
global completed Wronskian sewing.  The obstruction is witnessed by the
already compiled diagonal counterexamples arbitrarily close to the Taylor
center; no zero-locus, Gram, or moment hypothesis is used. -/
theorem not_canonicalNativeBoundaryCompletedReadoutSewing_of_cameraFive_counterexample :
    ¬ CanonicalNativeBoundaryCompletedReadoutSewing := by
  intro hsewing
  obtain ⟨t, ht, _, _, _, _, hraw⟩ :=
    canonicalC3RawDefect_counterexamples_arbitrarily_close
      1 (by norm_num)
  let z : ℂ := Complex.I * (t : ℂ)
  have hz : z.im ≠ 0 := by
    simpa [z] using ne_of_gt ht
  have hreadout :
      canonicalNativeBoundaryReadout z z hz hz =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z := by
    simpa [z] using hsewing z z hz hz
  have hnativeDefect :
      canonicalNativeBoundaryReadoutDefect z z hz hz = 0 := by
    unfold canonicalNativeBoundaryReadoutDefect
    rw [hreadout]
    exact sub_self _
  have hrawZero :
      canonicalCompletedC3RawGammaWronskianDefect z z hz hz = 0 := by
    rw [← canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect
      z z hz hz]
    exact hnativeDefect
  exact hraw hz hrawZero

end

end CarrySelfAdjointOperator
