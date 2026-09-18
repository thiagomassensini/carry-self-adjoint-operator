import CarrySelfAdjointOperator.CompletedC3CoisometricWronskianProjectionGate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The Gamma--TFVD energy balance is not the sewing theorem.  Even after the
balance is supplied as zero, the diagonal sewing is exactly the independent
raw Gamma--Wronskian defect equation. -/
theorem canonicalCompletedC3CoisometricSewing_iff_rawDefect_of_gammaBalance_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hbalance : canonicalCompletedC3GammaCorrectionBalance
      z hz hzStrip.1 = 0) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3RawGammaWronskianDefect z z hz hz = 0 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gammaCorrectionBalance
    z hz hzStrip]
  rw [hbalance]
  simp

end
end CarrySelfAdjointOperator
