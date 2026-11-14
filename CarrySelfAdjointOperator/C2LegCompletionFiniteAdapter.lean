import CarrySelfAdjointOperator.C2LegCompletionPolarization
import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The C2 height-line chart is the repository's original finite C2
characteristic, with its own seed, aligned centers, and cutoff. -/
theorem c2FiniteChartHeightValue_eq_originalC2Characteristic
    (cutoff : ℕ) (time : ℝ) :
    c2FiniteChartHeightValue cutoff (time : ℂ) =
      finiteBracketCharacteristic 2 cutoff (nativeLine time) := by
  rw [c2FiniteChartHeightValue,
    c2FiniteChartValue_eq_nativeFiniteCharacteristic]
  congr 1

/-- The dressing keeps the original completion numerator and C2 camera
denominator. -/
theorem c2CompletionDressing_eq_originalCompletion_div_c2Factor
    (z : ℂ) :
    c2CompletionDressing z =
      nativeXiCompletionFactor z / c2Factor (c2SpectralLine z) := by
  simp [c2CompletionDressing, factor_two]

/-- Exact algebraic comparison of the physical Gamma boundary with the finite
C2 source and its central proxy. The Gamma residual is retained explicitly. -/
theorem c2FiniteSourceGammaWronskian_split
    (cutoff : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2PolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCompanion cutoff x) z w =
      (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) -
      (c2PolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCompanion cutoff x) z w -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) := by
  ring

/-- Finite adapter with the proved leg formula inserted. The first parenthesis
is the outstanding Gamma-versus-central comparison. -/
theorem c2FiniteSourceGammaWronskian_split_with_legs
    (cutoff : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2PolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCompanion cutoff x) z w =
      (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) -
      (Complex.I * star (c2CompletionDressing z) *
        c2CompletionDressing w *
          (star (c2FiniteChartHeightValue cutoff z) *
              c2FiniteChartHeightLegCorrection cutoff w +
            star (c2FiniteChartHeightLegCorrection cutoff z) *
              c2FiniteChartHeightValue cutoff w)) := by
  calc
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2PolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCompanion cutoff x) z w =
      (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) -
      (c2PolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCompanion cutoff x) z w -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) :=
      c2FiniteSourceGammaWronskian_split cutoff z w hz hw
    _ = (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        c2CentralPolarizedWronskian
          (fun x => c2FiniteChartHeightCharacteristic cutoff x)
          (fun x => c2FiniteChartHeightCentralCompanion cutoff x) z w) -
      (Complex.I * star (c2CompletionDressing z) *
        c2CompletionDressing w *
          (star (c2FiniteChartHeightValue cutoff z) *
              c2FiniteChartHeightLegCorrection cutoff w +
            star (c2FiniteChartHeightLegCorrection cutoff z) *
              c2FiniteChartHeightValue cutoff w)) := by
      rw [c2FiniteChartHeightWronskian_sub_central_eq_legCorrection]

end
end CarrySelfAdjointOperator
