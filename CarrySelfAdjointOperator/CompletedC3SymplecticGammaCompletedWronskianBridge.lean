import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/--
Exact completed sewing ledger for the corrected symplectic Gamma source.

The weighted mismatch between the corrected positive Gamma boundary
and the completed `(F,-F')` Wronskian splits into exactly four
already-existing geometric channels:

1. dynamic Cauchy boundary minus static symplectic Green;
2. finite structural defect;
3. head-tail completion defect;
4. archimedean/chart completion channel.

No vanishing, zero, confinement, HP, Hankel or Jacobi hypothesis
is used.
-/
theorem
canonicalCompletedC3WeightedSymplecticGammaBoundary_sub_completedWronskian
    {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
          w z =
    mixedHermitianWeight nativeXiCompletionFactor w z *
        (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
          canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) -
      mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalC3FiniteMixedHeightStructuralDefect 1
          (operatorHeightParameter w) (operatorHeightParameter z) -
      mixedHermitianWeight nativeXiCompletionFactor w z *
        canonicalC3MixedHeightTailCompletionDefect 1 w z -
      canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  have hcompletion :=
    completedFNegFPrimeWronskian_crossedChartIdentity
      (z := w) (w := z) hwStrip hzStrip

  have hgamma :=
    canonicalCompletedC3SymplecticGammaBoundary_sub_rawWronskian
      (z := z) (w := w) hz hw hzStrip hwStrip

  calc
    mixedHermitianWeight nativeXiCompletionFactor w z *
          canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
            w z =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
            canonicalCompletedC3RawHeightMixedWronskian w z) -
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
      rw [hcompletion]
      ring
    _ =
        mixedHermitianWeight nativeXiCompletionFactor w z *
              (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
                canonicalCompletedC3SymplecticCameraComplexGreenReadout
                  z (conj w)) -
          mixedHermitianWeight nativeXiCompletionFactor w z *
              canonicalC3FiniteMixedHeightStructuralDefect 1
                (operatorHeightParameter w) (operatorHeightParameter z) -
          mixedHermitianWeight nativeXiCompletionFactor w z *
              canonicalC3MixedHeightTailCompletionDefect 1 w z -
          canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
      rw [hgamma]
      ring

end

end CarrySelfAdjointOperator
