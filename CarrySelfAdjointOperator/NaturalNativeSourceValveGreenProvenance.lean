import CarrySelfAdjointOperator.CompletedNativeCorrectedGeometryHeightProvenance
import CarrySelfAdjointOperator.CompletedNativeCausalGreenTraceTransport
import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import CarrySelfAdjointOperator.GreenMultiplicativeValveBridge
import Mathlib.Tactic

/-!
# Natural native source, valve, and Green provenance before Gram

This file packages the source-direction part of the height construction.  The
C2 fibre/bracket identities, the exact centre tail, the multiplicative valve,
the causal Green return, and the four-corner native Hilbert carrier are all
assembled before any Hankel, Cholesky, Jacobi, or height operator is used.

The last material step is intentionally exposed as a named sewing defect in
the existing Green theorem.  Thus this theorem records the natural genealogy
of the operator without replacing the native carrier by a positive proxy.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open CPFormal.Carry.C2
open CPFormal.Carry.Cp
open CPFormal.Carry.Positional
open C3TraceDynamics
open FiniteNativeCarryOperator
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open ProjectiveDepth
open ProjectiveValve
open PowerSeries
open GreenMultiplicativeValveBridge
open Filter

noncomputable section

/--
The exact pre-Gram genealogy of the native height construction.

The first four fields are the C2 source, bracket/readout, tail, and completed
characteristic identities.  The next three are the formal valve identities.
The causal field supplies the Green source, boundary return, Hilbert trace,
and the already formalized incidence transport.  The four-corner field keeps
the genuine native Hilbert carrier visible before scalar moment extraction.
The final field states the exact remaining Wronskian sewing criterion.
-/
theorem canonicalC2Geometry_native_source_valve_green_preGram
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    (∀ j : ℕ,
        4 * (j + 1) =
            2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j ∧
          ((leftIncidence j).1.2 : ℝ) =
            c2FiberPoint (c2AlignedIndexCore j) (-1)
              (c2AlignedIndexDepth j) ∧
          ((rightIncidence j).1.2 : ℝ) =
            c2FiberPoint (c2AlignedIndexCore j) 1
              (c2AlignedIndexDepth j) ∧
          CPFormal.Carry.C2.effectiveDepth (leftIncidence j).1.2 =
            c2AlignedIndexDepth j ∧
          CPFormal.Carry.C2.effectiveDepth (rightIncidence j).1.2 =
            c2AlignedIndexDepth j ∧
          Real.log ((4 * (j + 1) : ℕ) : ℝ) =
            (c2AlignedIndexDepth j : ℝ) * Real.log 2 +
              primeDepthLogLedger (c2AlignedIndexCore j) ∧
          Real.log ((4 * (j + 1) : ℕ) : ℝ) *
              CPFormal.Carry.Cp.criticalAmplitude 2
                (c2AlignedIndexDepth j) =
            Real.log 2 * ProjectiveDepth.newtonJet
                (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1
                  (c2AlignedIndexDepth j) +
              primeDepthLogLedger (c2AlignedIndexCore j) *
                ProjectiveDepth.newtonJet
                  (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0
                    (c2AlignedIndexDepth j)) ∧
      (∀ (M order : ℕ),
        evalFormalStencil
            (fun n => nativeDirichletSlopeTaylorCoefficient order n)
            (finiteStencil 2 M) =
          evalFormalStencil
              (fun n => nativeDirichletSlopeTaylorCoefficient order n)
              (seedStencil 2) +
            ∑ j ∈ Finset.range M,
              c2FiberNativeTaylorBracket order
                (c2AlignedIndexCore j) (c2AlignedIndexDepth j)) ∧
      (∀ (M order : ℕ),
        evalFormalStencil
            (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
            (finiteStencil 2 M) =
          evalFormalStencil
              (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
              (seedStencil 2) +
            ∑ j ∈ Finset.range M,
              c2FiberAllOrderBracket order
                (c2AlignedIndexCore j) (c2AlignedIndexDepth j)) ∧
      (∀ (tailCutoff : ℕ) {s : ℂ}, s ∈ nativeScalarDomain →
        finiteBracketCharacteristic 2 tailCutoff s +
            (∑' index : ℕ,
              centerBracketTerm 2 s (index + tailCutoff)) =
          factor 2 s * nativeScalar s) ∧
      (∀ (packagedCutoff : ℕ) (time : ℝ),
        nativeXiCompletionFactor (time : ℂ) *
            completedPackagedFiniteNativeOperatorJet
              2 packagedCutoff 0 time /
              factor 2 (nativeLine time) =
          completedNativeOperatorCharacteristic (time : ℂ)) ∧
      normalizedCompletedNativeEvenFormalSeries =
        projectiveValveMass (-(mk canonicalCompletedNativeLogDerivativeMoment)) ∧
      projectiveValveCurvature normalizedCompletedNativeEvenFormalSeries⁻¹ =
        mk canonicalCompletedNativeLogDerivativeMoment ∧
      (∀ C : PowerSeries ℝ,
        d⁄dX ℝ (toProjective (greenLogPotential C)) = toProjective C) ∧
      (∀ {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
          (S : Finset NativeGpreBoundaryContext),
        (carryWeightedVerticalCenteredBracket
            (canonicalBR2CarryAmplitudeRatio base)
            (canonicalCompletedC3DirichletGradientCausalGreenState
              base s hs) =
          canonicalCompletedC3DirichletGradientBracketSourceState base s hs) ∧
        Nonempty (BR2BracketIncidenceJetTransport base radius
          (canonicalBR2CameraBracketCausalGreenResponseParityJet base radius)) ∧
        (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs) =
          canonicalCompletedC3DirichletGradientState s hs) ∧
        (canonicalNativeHilbertGluedTraceGreenDefect
            (canonicalBR2CarryAmplitudeRatio base) S
            (canonicalCompletedC3CausalGreenBoundarySum
              (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                hbase s hs))
            (canonicalCompletedC3CausalGreenBoundarySum
              (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
                hbase t ht)) =
          carryWeightedVerticalBoundaryWronskian
            (canonicalBR2CarryAmplitudeRatio base)
            (canonicalCompletedC3DirichletGradientState s hs)
            (canonicalCompletedC3DirichletGradientState t ht)) ∧
        (∀ (M p q : ℕ),
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
              M (p + q + 1) =
            polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment p q)) ∧
      (∀ (M : ℕ) (z w : ℂ),
        greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair M w)
            (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z)) =
          canonicalC3MixedRadialCoefficient z w *
            nativeGpreFourCornerPolarizedDirichletPrefix
              M w (reflectedParameter z) ∧
        (nativeGpreFourCornerPolarizedDirichletPrefix
            M w (reflectedParameter z) =
          inner ℂ
            (canonicalCompletedC3DirichletGradientPrefixState w M)
            (canonicalCompletedC3DirichletGradientPrefixState
              (reflectedParameter z) M)) ∧
        (nativeGpreFourCornerPolarizedDirichletPrefix
            M w (reflectedParameter z) =
          ∑ n ∈ Finset.range M,
            (starRingEnd ℂ) (positiveDirichletGradient w n) *
              sameEdgeRecoveredReflectedGradient n
                (positiveDirichletGradient z n)
                (positiveLogDirichletGradient z n))) ∧
      (∀ {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
          (hw : 0 < w.re),
        canonicalCompletedC3RawMixedWronskian z w =
            canonicalC3MixedRadialCoefficient z w *
              canonicalCompletedC3RawGammaGram
                w (reflectedParameter z) hw
                (by simpa [reflectedParameter] using sub_pos.mpr hzUpper) ↔
          Tendsto
            (fun M : ℕ => canonicalC3FiniteMixedTotalDefect M z w)
            atTop (nhds 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact canonicalC2Geometry_nativeSourceChain j
  · intro M order
    exact canonicalC2Geometry_nativeTaylorReadout_eq_seed_add_fibreBrackets
      M order
  · intro M order
    exact canonicalC2Geometry_logPowerReadout_eq_seed_add_fibreBrackets
      M order
  · intro tailCutoff s hs
    exact canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar
      tailCutoff hs
  · intro packagedCutoff time
    exact canonicalC2Geometry_completedPackagedNativeJet_zero_normalized_eq_commonCharacteristic
      packagedCutoff time
  · exact normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg
  · exact projectiveValveCurvature_nativeReciprocal_eq_moments
  · intro C
    exact derivative_toProjective_greenLogPotential C
  · intro s t hs ht S
    exact canonicalCompletedNativeCausalGreenBoundaryTraceTransport
      hbase hradius hs ht S
  · intro M z w
    exact canonicalCompletedNativeCarryGreenFourCornerProvenance M z w
  · intro z w hz hzUpper hw
    exact canonicalCompletedNativeCarryGreenWronskian_sewing_iff_totalDefect_zero
      hz hzUpper hw

end

end CarrySelfAdjointOperator
