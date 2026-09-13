import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import Mathlib.Tactic

/-!
# Causal Green to Hilbert trace transport before moments

This file records the exact native route which precedes the Hankel/Jacobi
layer.  The causal Green response is paired with its boundary return, the
sum reconstructs the original completed gradient state, and the native
Hilbert trace glue then reads the resulting pair as the carry-weighted
vertical Wronskian.  The final chiral response identity is included only as
the scalar coefficient readout; no positive Green-moment carrier is inserted
by this theorem.

The separation is intentional.  The signed Wronskian/chiral readout is an
exact consequence of the native construction, whereas a single positive
carrier whose Gram is the canonical moment kernel is a stronger sewing gate.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The actual causal response and its boundary return pass through the
native Hilbert trace without introducing a moment or Jacobi object. -/
theorem canonicalCompletedNativeCausalGreenBoundaryTraceTransport
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (S : Finset NativeGpreBoundaryContext) :
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
          canonicalCompletedNativeLogDerivativeMoment p q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact canonicalCompletedC3CausalGreenBoundary_native_source_response
      hbase hs
  · exact
      (canonicalCompletedNativeCarryGreenIncidenceCrosswalk hbase hradius).2.1
  · exact canonicalCompletedC3CausalGreenBoundarySum_state hbase hs
  · rw [canonicalNativeHilbertGluedTraceGreenDefect_eq_verticalWronskian,
      canonicalCompletedC3CausalGreenBoundarySum_state hbase hs,
      canonicalCompletedC3CausalGreenBoundarySum_state hbase ht]
  · intro M p q
    exact canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment
      M p q

end

end CarrySelfAdjointOperator
