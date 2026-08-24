import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkLimitBridge
import Mathlib.Tactic

/-!
# Completed bracket--TFVD--Green factorization

This file makes the order of the completed sewing explicit.  A single
cutoff-indexed carrier retains the canonical enriched TFVD transport together
with the unresolved value and log-jet tails.  Its scalar trace and its C3
Green port are projections of that same carrier.

The completed Wronskian is first identified with the tail-completed TFVD
trace.  Independently, the TFVD Green port is identified with the Genuine
bracket port and only then read by the lossless two-quadrature Naimark map.
No Green--Wronskian equality, zero hypothesis, or early real projection is
used in either identification.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

open scoped BigOperators ComplexConjugate Topology

noncomputable section

/-! ## One carrier for TFVD head, tails, and bracket port -/

/-- Cutoff-indexed enriched TFVD state before any scalar boundary pairing.
The finite transport and the two unresolved tails remain separate fields. -/
structure CanonicalC3BracketTfvdCompletionState (M : ℕ) where
  transport : FiniteC3EnrichedTfvdPairTransportData M
  valueTail : ℂ
  logJetTail : ℂ

namespace CanonicalC3BracketTfvdCompletionState

/-- Tail-completed value projection of the structured TFVD state. -/
def valueReadout {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) : ℂ :=
  state.transport.valueReadout + state.valueTail

/-- Tail-completed log-jet projection of the structured TFVD state. -/
def logJetReadout {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) : ℂ :=
  state.transport.logJetReadout + state.logJetTail

/-- Complete C3 Green port retained by the same structured TFVD state. -/
def greenPort {M : ℕ}
    (state : CanonicalC3BracketTfvdCompletionState M) :
    FiniteC3GreenPortCarrier (M * 3) :=
  state.transport.greenPort

end CanonicalC3BracketTfvdCompletionState

/-- Canonical bracket state at cutoff `M`, with both completion tails stored
beside, rather than substituted for, the enriched TFVD transport. -/
def canonicalC3BracketTfvdCompletionState
    (M : ℕ) (s : ℂ) : CanonicalC3BracketTfvdCompletionState M where
  transport := canonicalBoundaryResidualData
    M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ)) s
  valueTail := realCpBracketCutoffTail 3 M s
  logJetTail := canonicalC3LogJetCutoffTail M s

/-- The finite value head, finite log-jet head, and Genuine bracket port are
simultaneous projections of one canonical structured state. -/
theorem canonicalC3BracketTfvdCompletionState_transport_components
    (M : ℕ) (s : ℂ) :
    let state := canonicalC3BracketTfvdCompletionState M s
    (state.transport.valueReadout =
        finiteBracketedDirichletChart 3 M s) ∧
    (state.transport.logJetReadout =
        finiteCanonicalLogBracketChart M s) ∧
    (state.greenPort =
        finiteC3GenuineBracketGreenBoundaryPair (M * 3) s) := by
  simpa [canonicalC3BracketTfvdCompletionState,
    CanonicalC3BracketTfvdCompletionState.greenPort,
    canonicalBoundaryResidualData, canonicalBoundaryResidualPair] using
    (finiteC3EnrichedTfvdPairTransport_canonical
      M tfvdHaarScale_ne_zero (fun _ : ℕ ↦ (1 : ℂ))
      (by intro m; norm_num) s)

/-- The value projection of the structured state is the existing
cutoff-completed enriched TFVD value coordinate. -/
theorem canonicalC3BracketTfvdCompletionState_valueReadout_eq_cutoffCompleted
    (M : ℕ) (s : ℂ) :
    (canonicalC3BracketTfvdCompletionState M s).valueReadout =
      canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout M s := by
  rfl

/-- The log-jet projection of the structured state is the existing
cutoff-completed enriched TFVD log-jet coordinate. -/
theorem canonicalC3BracketTfvdCompletionState_logJetReadout_eq_cutoffCompleted
    (M : ℕ) (s : ℂ) :
    (canonicalC3BracketTfvdCompletionState M s).logJetReadout =
      canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout M s := by
  rw [CanonicalC3BracketTfvdCompletionState.logJetReadout]
  rw [(canonicalC3BracketTfvdCompletionState_transport_components M s).2.1]
  rfl

/-- Head plus value tail is independent of the cutoff and equals the
canonical completed enriched TFVD value. -/
theorem canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    (canonicalC3BracketTfvdCompletionState M s).valueReadout =
      canonicalCompletedC3EnrichedTfvdValueTailReadout s := by
  rw [canonicalC3BracketTfvdCompletionState_valueReadout_eq_cutoffCompleted]
  exact canonicalCompletedC3FiniteEnrichedTfvdValueTailReadout_eq_completed
    M hs

/-- Head plus log-jet tail is independent of the cutoff and equals the
canonical completed enriched TFVD log jet. -/
theorem canonicalC3BracketTfvdCompletionState_logJetReadout_eq_completed
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    (canonicalC3BracketTfvdCompletionState M s).logJetReadout =
      canonicalCompletedC3EnrichedTfvdLogJetTailReadout s := by
  rw [canonicalC3BracketTfvdCompletionState_logJetReadout_eq_cutoffCompleted]
  exact canonicalCompletedC3FiniteEnrichedTfvdLogJetTailReadout_eq_completed
    M hs

/-- The Green projection of the very same state is the Genuine bracket port,
before a Green form or scalar readout is applied. -/
theorem canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket
    (M : ℕ) (s : ℂ) :
    (canonicalC3BracketTfvdCompletionState M s).greenPort =
      finiteC3GenuineBracketGreenBoundaryPair (M * 3) s :=
  (canonicalC3BracketTfvdCompletionState_transport_components M s).2.2

/-! ## The completed `(F,-F')` trace is a projection of the same state -/

/-- Chart-normalized value projection, formed from the structured TFVD value
only after its head and tail have been joined. -/
def canonicalC3BracketTfvdNormalizedValueReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  (canonicalC3BracketTfvdCompletionState M
      (operatorHeightParameter z)).valueReadout /
    cpChartFactor 3 (operatorHeightParameter z)

/-- Chart-normalized companion.  Value and log-jet channels remain separate
until this quotient-rule readout. -/
def canonicalC3BracketTfvdNormalizedLogJetReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  let state := canonicalC3BracketTfvdCompletionState M s
  Complex.I *
    ((state.logJetReadout * cpChartFactor 3 s +
        state.valueReadout * deriv (cpChartFactor 3) s) /
      cpChartFactor 3 s ^ 2)

/-- Xi-completed value obtained from the bracket-derived TFVD state. -/
def canonicalC3BracketTfvdCompletedValueReadout
    (M : ℕ) (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z *
    canonicalC3BracketTfvdNormalizedValueReadout M z

/-- Xi product companion obtained from the two still separated normalized
TFVD channels. -/
def canonicalC3BracketTfvdBoundaryCompanion
    (M : ℕ) (z : ℂ) : ℂ :=
  nativeXiCompletionBoundaryCompanion z *
      canonicalC3BracketTfvdNormalizedValueReadout M z +
    nativeXiCompletionFactor z *
      canonicalC3BracketTfvdNormalizedLogJetReadout M z

/-- Completed scalar trace pair read from the structured bracket--TFVD
state. -/
def canonicalC3BracketTfvdCompletedTracePair
    (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  (canonicalC3BracketTfvdCompletedValueReadout M z,
    canonicalC3BracketTfvdBoundaryCompanion M z)

theorem canonicalC3BracketTfvdNormalizedValueReadout_eq_cutoff
    (M : ℕ) (z : ℂ) :
    canonicalC3BracketTfvdNormalizedValueReadout M z =
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout
        M z := by
  unfold canonicalC3BracketTfvdNormalizedValueReadout
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout
  rw [canonicalC3BracketTfvdCompletionState_valueReadout_eq_cutoffCompleted]

theorem canonicalC3BracketTfvdNormalizedLogJetReadout_eq_cutoff
    (M : ℕ) (z : ℂ) :
    canonicalC3BracketTfvdNormalizedLogJetReadout M z =
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout
        M z := by
  unfold canonicalC3BracketTfvdNormalizedLogJetReadout
    canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout
  dsimp only
  rw [canonicalC3BracketTfvdCompletionState_logJetReadout_eq_cutoffCompleted,
    canonicalC3BracketTfvdCompletionState_valueReadout_eq_cutoffCompleted]

theorem canonicalC3BracketTfvdCompletedValueReadout_eq_cutoff
    (M : ℕ) (z : ℂ) :
    canonicalC3BracketTfvdCompletedValueReadout M z =
      canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout
        M z := by
  unfold canonicalC3BracketTfvdCompletedValueReadout
    canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout
  rw [canonicalC3BracketTfvdNormalizedValueReadout_eq_cutoff]

theorem canonicalC3BracketTfvdBoundaryCompanion_eq_cutoff
    (M : ℕ) (z : ℂ) :
    canonicalC3BracketTfvdBoundaryCompanion M z =
      canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion M z := by
  unfold canonicalC3BracketTfvdBoundaryCompanion
    canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion
    productBoundaryCompanion
  rw [canonicalC3BracketTfvdNormalizedValueReadout_eq_cutoff,
    canonicalC3BracketTfvdNormalizedLogJetReadout_eq_cutoff]

/-- At every cutoff, the completed trace projection is the canonical
tail-completed enriched TFVD trace pair. -/
theorem canonicalC3BracketTfvdCompletedTracePair_eq_completed
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalC3BracketTfvdCompletedTracePair M z =
      canonicalCompletedC3TracePair z := by
  unfold canonicalC3BracketTfvdCompletedTracePair
    canonicalCompletedC3TracePair
  apply Prod.ext
  · rw [canonicalC3BracketTfvdCompletedValueReadout_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdCompletedValueTailReadout_eq_completed
        M hs]
  · rw [canonicalC3BracketTfvdBoundaryCompanion_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdBoundaryCompanion_eq_completed
        M hs]

/-- The bracket-derived completed TFVD trace is literally `(F,-F')`.
The Genuine Green port has not been read or used in this proof. -/
theorem canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime
    (M : ℕ) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalC3BracketTfvdCompletedTracePair M z =
      (completedNativeOperatorCharacteristic z,
        -deriv completedNativeOperatorCharacteristic z) := by
  rw [canonicalC3BracketTfvdCompletedTracePair_eq_completed M hs,
    canonicalCompletedC3TracePair_eq_F_negFprime hs]

/-- Polarized scalar Wronskian read only after the completed trace pair has
been reconstructed from the structured TFVD state at both points. -/
def canonicalC3BracketTfvdCompletedWronskianReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
    (canonicalC3BracketTfvdCompletedTracePair M z).1
    (canonicalC3BracketTfvdCompletedTracePair M z).2
    (canonicalC3BracketTfvdCompletedTracePair M w).1
    (canonicalC3BracketTfvdCompletedTracePair M w).2

/-- The Wronskian of `(F,-F')` factors through the completed enriched TFVD
trace, with no Green identity in the proof. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalC3BracketTfvdCompletedWronskianReadout M z w =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
        z w := by
  unfold canonicalC3BracketTfvdCompletedWronskianReadout
  rw [canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hw]
  rfl

/-! ## The other projection: enriched TFVD to bracket to Green -/

/-- Mixed enriched pair used before scalarization: its value leg comes from
`w` and its log-jet leg comes from `z`. -/
def canonicalC3BracketTfvdMixedPair (z w : ℂ) :
    EnrichedTfvdValueLogJetPair :=
  canonicalMixedBoundaryResidualPair
    tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ)) z w

/-- Direct mixed transport.  Its Green port depends on the retained value
leg and therefore realizes the bracket at `w`. -/
def canonicalC3BracketTfvdMixedDirectTransport
    (M : ℕ) (z w : ℂ) : FiniteC3EnrichedTfvdPairTransportData M :=
  finiteC3EnrichedTfvdPairTransport
    M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ)) w
    (canonicalC3BracketTfvdMixedPair z w)

/-- Reflected canonical transport paired with the direct mixed transport. -/
def canonicalC3BracketTfvdMixedReflectedTransport
    (M : ℕ) (z : ℂ) : FiniteC3EnrichedTfvdPairTransportData M :=
  finiteC3EnrichedTfvdPairTransport
    M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ))
    (reflectedParameter z)
    (canonicalBoundaryResidualPair tfvdHaarScale
      (fun _ : ℕ ↦ (1 : ℂ)) (reflectedParameter z))

/-- TFVD boundary readout corrected only by its independently constructed
block Green provenance.  No Green form appears in this definition. -/
def canonicalC3BracketTfvdMixedCorrectedBoundary
    (M : ℕ) (z w : ℂ) : ℂ :=
  let pair := canonicalC3BracketTfvdMixedPair z w
  let direct := canonicalC3BracketTfvdMixedDirectTransport M z w
  let reflected := canonicalC3BracketTfvdMixedReflectedTransport M z
  finiteC3EnrichedTfvdPairBoundaryForm M direct -
    finiteC3EnrichedTfvdPairGreenProvenance
      M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ))
      pair direct reflected

/-- The direct mixed Green port is the Green projection of the canonical
completion state at `w`; changing the log-jet leg does not change this port. -/
theorem canonicalC3BracketTfvdMixedDirectTransport_greenPort
    (M : ℕ) (z w : ℂ) :
    (canonicalC3BracketTfvdMixedDirectTransport M z w).greenPort =
      (canonicalC3BracketTfvdCompletionState M w).greenPort := by
  rfl

/-- The reflected mixed Green port is the Green projection of the canonical
completion state at the reflected parameter. -/
theorem canonicalC3BracketTfvdMixedReflectedTransport_greenPort
    (M : ℕ) (z : ℂ) :
    (canonicalC3BracketTfvdMixedReflectedTransport M z).greenPort =
      (canonicalC3BracketTfvdCompletionState M
        (reflectedParameter z)).greenPort := by
  rfl

/-- Two real Naimark quadratures applied to the two Green-port projections of
the structured TFVD states. -/
def canonicalC3BracketTfvdMixedGreenQuadratures
    (M : ℕ) (z w : ℂ) : FiniteC3SymplecticGreenQuadratures :=
  finiteC3SymplecticNaimarkGreenQuadratures (M * 3)
    (canonicalC3BracketTfvdCompletionState M w).greenPort
    (canonicalC3BracketTfvdCompletionState M
      (reflectedParameter z)).greenPort

/-- Complex Green readout, formed only after retaining both real Naimark
quadratures. -/
def canonicalC3BracketTfvdMixedGreenReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  (canonicalC3BracketTfvdMixedGreenQuadratures M z w).complexReadout

/-- The Naimark reconstruction is exactly the complex Green form of the two
TFVD Green-port projections. -/
theorem canonicalC3BracketTfvdMixedGreenReadout_eq_stateGreen
    (M : ℕ) (z w : ℂ) :
    canonicalC3BracketTfvdMixedGreenReadout M z w =
      greenForm (𝕜 := ℂ)
        (canonicalC3BracketTfvdCompletionState M w).greenPort
        (canonicalC3BracketTfvdCompletionState M
          (reflectedParameter z)).greenPort := by
  unfold canonicalC3BracketTfvdMixedGreenReadout
    canonicalC3BracketTfvdMixedGreenQuadratures
  exact finiteC3SymplecticNaimark_complexReadout_eq_greenForm _ _ _

/-- Only after the TFVD-port identity is established is the readout
identified with the Green form of the two Genuine bracket ports. -/
theorem canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen
    (M : ℕ) (z w : ℂ) :
    canonicalC3BracketTfvdMixedGreenReadout M z w =
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (M * 3) w)
        (finiteC3GenuineBracketGreenBoundaryPair
          (M * 3) (reflectedParameter z)) := by
  rw [canonicalC3BracketTfvdMixedGreenReadout_eq_stateGreen,
    canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket,
    canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket]

/-- The independently defined corrected TFVD boundary is the Green readout
of those same state projections.  This is the honest
`bracket -> enriched TFVD -> Green` factorization. -/
theorem canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout
    (M : ℕ) (z w : ℂ) :
    canonicalC3BracketTfvdMixedCorrectedBoundary M z w =
      canonicalC3BracketTfvdMixedGreenReadout M z w := by
  have htransport :=
    finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance_twoParameter
      M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ))
      w (reflectedParameter z)
      (canonicalC3BracketTfvdMixedPair z w)
      (canonicalBoundaryResidualPair tfvdHaarScale
        (fun _ : ℕ ↦ (1 : ℂ)) (reflectedParameter z))
  dsimp only at htransport
  have htransport' :
      finiteC3EnrichedTfvdPairBoundaryForm M
          (canonicalC3BracketTfvdMixedDirectTransport M z w) =
        greenForm
            (canonicalC3BracketTfvdMixedDirectTransport M z w).greenPort
            (canonicalC3BracketTfvdMixedReflectedTransport M z).greenPort +
          finiteC3EnrichedTfvdPairGreenProvenance
            M tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ))
            (canonicalC3BracketTfvdMixedPair z w)
            (canonicalC3BracketTfvdMixedDirectTransport M z w)
            (canonicalC3BracketTfvdMixedReflectedTransport M z) := by
    simpa [canonicalC3BracketTfvdMixedDirectTransport,
      canonicalC3BracketTfvdMixedReflectedTransport] using htransport
  unfold canonicalC3BracketTfvdMixedCorrectedBoundary
  dsimp only
  rw [htransport',
    canonicalC3BracketTfvdMixedDirectTransport_greenPort,
    canonicalC3BracketTfvdMixedReflectedTransport_greenPort,
    ← canonicalC3BracketTfvdMixedGreenReadout_eq_stateGreen]
  ring

/-- Compatibility with the all-cutoff mixed Green readout constructed in the
global Naimark bridge. -/
theorem canonicalC3BracketTfvdMixedGreenReadout_eq_globalNaimarkReadout
    (M : ℕ) (z w : ℂ) :
    canonicalC3BracketTfvdMixedGreenReadout M z w =
      canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M z w := by
  rw [canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen,
    canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_eq_greenForm]
  rw [Nat.mul_comm M 3]

/-! ## The completed sewing diagram with every channel retained -/

/-- The radial field of the existing six-channel ledger is the xi-weighted
Green readout extracted from the bracket-derived TFVD state. -/
theorem canonicalCompletedC3FiniteFNegFPrimeMixedChannels_radialGreen_eq_bracketTfvd
    (M : ℕ) (z w : ℂ) :
    (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).radialGreen =
      mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalC3BracketTfvdMixedGreenReadout M
          (operatorHeightParameter z) (operatorHeightParameter w) := by
  calc
    (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).radialGreen =
        canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout
          M z w :=
      (canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout_eq_ledger
        M z w).symm
    _ = mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3FiniteMixedSymplecticNaimarkGreenReadout M
            (operatorHeightParameter z) (operatorHeightParameter w) := rfl
    _ = mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3BracketTfvdMixedGreenReadout M
            (operatorHeightParameter z) (operatorHeightParameter w) := by
      rw [canonicalC3BracketTfvdMixedGreenReadout_eq_globalNaimarkReadout]

/-- The complete six-channel TFVD ledger reads the same completed Wronskian
as the trace projection of the structured bracket--TFVD state. -/
theorem canonicalCompletedC3FiniteFNegFPrimeMixedChannels_finalReadout_eq_bracketTfvdWronskian
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).finalReadout =
      mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        canonicalC3BracketTfvdCompletedWronskianReadout M z w := by
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    M hz hw]
  exact finalScalarReadout_eq_completedFNegFPrimeWronskian M hz hw

/-- Exact completed sewing in the honest order

`completed Wronskian -> enriched TFVD ledger -> bracket Green readout`.

Every non-radial channel remains explicit.  In particular this theorem does
not assert their vanishing. -/
theorem completedWronskian_factors_through_bracketTfvd_then_green
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        canonicalC3BracketTfvdCompletedWronskianReadout M z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3BracketTfvdMixedGreenReadout M
            (operatorHeightParameter z) (operatorHeightParameter w) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).archimedeanChart := by
  rw [← canonicalCompletedC3FiniteFNegFPrimeMixedChannels_finalReadout_eq_bracketTfvdWronskian
    M hz hw]
  unfold CanonicalCompletedC3FNegFPrimeMixedChannels.finalReadout
  rw [canonicalCompletedC3FiniteFNegFPrimeMixedChannels_radialGreen_eq_bracketTfvd]

/-- The same sewing with the intermediate corrected TFVD boundary visible.
Green is reached only through the independently proved TFVD-port theorem. -/
theorem completedWronskian_factors_through_correctedTfvdBoundary_then_green
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight z w *
        canonicalC3BracketTfvdCompletedWronskianReadout M z w =
      mixedHermitianWeight nativeXiCompletionFactor z w *
          canonicalC3BracketTfvdMixedCorrectedBoundary M
            (operatorHeightParameter z) (operatorHeightParameter w) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels
          M z w).archimedeanChart := by
  rw [canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout]
  exact completedWronskian_factors_through_bracketTfvd_then_green M hz hw

/-! ## Completion of the honest TFVD-to-Green route -/

/-- The corrected TFVD boundary itself converges to the completed radial
Green kernel.  The proof passes through its bracket port and the global
Naimark readout, not through a Wronskian identity. -/
theorem canonicalC3BracketTfvdMixedCorrectedBoundary_tendsto_completedGreen
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ ↦ canonicalC3BracketTfvdMixedCorrectedBoundary M z w)
      atTop
      (nhds
        (canonicalCompletedC3MixedRadialGreenKernel
          z w hw hzReflected)) := by
  exact
    (canonicalC3FiniteMixedSymplecticNaimarkGreenReadout_tendsto_completed
      hw hzReflected).congr'
      (Eventually.of_forall fun M ↦ by
        exact ((canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout
          M z w).trans
          (canonicalC3BracketTfvdMixedGreenReadout_eq_globalNaimarkReadout
            M z w)).symm)

/-- Candidate global Green readout written through the corrected enriched
TFVD boundary, with the chart channel retained until the final addition. -/
def canonicalC3BracketTfvdGlobalGreenReadout
    (M : ℕ) (z w : ℂ) : ℂ :=
  mixedHermitianWeight nativeXiCompletionFactor z w *
      canonicalC3BracketTfvdMixedCorrectedBoundary M
        (operatorHeightParameter z) (operatorHeightParameter w) +
    canonicalCompletedC3ArchimedeanChartMixedChannel z w

/-- The bracket--TFVD global readout is exactly the concrete global Naimark
Green readout already constructed. -/
theorem canonicalC3BracketTfvdGlobalGreenReadout_eq_symplectic
    (M : ℕ) (z w : ℂ) :
    canonicalC3BracketTfvdGlobalGreenReadout M z w =
      canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout
        M z w := by
  unfold canonicalC3BracketTfvdGlobalGreenReadout
    canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout
    canonicalCompletedC3FiniteFNegFPrimeSymplecticRadialReadout
  rw [canonicalC3BracketTfvdMixedCorrectedBoundary_eq_greenReadout,
    canonicalC3BracketTfvdMixedGreenReadout_eq_globalNaimarkReadout]

/-- Exact remaining frontier after forcing the route through bracket and
enriched TFVD: convergence to the completed Wronskian is equivalent to the
same explicit structural no-leak condition. -/
theorem canonicalC3BracketTfvdGlobalGreenReadout_tendsto_wronskian_iff
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    Tendsto
        (fun M : ℕ ↦ canonicalC3BracketTfvdGlobalGreenReadout M z w)
        atTop
        (nhds
          (mixedHermitianWeight canonicalC3ChartFactorHeight z w *
            completedGreenWronskian
              completedNativeOperatorCharacteristic
              (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
              z w)) ↔
      Tendsto
        (fun M : ℕ ↦
          canonicalC3FiniteMixedHeightStructuralDefect M
            (operatorHeightParameter z) (operatorHeightParameter w))
        atTop (nhds 0) := by
  constructor
  · intro h
    exact
      (canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto_wronskian_iff
        hz hw).mp
        (h.congr' (Eventually.of_forall fun M ↦
          canonicalC3BracketTfvdGlobalGreenReadout_eq_symplectic M z w))
  · intro h
    have hsymplectic :=
      (canonicalCompletedC3FiniteFNegFPrimeSymplecticGlobalGreenReadout_tendsto_wronskian_iff
        hz hw).mpr h
    exact hsymplectic.congr'
      (Eventually.of_forall fun M ↦
        (canonicalC3BracketTfvdGlobalGreenReadout_eq_symplectic M z w).symm)

end

end CarrySelfAdjointOperator
