import CarrySelfAdjointOperator.BR2CausalGreenResponseTransport
import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedNativeTfvdCameraIncidenceCandidateAudit
import CarrySelfAdjointOperator.CompletedC3FourTraceSymplecticBridge
import Mathlib.Tactic

/-!
# Pre-recovery BR2 incidence audit in the enriched TFVD carrier

The finite enriched TFVD analysis is the first existing carrier in the
genealogy which simultaneously accepts an arbitrary BR2 incidence and retains
the TFVD bracket, trace, and the two `G_pre` provenance roles.  It is therefore
strictly before `br2FiniteTfvdHilbertRecovery`.

This file does **not** identify that carrier with the parameter-seeded C3
six-camera ledger.  Instead it records the strongest transport already
available without that missing type bridge.  A causal response is analyzed in
the enriched TFVD carrier; its bracket coordinate is exactly the literal BR2
bracket, and the existing Parseval Green-frame analysis then realizes that
coordinate isometrically in a four-channel orthogonal carrier.

The resulting object is a genuine incidence-level total dilation, but it is
not yet a finite-camera visible realization of `C₆`: no existing map carries
the retained TFVD/provenance data to the required
`FiniteHilbertFamily state CarryVerticalL2` camera input.  Treating the whole
isometric state as visible is formally ruled out at the first Hankel test.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The incidence-level enriched state before recovery -/

/-- The actual enriched TFVD analysis of the causal BR2 response.  Its target
retains the TFVD bracket coordinate, trace coordinate, and both finite
provenance roles.  No TFVD reconstruction occurs in this definition. -/
def br2CausalTfvdPreRecoveryIncidenceMap
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    (ℕ →₀ ℝ) →ₗ[ℝ] NativeGpreFiniteTfvdAnalysisCarrier S :=
  ((nativeGpreFiniteTfvdAnalysis q S).toLinearMap.restrictScalars ℝ).comp
    (br2CameraBracketCausalGreenResponseMap q)

/-- The state of one bracket incidence in the retained enriched TFVD carrier.
This is the concrete low-order prototype prior to any recovery/synthesis. -/
def br2CausalTfvdPreRecoveryIncidenceState
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (base radius index : ℕ) : NativeGpreFiniteTfvdAnalysisCarrier S :=
  br2CausalTfvdPreRecoveryIncidenceMap q S
    (cameraBracketIncidence base radius index)

/-- The bracket coordinate of the retained enriched state is the literal BR2
bracket.  This is the exact point at which the causal response has restored
the source bracket, while trace and provenance are still present in the full
source state. -/
theorem br2CausalTfvdPreRecoveryIncidenceState_bracket_eq
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    nativeGpreFiniteTfvdAnalysisBracketProjection S
        (br2CausalTfvdPreRecoveryIncidenceState q S base radius index) =
      br2CameraBracketVerticalState base radius index := by
  unfold br2CausalTfvdPreRecoveryIncidenceState
    br2CausalTfvdPreRecoveryIncidenceMap
  change nativeGpreFiniteTfvdAnalysisBracketProjection S
      (nativeGpreFiniteTfvdAnalysis q S
        (br2CameraBracketCausalGreenResponseMap q
          (cameraBracketIncidence base radius index))) = _
  rw [br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence
    q hbase hradius]
  exact nativeGpreFiniteTfvdAnalysisBracketProjection_br2CausalGreenResponse
    q hqpos hq1 S hbase hradius index

/-! ## The available Parseval total dilation -/

/-- Feed only the restored bracket coordinate of the pre-recovery enriched
state into the existing canonical Parseval Green-frame analysis.  This is a
real-linear incidence transport and uses no TFVD recovery.  The other TFVD
coordinates remain available in `br2CausalTfvdPreRecoveryIncidenceState`, but
there is currently no typed finite-camera map which consumes all of them. -/
def br2CausalTfvdParsevalGreenFrameIncidenceMap
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalCompletedGreenFrameCarrier :=
  LinearMap.comp
    (canonicalCompletedGreenFrameParsevalAnalysis.toLinearMap.restrictScalars ℝ)
    (LinearMap.comp
      ((nativeGpreFiniteTfvdAnalysisBracketProjection S).toLinearMap.restrictScalars ℝ)
      (br2CausalTfvdPreRecoveryIncidenceMap q S))

/-- The total Parseval-dilated state attached to one BR2 incidence. -/
def br2CausalTfvdParsevalGreenFrameIncidenceState
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (base radius index : ℕ) : CanonicalCompletedGreenFrameCarrier :=
  br2CausalTfvdParsevalGreenFrameIncidenceMap q S
    (cameraBracketIncidence base radius index)

/-- The available Parseval state is precisely the canonical Parseval Green
frame image of the literal BR2 bracket. -/
theorem br2CausalTfvdParsevalGreenFrameIncidenceState_eq_bracket
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ℕ) :
    br2CausalTfvdParsevalGreenFrameIncidenceState q S base radius index =
      canonicalCompletedGreenFrameParsevalAnalysis
        (br2CameraBracketVerticalState base radius index) := by
  unfold br2CausalTfvdParsevalGreenFrameIncidenceState
    br2CausalTfvdParsevalGreenFrameIncidenceMap
  change canonicalCompletedGreenFrameParsevalAnalysis
      (nativeGpreFiniteTfvdAnalysisBracketProjection S
        (br2CausalTfvdPreRecoveryIncidenceState q S base radius index)) = _
  rw [br2CausalTfvdPreRecoveryIncidenceState_bracket_eq
    q hqpos hq1 S hbase hradius index]

/-- The total Gram of the available pre-recovery Parseval dilation is exactly
the BR2 Gram.  In particular, it preserves the literal C3 energy `6I` without
requiring any Hankel positivity or moment equation. -/
theorem br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (i j : ℕ) :
    inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S base radius i)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S base radius j) =
      inner ℂ (br2CameraBracketVerticalState base radius i)
        (br2CameraBracketVerticalState base radius j) := by
  rw [br2CausalTfvdParsevalGreenFrameIncidenceState_eq_bracket
      q hqpos hq1 S hbase hradius i,
    br2CausalTfvdParsevalGreenFrameIncidenceState_eq_bracket
      q hqpos hq1 S hbase hradius j,
    canonicalCompletedGreenFrameParsevalAnalysis_inner]

/-- The total pairing has a literal four-channel expansion: seed, residual,
depth-one Green, and bulk Green.  This is the pre-synthesis address of all
the energy in the currently available dilation. -/
theorem br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_channelSum
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (base radius i j : ℕ) :
    let ui := br2CausalTfvdParsevalGreenFrameIncidenceState q S base radius i
    let uj := br2CausalTfvdParsevalGreenFrameIncidenceState q S base radius j
    inner ℂ ui uj =
      inner ℂ ui.fst.fst.fst uj.fst.fst.fst +
        inner ℂ ui.fst.fst.snd uj.fst.fst.snd +
        inner ℂ ui.fst.snd uj.fst.snd +
        inner ℂ ui.snd uj.snd := by
  dsimp only
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rfl

/-- The total dilation has the required raw low-degree energies.  These are
the total-side tests for `(0,0)`, `(0,2)`, and `(1,1)` before any proposed
camera compression. -/
theorem br2CausalTfvdParsevalGreenFrameIncidenceState_lowDegree_total
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 0)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 0) = 6 ∧
      inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 0)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 2) = 0 ∧
      inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 1)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 1) = 6 := by
  have hbase : IsSupported 3 := by
    norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by
    norm_num [mem_radiusSet_iff]
  constructor
  · rw [br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
      q hqpos hq1 S hbase hradius]
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  constructor
  · rw [br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
      q hqpos hq1 S hbase hradius]
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  · rw [br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
      q hqpos hq1 S hbase hradius]
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num

/-! ## Exact no-go for using the whole dilation as a visible channel -/

/-- The coefficient defect obtained by incorrectly declaring the whole
pre-recovery Parseval dilation to be the visible channel.  It is retained as
an exact identity, not estimated. -/
def br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ)
    (i j : ℕ ⊕ ℕ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
      M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) -
    inner ℂ
      (br2CausalTfvdParsevalGreenFrameIncidenceState
        q S base radius (parityJetNumber i))
      (br2CausalTfvdParsevalGreenFrameIncidenceState
        q S base radius (parityJetNumber j))

/-- The total-side defect is exactly the already-known negative energy
excess.  Hence this is not a new candidate for `correctedMap`; it is the
correct isometric total prior to the still-missing visible compression. -/
theorem br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect_eq_neg_energyExcess
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) {base radius : ℕ}
    (hbase : IsSupported base) (hradius : radius ∈ radiusSet base)
    (i j : ℕ ⊕ ℕ) :
    br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect
        M q hqpos.le hq1 S base radius i j =
      - nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S base radius i j := by
  unfold br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
  rw [br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
    q hqpos hq1 S hbase hradius]
  cases i <;> cases j <;>
    simp [br2CameraBracketProjectiveHilbertParityJet, parityJetNumber]

/-- If the full total dilation is misread as visible, the first Hankel test
fails by six.  This leaves open only a genuine compression/projection from
the four-channel carrier, not an identification of its total inner product
with the six-source coefficient. -/
theorem br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect_firstHankel_eq_six
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect
        M q hqpos.le hq1 S 3 1 (Sum.inl 0) (Sum.inl 1) -
      br2CausalTfvdParsevalGreenFrameTotalCoefficientDefect
        M q hqpos.le hq1 S 3 1 (Sum.inr 0) (Sum.inr 0) = 6 := by
  have hbase : IsSupported 3 := by
    norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by
    norm_num [mem_radiusSet_iff]
  change
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S 0 2 -
      inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 0)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 2) -
      (nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S 1 1 -
      inner ℂ
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 1)
        (br2CausalTfvdParsevalGreenFrameIncidenceState q S 3 1 1)) = 6
  have hcoeff :=
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_lowDegree_hankel
      M q hqpos hq1 S
  rw [hcoeff]
  have hraw02 :=
    br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
      q hqpos hq1 S hbase hradius 0 2
  have hraw11 :=
    br2CausalTfvdParsevalGreenFrameIncidenceState_inner_eq_br2
      q hqpos hq1 S hbase hradius 1 1
  rw [hraw02, hraw11, br2C3CameraBracketVerticalState_inner,
    br2C3CameraBracketVerticalState_inner]
  norm_num

end

end CarrySelfAdjointOperator
