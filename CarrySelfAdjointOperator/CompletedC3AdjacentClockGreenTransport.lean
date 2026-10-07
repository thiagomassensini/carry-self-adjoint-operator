import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff

/-!
# Material-clock product rule in the actual adjacent-edge mixed ledger

The existing native log gradient is Delta(log * value). Its two product-rule
orientations retain the endpoints. At an adjacent pair they yield the log
of the shared material node times the ordinary wedge, plus two log-gap
returns. These channels are retained per leg before finite synthesis. The
existing Green port, ordered crosses and synthesis residual are unchanged.
No Hilbert positivity or completed limiting cancellation is inferred.
-/
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

/-- Delta(log * f) with the right endpoint multiplying Delta f. -/
theorem canonicalC3LogGradient_right_productRule (s : ℂ) (n : ℕ) :
    positiveLogDirichletGradient s n =
      positiveLogVertexWeight (n + 1) * positiveDirichletGradient s n +
        positiveLogGap n * positiveDirichletValue s n := by
  unfold positiveLogDirichletGradient positiveLogDirichletValue
    positiveLogVertexWeight positiveLogGap
  simp only [positiveDirichletGradient_eq_value_sub_value, Nat.add_assoc]
  ring

/-- The other exact product-rule orientation retains the upper endpoint. -/
theorem canonicalC3LogGradient_left_productRule (s : ℂ) (n : ℕ) :
    positiveLogDirichletGradient s n =
      positiveLogVertexWeight n * positiveDirichletGradient s n +
        positiveLogGap n * positiveDirichletValue s (n + 1) := by
  unfold positiveLogDirichletGradient positiveLogDirichletValue
    positiveLogVertexWeight positiveLogGap
  simp only [positiveDirichletGradient_eq_value_sub_value, Nat.add_assoc]
  ring

/-- Two source-derived channels at consecutive material edges n,n+1.
The frequency is log(n+2), the shared material node, not a vertical depth.
The second channel uses only literal log gaps and the two outer samples. -/
def canonicalC3AdjacentClockChannels (z w : ℂ) (n : ℕ) : ℂ × ℂ :=
  (positiveLogVertexWeight (n + 1) *
      (positiveDirichletGradient w (n + 1) * positiveDirichletGradient z n -
        positiveDirichletGradient w n * positiveDirichletGradient z (n + 1)),
    positiveLogGap n * positiveDirichletGradient w (n + 1) * positiveDirichletValue z n -
      positiveLogGap (n + 1) * positiveDirichletGradient w n * positiveDirichletValue z (n + 2))

/-- Exact bilinear orientation of the current mixed wedge, for independent z,w. -/
theorem canonicalC3AdjacentClockChannels_eq_mixedWedge (z w : ℂ) (n : ℕ) :
    sameSEdgeBoundaryWedge
        (positiveDirichletGradient w n) (positiveDirichletGradient w (n + 1))
        (positiveLogDirichletGradient z n) (positiveLogDirichletGradient z (n + 1)) =
      (canonicalC3AdjacentClockChannels z w n).1 + (canonicalC3AdjacentClockChannels z w n).2 := by
  unfold sameSEdgeBoundaryWedge canonicalC3AdjacentClockChannels
  rw [canonicalC3LogGradient_right_productRule z n,
    canonicalC3LogGradient_left_productRule z (n + 1)]
  simp only [Nat.add_assoc]
  ring

/-- Literal current C3 leg addressing: two adjacent pairs in each three-edge cell. -/
def canonicalC3AdjacentMaterialLegIndex {M : ℕ} (mr : Fin M × Fin 2) : ℕ :=
  3 * (mr.1 : ℕ) + (mr.2 : ℕ)

/-- No coordinate reinterpretation: these are exactly the current mixed legs. -/
theorem canonicalC3MixedLegWedge_at_materialIndex
    {M : ℕ} (x : CanonicalC3AllCutoffMixedSourceHilbert) (mr : Fin M × Fin 2) :
    let n := canonicalC3AdjacentMaterialLegIndex mr
    sameSEdgeBoundaryWedge
      ((x.mixedLegs M).left mr) ((x.mixedLegs M).right mr)
      ((x.mixedLegs M).jetLeft mr) ((x.mixedLegs M).jetRight mr) =
    sameSEdgeBoundaryWedge
      (x.wSource.1 n) (x.wSource.1 (n + 1)) (x.zSource.2 n) (x.zSource.2 (n + 1)) := by
  rcases mr with ⟨m, a⟩
  fin_cases a <;>
    simp only [canonicalC3AdjacentMaterialLegIndex,
      CanonicalC3AllCutoffMixedSourceHilbert.mixedLegs, Nat.add_zero, Nat.add_assoc] <;> rfl

/-- The two channels stay separated at every leg, before any sum. -/
def canonicalC3AdjacentClockChannelFamily (M : ℕ) (z w : ℂ) :
    Fin M × Fin 2 → ℂ × ℂ :=
  fun mr => canonicalC3AdjacentClockChannels z w (canonicalC3AdjacentMaterialLegIndex mr)

/-- The retained Hilbert prefixes realize those same local channels literally. -/
theorem canonicalC3MixedPrefixLeg_clockTransport
    (M : ℕ) (z w : ℂ) (mr : Fin M × Fin 2) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState M z w
    sameSEdgeBoundaryWedge
      ((x.mixedLegs M).left mr) ((x.mixedLegs M).right mr)
      ((x.mixedLegs M).jetLeft mr) ((x.mixedLegs M).jetRight mr) =
      (canonicalC3AdjacentClockChannelFamily M z w mr).1 +
        (canonicalC3AdjacentClockChannelFamily M z w mr).2 := by
  dsimp only
  rw [canonicalC3MixedLegWedge_at_materialIndex]
  have hm := mr.1.isLt
  have ha := mr.2.isLt
  have hn : canonicalC3AdjacentMaterialLegIndex mr < 3 * M := by
    unfold canonicalC3AdjacentMaterialLegIndex; omega
  have hn1 : canonicalC3AdjacentMaterialLegIndex mr + 1 < 3 * M := by
    unfold canonicalC3AdjacentMaterialLegIndex; omega
  simp only [canonicalC3AllCutoffMixedSourcePrefixState_wSource,
    canonicalC3AllCutoffMixedSourcePrefixState_zSource,
    canonicalCompletedC3HilbertPrefixState,
    canonicalCompletedC3DirichletGradientPrefixState_apply,
    canonicalCompletedC3LogJetPrefixState_apply, if_pos hn, if_pos hn1]
  exact canonicalC3AdjacentClockChannels_eq_mixedWedge z w _

/-- The actual Green provenance transports with both local clock channels.
No equality to the historical same-edge reflected form is asserted. -/
theorem canonicalC3MixedPrefixGreenProvenance_clockTransport (M : ℕ) (z w : ℂ) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState M z w
    x.greenProvenanceReadout M w (reflectedParameter z) =
      (∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).1) +
        (∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).2) -
      greenForm (CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) w x.wSource)
        (CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) (reflectedParameter z) x.reflectedZSource) := by
  dsimp only
  unfold CanonicalC3AllCutoffMixedSourceHilbert.greenProvenanceReadout
  simp_rw [canonicalC3MixedPrefixLeg_clockTransport]
  rw [Finset.sum_add_distrib]

/-- Complete finite head synthesis also retains the existing ordered crosses
and the four synthesis residuals. The I rotation stays at the final readout. -/
theorem canonicalC3MixedPrefixHead_clockTransport (M : ℕ) (z w : ℂ) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState M z w
    mixedScalarBoundaryWedge
      (CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M x.zSource)
      (Complex.I * CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M x.zSource)
      (CanonicalC3AllCutoffMixedSourceHilbert.valueHeadReadout M x.wSource)
      (Complex.I * CanonicalC3AllCutoffMixedSourceHilbert.logJetHeadReadout M x.wSource) =
      ((∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).1) +
        (∑ mr, (canonicalC3AdjacentClockChannelFamily M z w mr).2)) +
      x.offDiagonalReadout M + x.heightResidualReadout M := by
  dsimp only
  rw [mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    (legs := (canonicalC3AllCutoffMixedSourcePrefixState M z w).mixedLegs M)]
  simp_rw [canonicalC3MixedPrefixLeg_clockTransport]
  rw [Finset.sum_add_distrib]
  rfl

/-- Same-parameter ordinary wedge vanishes, leaving the geometric log-gap return. -/
theorem canonicalC3AdjacentClockChannels_sameParameter_first (s : ℂ) (n : ℕ) :
    (canonicalC3AdjacentClockChannels s s n).1 = 0 := by
  unfold canonicalC3AdjacentClockChannels
  dsimp only
  ring

/-- On the diagonal this is precisely log-gap return minus the unchanged Green port. -/
theorem canonicalC3MixedPrefixGreenProvenance_sameParameter (M : ℕ) (s : ℂ) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState M s s
    x.greenProvenanceReadout M s (reflectedParameter s) =
      (∑ mr, (canonicalC3AdjacentClockChannelFamily M s s mr).2) -
      greenForm (CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) s x.wSource)
        (CanonicalC3AllCutoffMixedSourceHilbert.greenPort (3 * M) (reflectedParameter s) x.reflectedZSource) := by
  dsimp only
  rw [canonicalC3MixedPrefixGreenProvenance_clockTransport]
  simp [canonicalC3AdjacentClockChannelFamily, canonicalC3AdjacentClockChannels_sameParameter_first]

/-- Source samples are finite affine reconstructions, including the global unit seed.
No raw nodal l2 state is created. -/
theorem canonicalC3Sample_eq_seed_add_gradientPrefix (s : ℂ) (n : ℕ) :
    positiveDirichletValue s n = 1 + ∑ j ∈ Finset.range n, positiveDirichletGradient s j := by
  induction n with
  | zero => simp [positiveDirichletValue]
  | succ n ih =>
    rw [Finset.sum_range_succ, positiveDirichletGradient_eq_value_sub_value]
    linear_combination ih

/-- Each finite reconstruction reads the very same completed ordinary prefix.
The endpoint n=3M is included, using all 3M preceding gradients. -/
theorem canonicalC3Sample_eq_seed_add_completedGradientPrefix
    (M : ℕ) (s : ℂ) {n : ℕ} (hn : n ≤ 3 * M) :
    positiveDirichletValue s n = 1 +
      ∑ j ∈ Finset.range n, canonicalCompletedC3DirichletGradientPrefixState s (3 * M) j := by
  rw [canonicalC3Sample_eq_seed_add_gradientPrefix]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [canonicalCompletedC3DirichletGradientPrefixState_apply, if_pos (by
    have := Finset.mem_range.mp hj; omega)]


/-- Both outer samples of every return are reconstructed from the same finite
ordinary prefix and its certified global seed. Even the last outer node
uses only the retained 3M gradients; no infinite nodal state is introduced. -/
theorem canonicalC3AdjacentClockReturn_eq_seededPrefix
    (M : ℕ) (z w : ℂ) (mr : Fin M × Fin 2) :
    let n := canonicalC3AdjacentMaterialLegIndex mr
    (canonicalC3AdjacentClockChannelFamily M z w mr).2 =
      positiveLogGap n * positiveDirichletGradient w (n + 1) *
          (1 + ∑ j ∈ Finset.range n, canonicalCompletedC3DirichletGradientPrefixState z (3 * M) j) -
        positiveLogGap (n + 1) * positiveDirichletGradient w n *
          (1 + ∑ j ∈ Finset.range (n + 2), canonicalCompletedC3DirichletGradientPrefixState z (3 * M) j) := by
  dsimp only
  have hm := mr.1.isLt
  have ha := mr.2.isLt
  have hn : canonicalC3AdjacentMaterialLegIndex mr ≤ 3 * M := by
    unfold canonicalC3AdjacentMaterialLegIndex; omega
  have hu : canonicalC3AdjacentMaterialLegIndex mr + 2 ≤ 3 * M := by
    unfold canonicalC3AdjacentMaterialLegIndex; omega
  rw [← canonicalC3Sample_eq_seed_add_completedGradientPrefix M z hn,
    ← canonicalC3Sample_eq_seed_add_completedGradientPrefix M z hu]
  rfl

end
end CarrySelfAdjointOperator
