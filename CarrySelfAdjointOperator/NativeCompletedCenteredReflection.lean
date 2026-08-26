import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import CarrySelfAdjointOperator.CompletedEnrichedTfvdBoundaryCompanion
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CarrySelfAdjointOperator.NativeScalarDirectSchwarzReflection
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyCollapse
import Mathlib.Tactic

/-!
# Centered reflection from the completed native channel

The direct native bracket series gives the antilinear identity

`F (-conj z) = conj (F z)`

for the completed characteristic: negated conjugation of centered height is
ordinary conjugation of the spectral parameter.  Composing this native
identity with the already proved centered parity `F (-z) = F z` yields the
centered Schwarz reflection `F (conj z) = conj (F z)` on the natural strip.

The two steps remain separate below, so the native conjugation channel is not
silently identified with centered parity.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Negated conjugation of centered height is ordinary conjugation of the
corresponding spectral parameter. -/
theorem operatorHeightParameter_neg_conj (z : ℂ) :
    operatorHeightParameter (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (operatorHeightParameter z) := by
  apply Complex.ext <;> simp [operatorHeightParameter]

/-- The native archimedean completion factor follows the same direct
conjugation channel. -/
theorem nativeXiCompletionFactor_neg_conj_from_nativeChannel (z : ℂ) :
    nativeXiCompletionFactor (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (nativeXiCompletionFactor z) := by
  unfold nativeXiCompletionFactor
  dsimp only
  rw [operatorHeightParameter_neg_conj]
  simp only [map_mul, map_sub, map_one, map_ofNat, map_div₀]
  rw [← Complex.exp_conj, ← Complex.Gamma_conj]
  congr 2 <;>
    simp only [map_neg, map_mul, map_div₀, map_ofNat,
      Complex.conj_ofReal]

/-- Direct antilinear reflection of the completed characteristic.  This step
uses only conjugation of the completion factor and the termwise native bracket
channel; centered parity is not used. -/
theorem completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel
    (z : ℂ) :
    completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  unfold completedNativeOperatorCharacteristic
  rw [nativeXiCompletionFactor_neg_conj_from_nativeChannel,
    operatorHeightParameter_neg_conj,
    nativeScalar_conj_from_nativeSeries]
  simp

/-- Conjugating centered height is reflection of the spectral parameter about
the critical center: `s ↦ 1 - conj s`. -/
theorem operatorHeightParameter_conj_eq_reflectedParameter (z : ℂ) :
    operatorHeightParameter ((starRingEnd ℂ) z) =
      reflectedParameter (operatorHeightParameter z) := by
  apply Complex.ext
  · simp [operatorHeightParameter, reflectedParameter]
    ring
  · simp [operatorHeightParameter, reflectedParameter]

/-- The reflected centered-height parameter remains in the natural strip. -/
theorem operatorHeightParameter_conj_mem_genuineCriticalStrip
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    operatorHeightParameter ((starRingEnd ℂ) z) ∈ genuineCriticalStrip := by
  rw [operatorHeightParameter_conj_eq_reflectedParameter]
  exact reflectedParameter_mem_genuineCriticalStrip hs

/-- The ordinary native value channel reconstructs the centered-reflected
Dirichlet vertex without passing through the completed scalar. -/
theorem sameEdgeReflectedVertex_operatorHeightParameter
    (z : ℂ) (n : ℕ) :
    sameEdgeReflectedVertex n
        (positiveDirichletValue (operatorHeightParameter z) n) =
      positiveDirichletValue
        (operatorHeightParameter ((starRingEnd ℂ) z)) n := by
  rw [sameEdgeReflectedVertex_canonical,
    operatorHeightParameter_conj_eq_reflectedParameter]

/-- The ordinary/log-jet native pair reconstructs the complete reflected
gradient at centered height `conj z`, before any scalar readout. -/
theorem sameEdgeRecoveredReflectedGradient_operatorHeightParameter
    (z : ℂ) (n : ℕ) :
    sameEdgeRecoveredReflectedGradient n
        (positiveDirichletGradient (operatorHeightParameter z) n)
        (positiveLogDirichletGradient (operatorHeightParameter z) n) =
      positiveDirichletGradient
        (operatorHeightParameter ((starRingEnd ℂ) z)) n := by
  rw [sameEdgeRecoveredReflectedGradient_canonical,
    operatorHeightParameter_conj_eq_reflectedParameter]

/-- The same native value/log-jet state reads the reflected Green edge energy
used by the TFVD collapse; no completed parity theorem is used. -/
theorem sameEdgeRecoveredReflectedEnergyEdge_operatorHeightParameter
    (z : ℂ) (n : ℕ) :
    sameEdgeRecoveredReflectedEnergyEdge n
        (positiveDirichletGradient (operatorHeightParameter z) n)
        (positiveLogDirichletGradient (operatorHeightParameter z) n) =
      (finiteReflectedGradientEdge n (operatorHeightParameter z)).re := by
  exact sameEdgeRecoveredReflectedEnergyEdge_canonical
    (operatorHeightParameter z) n

/-! ## Equivariance of the completed scalar readout -/

/-- One reflected C3 value block reconstructed edge by edge from the ordinary
and log-jet channels at `s`.  All three residues are retained. -/
def sameEdgeReconstructedReflectedEnrichedValueBlock
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode m kappa (omega m)
    (sameEdgeRecoveredReflectedGradient (3 * m)
      (positiveDirichletGradient s (3 * m))
      (positiveLogDirichletGradient s (3 * m)))
    (sameEdgeRecoveredReflectedGradient (3 * m + 1)
      (positiveDirichletGradient s (3 * m + 1))
      (positiveLogDirichletGradient s (3 * m + 1)))
    (sameEdgeRecoveredReflectedGradient (3 * m + 2)
      (positiveDirichletGradient s (3 * m + 2))
      (positiveLogDirichletGradient s (3 * m + 2)))

/-- The reconstructed three-channel block is literally the canonical value
block at the reflected parameter. -/
theorem sameEdgeReconstructedReflectedEnrichedValueBlock_eq_canonical
    (kappa : ℂ) (omega : ℕ → ℂ) (m : ℕ) (s : ℂ) :
    sameEdgeReconstructedReflectedEnrichedValueBlock kappa omega m s =
      canonicalEnrichedAngularTfvdCoordinate
        kappa omega m (reflectedParameter s) := by
  unfold sameEdgeReconstructedReflectedEnrichedValueBlock
    canonicalEnrichedAngularTfvdCoordinate
  rw [sameEdgeRecoveredReflectedGradient_canonical,
    sameEdgeRecoveredReflectedGradient_canonical,
    sameEdgeRecoveredReflectedGradient_canonical]

/-- All-order reflected value port reconstructed from the ordinary/log-jet
state at `s`.  The seed is reconstructed by the same endpoint map. -/
def sameEdgeReconstructedReflectedValuePort
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    SeededEnrichedTfvdPort :=
  {
    seed := sameEdgeReflectedVertex 0 (positiveDirichletValue s 0)
    blocks := fun m ↦
      sameEdgeReconstructedReflectedEnrichedValueBlock kappa omega m s
  }

/-- The all-order reconstructed port equals the canonical reflected port as a
typed state, before any scalar synthesis. -/
theorem sameEdgeReconstructedReflectedValuePort_eq_canonical
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    sameEdgeReconstructedReflectedValuePort kappa omega s =
      canonicalSeededEnrichedTfvdGenuinePort
        kappa omega (reflectedParameter s) := by
  unfold sameEdgeReconstructedReflectedValuePort
    canonicalSeededEnrichedTfvdGenuinePort
  congr
  · calc
      sameEdgeReflectedVertex 0 (positiveDirichletValue s 0) =
          positiveDirichletValue (reflectedParameter s) 0 :=
        sameEdgeReflectedVertex_canonical s 0
      _ = 1 := by simp [positiveDirichletValue]
  · funext m
    exact sameEdgeReconstructedReflectedEnrichedValueBlock_eq_canonical
      kappa omega m s

/-- The unresolved reflected tail is read from the reconstructed all-order
blocks themselves.  No precomputed reflected scalar tail is inserted. -/
def sameEdgeReconstructedReflectedBracketCutoffTail
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' k : ℕ,
    enrichedTfvdGenuineBracketReadout kappa (omega (k + M))
      (sameEdgeReconstructedReflectedEnrichedValueBlock
        kappa omega (k + M) s)

/-- Termwise reconstruction commutes with the infinite cutoff tail. -/
theorem sameEdgeReconstructedReflectedBracketCutoffTail_eq_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    sameEdgeReconstructedReflectedBracketCutoffTail M kappa omega s =
      realCpBracketCutoffTail 3 M (reflectedParameter s) := by
  unfold sameEdgeReconstructedReflectedBracketCutoffTail
    realCpBracketCutoffTail
  apply tsum_congr
  intro k
  rw [sameEdgeReconstructedReflectedEnrichedValueBlock_eq_canonical]
  exact enrichedTfvdGenuineBracketReadout_canonical
    hkappa omega (k + M) (homega (k + M)) (reflectedParameter s)

/-- In the Genuine strip the reconstructed reflected tail is absolutely
summable.  Hence its `tsum` is the convergent completion, not the default
value of a nonsummable series. -/
theorem summable_norm_sameEdgeReconstructedReflectedBracketCutoffTail
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun k : ℕ ↦
      ‖enrichedTfvdGenuineBracketReadout kappa (omega (k + M))
        (sameEdgeReconstructedReflectedEnrichedValueBlock
          kappa omega (k + M) s)‖) := by
  have hreflected : -1 < (reflectedParameter s).re := by
    rw [reflectedParameter_re]
    linarith [hs.2]
  have hsum := summable_norm_realCpSaturatedBracket
    3 (by norm_num) hreflected
  have hsumTail : Summable (fun k : ℕ ↦
      ‖realCpSaturatedBracket 3 (k + M) (reflectedParameter s)‖) := by
    simpa [Function.comp_def] using hsum.comp_injective
      (show Function.Injective (fun k : ℕ ↦ k + M) by
        intro a b hab
        exact Nat.add_right_cancel hab)
  apply hsumTail.congr
  intro k
  congr 1
  rw [sameEdgeReconstructedReflectedEnrichedValueBlock_eq_canonical]
  exact (enrichedTfvdGenuineBracketReadout_canonical
    hkappa omega (k + M) (homega (k + M)) (reflectedParameter s)).symm

/-- Prefix and tail are both synthesized from the reconstructed reflected
state.  This is the unnormalized scalar readout before the archimedean
completion factor is applied. -/
def sameEdgeReconstructedReflectedTfvdTailReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  finiteSeededEnrichedTfvdGenuineReadout M kappa omega
      (sameEdgeReconstructedReflectedValuePort kappa omega s) +
    sameEdgeReconstructedReflectedBracketCutoffTail M kappa omega s

/-- The scalar readout of the reconstructed state is exactly the existing
canonical tail-completed readout at the reflected parameter. -/
theorem sameEdgeReconstructedReflectedTfvdTailReadout_eq_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    sameEdgeReconstructedReflectedTfvdTailReadout M kappa omega s =
      NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout
        M kappa omega (reflectedParameter s) := by
  unfold sameEdgeReconstructedReflectedTfvdTailReadout
  rw [sameEdgeReconstructedReflectedValuePort_eq_canonical,
    sameEdgeReconstructedReflectedBracketCutoffTail_eq_canonical
      M hkappa omega homega s]
  rfl

/-- Before normalization and archimedean completion, the reconstructed scalar
readout is exactly the convergent native bracket chart at the reflected
parameter. -/
theorem sameEdgeReconstructedReflectedTfvdTailReadout_eq_reflectedChart
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedTfvdTailReadout M kappa omega s =
      bracketedDirichletChart 3 (reflectedParameter s) := by
  rw [sameEdgeReconstructedReflectedTfvdTailReadout_eq_canonical
    M hkappa omega homega s]
  apply
    NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      M hkappa omega homega
  rw [reflectedParameter_re]
  linarith [hs.2]

/-- Canonical completed scalar synthesis of the reflected state reconstructed
at centered height `z`. -/
def sameEdgeReconstructedReflectedCompletedScalarReadout (z : ℂ) : ℂ :=
  nativeXiCompletionFactor ((starRingEnd ℂ) z) *
    (sameEdgeReconstructedReflectedTfvdTailReadout
        1 tfvdHaarScale (fun _ : ℕ ↦ (1 : ℂ))
        (operatorHeightParameter z) /
      cpChartFactor 3
        (operatorHeightParameter ((starRingEnd ℂ) z)))

/-- The completed scalar readout commutes with the reconstructed centered
reflection.  This identity uses only the typed state reconstruction and the
same canonical readout on both sides. -/
theorem sameEdgeReconstructedReflectedCompletedScalarReadout_eq_canonical
    (z : ℂ) :
    sameEdgeReconstructedReflectedCompletedScalarReadout z =
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
        ((starRingEnd ℂ) z) := by
  unfold sameEdgeReconstructedReflectedCompletedScalarReadout
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    canonicalCompletedC3EnrichedTfvdValueTailReadout
  rw [sameEdgeReconstructedReflectedTfvdTailReadout_eq_canonical
    1 tfvdHaarScale_ne_zero (fun _ : ℕ ↦ (1 : ℂ))
      (by intro m; norm_num) (operatorHeightParameter z),
    operatorHeightParameter_conj_eq_reflectedParameter]

/-- On the natural strip, equivariance lands in the concrete completed native
operator characteristic.  No centered parity or scalar zero is used. -/
theorem sameEdgeReconstructedReflectedCompletedScalarReadout_eq_characteristic
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedScalarReadout z =
      completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) := by
  rw [sameEdgeReconstructedReflectedCompletedScalarReadout_eq_canonical]
  exact
    canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
      (operatorHeightParameter_conj_mem_genuineCriticalStrip hs)

/-- Completed reflected trace pair.  Its value coordinate is reconstructed
edge by edge, while its companion is retained from the same canonical
tail-completed bracket--TFVD carrier. -/
def sameEdgeReconstructedReflectedCompletedTracePair (z : ℂ) : ℂ × ℂ :=
  (sameEdgeReconstructedReflectedCompletedScalarReadout z,
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion
      ((starRingEnd ℂ) z))

/-- The reconstructed value and the retained companion are exactly the
existing canonical completed trace pair at the reflected centered height. -/
theorem sameEdgeReconstructedReflectedCompletedTracePair_eq_canonical
    (z : ℂ) :
    sameEdgeReconstructedReflectedCompletedTracePair z =
      canonicalCompletedC3TracePair ((starRingEnd ℂ) z) := by
  unfold sameEdgeReconstructedReflectedCompletedTracePair
    canonicalCompletedC3TracePair
  apply Prod.ext
  · exact sameEdgeReconstructedReflectedCompletedScalarReadout_eq_canonical z
  · rfl

/-- The same pair is the completed projection of the already constructed
bracket--TFVD state, not a second scalar presentation. -/
theorem sameEdgeReconstructedReflectedCompletedTracePair_eq_bracketTfvd
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedTracePair z =
      canonicalC3BracketTfvdCompletedTracePair
        1 ((starRingEnd ℂ) z) := by
  rw [sameEdgeReconstructedReflectedCompletedTracePair_eq_canonical,
    canonicalC3BracketTfvdCompletedTracePair_eq_completed
      1 (operatorHeightParameter_conj_mem_genuineCriticalStrip hs)]

/-- On the natural strip, the reflected completed trace pair is literally
`(F(conj z), -F'(conj z))`.  No centered parity theorem is used. -/
theorem sameEdgeReconstructedReflectedCompletedTracePair_eq_F_negFprime
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedTracePair z =
      (completedNativeOperatorCharacteristic ((starRingEnd ℂ) z),
        -deriv completedNativeOperatorCharacteristic
          ((starRingEnd ℂ) z)) := by
  rw [sameEdgeReconstructedReflectedCompletedTracePair_eq_canonical]
  exact canonicalCompletedC3TracePair_eq_F_negFprime
    (operatorHeightParameter_conj_mem_genuineCriticalStrip hs)

/-- Exact failure of the reconstructed completed readout to commute with
conjugation.  This is a concrete value, not an additional hypothesis. -/
def sameEdgeReconstructedReflectedCompletedScalarReadoutDefect
    (z : ℂ) : ℂ :=
  sameEdgeReconstructedReflectedCompletedScalarReadout z -
    (starRingEnd ℂ) (completedNativeOperatorCharacteristic z)

/-- On the natural strip, the structural readout defect is the difference
between the two completed centered reflections. -/
theorem
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_characteristic_sub_conj
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect z =
      completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) -
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  unfold sameEdgeReconstructedReflectedCompletedScalarReadoutDefect
  rw [sameEdgeReconstructedReflectedCompletedScalarReadout_eq_characteristic hs]

/-- The direct native conjugation channel rewrites the same concrete defect as
centered parity at `conj z`.  No centered parity theorem is used here. -/
theorem
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_centeredParityDefect
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect z =
      completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) -
        completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z) := by
  rw [
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_characteristic_sub_conj
      hs,
    completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel]

/-- Fully native normal form of the remaining completed transport.  It keeps
both completion factors and both native scalar channels explicit. -/
theorem
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_nativeCompletionDifference
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect z =
      nativeXiCompletionFactor ((starRingEnd ℂ) z) *
          NativeCarrySpectralWeyl.Camera.nativeScalar
            (operatorHeightParameter ((starRingEnd ℂ) z)) -
        nativeXiCompletionFactor (-(starRingEnd ℂ) z) *
          NativeCarrySpectralWeyl.Camera.nativeScalar
            (operatorHeightParameter (-(starRingEnd ℂ) z)) := by
  rw [
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_centeredParityDefect
      hs]
  rfl

/-- Vanishing of the concrete defect is exactly equivariance of the completed
scalar readout. -/
theorem
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect_eq_zero_iff :
    sameEdgeReconstructedReflectedCompletedScalarReadoutDefect z = 0 ↔
      sameEdgeReconstructedReflectedCompletedScalarReadout z =
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  unfold sameEdgeReconstructedReflectedCompletedScalarReadoutDefect
  exact sub_eq_zero

/-- After reconstruction and direct native conjugation, completed readout
equivariance is exactly centered parity at `conj z`. -/
theorem
    sameEdgeReconstructedReflectedCompletedScalarReadout_eq_conj_iff_centeredParityAtConj
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (sameEdgeReconstructedReflectedCompletedScalarReadout z =
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic z)) ↔
      (completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) =
        completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z)) := by
  rw [sameEdgeReconstructedReflectedCompletedScalarReadout_eq_characteristic hs,
    completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel]

/-- The reconstructed completed readout is equivariant at the centered
basepoint using only the direct native conjugation channel. -/
theorem sameEdgeReconstructedReflectedCompletedScalarReadout_zero :
    sameEdgeReconstructedReflectedCompletedScalarReadout 0 =
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) := by
  have hs : operatorHeightParameter (0 : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter, genuineCriticalStrip]
  rw [
    sameEdgeReconstructedReflectedCompletedScalarReadout_eq_conj_iff_centeredParityAtConj
      hs]
  simp

/-- After the direct native conjugation identity, centered Schwarz reflection
at `z` is exactly centered parity at `conj z`.  This equivalence isolates the
two logically distinct ingredients. -/
theorem completedNativeOperatorCharacteristic_centeredReflection_iff_evenAtConj
    (z : ℂ) :
    (completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic z)) ↔
      (completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z) =
        completedNativeOperatorCharacteristic ((starRingEnd ℂ) z)) := by
  rw [completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel]
  exact eq_comm

/-- Centered Schwarz reflection of the completed native characteristic.

The antilinear leg is the direct native channel above.  Centered parity is
then applied at `conj z`; no scalar channel is collapsed or cancelled. -/
theorem completedNativeOperatorCharacteristic_centeredReflection_via_nativeConjugation
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  have hsConj :
      operatorHeightParameter ((starRingEnd ℂ) z) ∈ genuineCriticalStrip :=
    operatorHeightParameter_conj_mem_genuineCriticalStrip hs
  have heven := completedNativeOperatorCharacteristic_neg
    (z := (starRingEnd ℂ) z) hsConj
  exact
    (completedNativeOperatorCharacteristic_centeredReflection_iff_evenAtConj z).2
      heven

end

end CarrySelfAdjointOperator
