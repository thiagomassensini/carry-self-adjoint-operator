import CarrySelfAdjointOperator.CompletedNativeCausalCoefficientMomentGate
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import Mathlib.Tactic

/-!
# Raw all-order TFVD jets in the completed Naimark carrier

The completed TFVD/Green intertwining already gives vector convergence for
every cutoff, finite-difference step, and parity order.  This file removes the
parity packaging and records the same statement for the raw derivative order
`order : ℕ`.  The raw family lives in one fixed Naimark carrier and retains
both Green-port quadratures, including the boundary return.

This is the indexing needed by `HasPolarizedCoefficientVectorEquation`: even
and odd families are obtained only after the raw all-order vector has been
constructed.
-/

open scoped Topology lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open Filter
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
attribute [local instance 10000] Complex.instNormedAddCommGroup

local instance rawAllOrderNaimarkComplexInnerProductSpace :
    InnerProductSpace ℂ RealifiedNaimarkComplexification :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal

/-- Raw order-`order` forward-difference vector of a cutoff TFVD state.  No
parity projection is made here. -/
def canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet
    (M k order : ℕ) : RealifiedNaimarkComplexification :=
  completedGreenForwardDifferenceJet
    (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState M)
    (canonicalGreenJetStep k) order

/-- Raw order-`order` forward-difference vector of the completed TFVD state
in the same global Naimark carrier. -/
def canonicalCompletedTfvdGreenNaimarkRawJet
    (k order : ℕ) : RealifiedNaimarkComplexification :=
  completedGreenForwardDifferenceJet
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
    (canonicalGreenJetStep k) order

/-- At every fixed finite-difference step and raw order, cutoff completion is
vector convergence in the global Naimark carrier. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet_tendsto
    (k order : ℕ) :
    Tendsto
      (fun M : ℕ =>
        canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet M k order)
      atTop
      (nhds (canonicalCompletedTfvdGreenNaimarkRawJet k order)) := by
  unfold canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet
    canonicalCompletedTfvdGreenNaimarkRawJet
    completedGreenForwardDifferenceJet
  exact (completedGreenForwardDifference_iter_tendsto_of_pointwise
    atTop
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState
    canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState_tendsto
    (canonicalGreenJetStep k) order 0).const_smul
      (((Nat.factorial order : ℂ) *
        canonicalGreenJetStep k ^ order)⁻¹)

/-- The whole raw order family converges in the product topology.  This is a
single all-order statement, not a separate parity assertion. -/
theorem canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet_tendsto_pi
    (k : ℕ) :
    Tendsto
      (fun M : ℕ =>
        fun order : ℕ =>
          canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet M k order)
      atTop
      (nhds (canonicalCompletedTfvdGreenNaimarkRawJet k)) := by
  rw [tendsto_pi_nhds]
  intro order
  exact canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet_tendsto k order

/-- Parity packaging after construction of the cutoff raw jet recovers
definitionally the previously formalized all-order parity jet. -/
theorem polarizedCoefficientParityJet_allCutoffNaimarkRawJet
    (M k : ℕ) :
    polarizedCoefficientParityJet
        (canonicalCompletedTfvdGreenAllCutoffNaimarkRawJet M k) =
      completedGreenForwardDifferenceParityJet
        (canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisPrefixState M) k := by
  funext i
  cases i <;> rfl

/-- The same raw-to-parity identification holds after cutoff completion. -/
theorem polarizedCoefficientParityJet_completedNaimarkRawJet
    (k : ℕ) :
    polarizedCoefficientParityJet
        (canonicalCompletedTfvdGreenNaimarkRawJet k) =
      completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState k := by
  funext i
  cases i <;> rfl

/-- A candidate coefficient vector is an all-order limit of the actual TFVD
vectors when every raw forward-difference order converges to it. -/
def IsCanonicalCompletedTfvdGreenRawJetLimit
    (rawJet : ℕ → RealifiedNaimarkComplexification) : Prop :=
  ∀ order : ℕ,
    Tendsto
      (fun k : ℕ => canonicalCompletedTfvdGreenNaimarkRawJet k order)
      atTop (nhds (rawJet order))

/-- The raw all-order limit, if it exists, is unique. -/
theorem IsCanonicalCompletedTfvdGreenRawJetLimit.unique
    {rawJet₁ rawJet₂ : ℕ → RealifiedNaimarkComplexification}
    (h₁ : IsCanonicalCompletedTfvdGreenRawJetLimit rawJet₁)
    (h₂ : IsCanonicalCompletedTfvdGreenRawJetLimit rawJet₂) :
    rawJet₁ = rawJet₂ := by
  funext order
  exact tendsto_nhds_unique (h₁ order) (h₂ order)

/-- Raw all-order convergence transports to the established parity package
without changing the derivative order. -/
theorem IsCanonicalCompletedTfvdGreenRawJetLimit.parity_tendsto
    {rawJet : ℕ → RealifiedNaimarkComplexification}
    (hraw : IsCanonicalCompletedTfvdGreenRawJetLimit rawJet)
    (i : ℕ ⊕ ℕ) :
    Tendsto
      (fun k : ℕ => completedGreenForwardDifferenceParityJet
        canonicalCompletedTfvdGreenAllCutoffNaimarkRealAxisState k i)
      atTop
      (nhds (polarizedCoefficientParityJet rawJet i)) := by
  cases i with
  | inl order => exact hraw (2 * order)
  | inr order => exact hraw (2 * order + 1)

/-! ## Finite raw Taylor square -/

/-- Raw coefficient jet before source, response, or boundary transport. -/
def canonicalCompletedC3DirichletGradientCoefficientRawJet
    (base cutoff k order : ℕ) :
    Fin (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) → ℂ :=
  completedGreenForwardDifferenceJet
    (canonicalCompletedC3DirichletGradientCoefficientRealAxisState base cutoff)
    (canonicalGreenJetStep k) order

/-- Exact Taylor coefficient vector exposed by one finite camera window. -/
def canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
    (base cutoff order : ℕ) :
    Fin (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) → ℂ :=
  fun i => nativeDirichletSlopeTaylorCoefficient order i.val

/-- Every raw finite coefficient vector converges in its finite-dimensional
norm to the exact logarithmic-orbit Taylor coefficient vector. -/
theorem canonicalCompletedC3DirichletGradientCoefficientRawJet_tendsto
    (base cutoff order : ℕ) :
    Tendsto
      (fun k : ℕ => canonicalCompletedC3DirichletGradientCoefficientRawJet
        base cutoff k order)
      atTop
      (nhds (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
        base cutoff order)) := by
  rw [tendsto_pi_nhds]
  intro i
  have hleft := completedGreenForwardDifferenceJet_natDirichletTerm_tendsto
    (m := i.val + 2) (by omega) order
  have hright := completedGreenForwardDifferenceJet_natDirichletTerm_tendsto
    (m := i.val + 1) (by omega) order
  have hsub := hleft.sub hright
  simpa [canonicalCompletedC3DirichletGradientCoefficientRawJet,
    canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix,
    canonicalCompletedC3DirichletGradientCoefficientRealAxisState,
    canonicalCompletedC3DirichletGradientSlopeCoefficients,
    positiveDirichletGradient, nativeDirichletSlopeTaylorCoefficient] using
      hsub.congr' (by
        filter_upwards with k
        rw [completedGreenForwardDifferenceJet_apply]
        exact (completedGreenForwardDifferenceJet_sub
          (fun z => natDirichletTerm
            (operatorHeightParameter z) (i.val + 2))
          (fun z => natDirichletTerm
            (operatorHeightParameter z) (i.val + 1))
          (canonicalGreenJetStep k) order).symm)

/-- The raw TFVD prefix jet is exactly the finite synthesis of its raw
coefficient vector. -/
theorem canonicalCompletedC3DirichletGradientPrefix_rawJet_eq_synthesis
    (base cutoff k order : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    completedGreenForwardDifferenceJet
        (fun z => canonicalCompletedC3DirichletGradientPrefixState
          (operatorHeightParameter z) N)
        (canonicalGreenJetStep k) order =
      finiteSlopeCoefficientSynthesisLinearMap N
        (canonicalCompletedC3DirichletGradientCoefficientRawJet
          base cutoff k order) := by
  dsimp only
  have hstate :
      (fun z => canonicalCompletedC3DirichletGradientPrefixState
        (operatorHeightParameter z)
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) =
      fun z => finiteSlopeCoefficientSynthesisLinearMap
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
        (canonicalCompletedC3DirichletGradientCoefficientRealAxisState
          base cutoff z) := by
    funext z
    exact (finiteSlopeCoefficientState_canonicalDirichletGradientCoefficients
      base cutoff (operatorHeightParameter z)).symm
  rw [hstate]
  exact completedGreenForwardDifferenceJet_linearMap
    (finiteSlopeCoefficientSynthesisLinearMap
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1))
    (canonicalCompletedC3DirichletGradientCoefficientRealAxisState base cutoff)
    (canonicalGreenJetStep k) order

/-- The causal response and boundary-return channels remain separate and
recombine exactly into the raw TFVD jet at every order. -/
theorem canonicalCompletedC3DirichletGradient_response_add_boundary_rawJet
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff k order : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    completedGreenForwardDifferenceJet
        (fun z => canonicalCompletedC3DirichletGradientBracketGreenResponse
          base cutoff (operatorHeightParameter z))
        (canonicalGreenJetStep k) order +
      finiteWeightedSlopeBoundaryReturnLinearMap
          (canonicalBR2CarryAmplitudeRatio base)
          (canonicalBR2CarryAmplitudeRatio_pos hbase).le
          (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
        (canonicalCompletedC3DirichletGradientCoefficientRawJet
          base cutoff k order) =
      completedGreenForwardDifferenceJet
        (fun z => canonicalCompletedC3DirichletGradientPrefixState
          (operatorHeightParameter z) N)
        (canonicalGreenJetStep k) order := by
  dsimp only
  have hresponse :
      completedGreenForwardDifferenceJet
          (fun z => canonicalCompletedC3DirichletGradientBracketGreenResponse
            base cutoff (operatorHeightParameter z))
          (canonicalGreenJetStep k) order =
        finiteWeightedSlopeGreenResponseLinearMap
            (canonicalBR2CarryAmplitudeRatio base)
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
          (canonicalCompletedC3DirichletGradientCoefficientRawJet
            base cutoff k order) := by
    have hstate :
        (fun z => canonicalCompletedC3DirichletGradientBracketGreenResponse
          base cutoff (operatorHeightParameter z)) =
        fun z => finiteWeightedSlopeGreenResponseLinearMap
            (canonicalBR2CarryAmplitudeRatio base)
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
          (canonicalCompletedC3DirichletGradientCoefficientRealAxisState
            base cutoff z) := by
      funext z
      exact
        canonicalCompletedC3DirichletGradientBracketGreenResponse_eq_responseLinearMap
          base cutoff (operatorHeightParameter z)
    rw [hstate]
    exact completedGreenForwardDifferenceJet_linearMap
      (finiteWeightedSlopeGreenResponseLinearMap
        (canonicalBR2CarryAmplitudeRatio base)
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1))
      (canonicalCompletedC3DirichletGradientCoefficientRealAxisState base cutoff)
      (canonicalGreenJetStep k) order
  rw [hresponse,
    canonicalCompletedC3DirichletGradientPrefix_rawJet_eq_synthesis]
  exact finiteWeightedSlopeGreenResponse_add_boundaryReturn
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
    (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
    (canonicalCompletedC3DirichletGradientCoefficientRawJet
      base cutoff k order)

/-- After the finite-difference step tends to zero, the complete finite TFVD
jet converges to the synthesis of the exact Taylor coefficient prefix. -/
theorem canonicalCompletedC3DirichletGradientPrefix_rawJet_tendsto_taylor
    (base cutoff order : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    Tendsto
      (fun k : ℕ => completedGreenForwardDifferenceJet
        (fun z => canonicalCompletedC3DirichletGradientPrefixState
          (operatorHeightParameter z) N)
        (canonicalGreenJetStep k) order)
      atTop
      (nhds (finiteSlopeCoefficientSynthesisLinearMap N
        (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
          base cutoff order))) := by
  dsimp only
  have hcoeff :=
    canonicalCompletedC3DirichletGradientCoefficientRawJet_tendsto
      base cutoff order
  have hmap :=
    (LinearMap.continuous_of_finiteDimensional
      (finiteSlopeCoefficientSynthesisLinearMap
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)))
      |>.continuousAt.tendsto.comp hcoeff
  apply hmap.congr'
  filter_upwards with k
  exact (canonicalCompletedC3DirichletGradientPrefix_rawJet_eq_synthesis
    base cutoff k order).symm

/-! ## The first two completed Taylor vectors -/

@[simp] theorem nativeDirichletSlopeTaylorCoefficient_zero
    (n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient 0 n =
      positiveDirichletGradient (1 / 2 : ℂ) n := by
  simp [nativeDirichletSlopeTaylorCoefficient,
    nativeCriticalDirichletAmplitude, positiveDirichletGradient]

@[simp] theorem nativeDirichletSlopeTaylorCoefficient_one
    (n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient 1 n =
      -Complex.I * positiveLogDirichletGradient (1 / 2 : ℂ) n := by
  simp [nativeDirichletSlopeTaylorCoefficient,
    nativeCriticalDirichletAmplitude, positiveLogDirichletGradient,
    positiveLogDirichletValue, positiveDirichletValue_eq_natDirichletTerm]
  ring_nf

/-- The zeroth finite Taylor synthesis is exactly the ordinary completed C3
prefix at the centered point. -/
theorem canonicalCompletedC3DirichletGradientTaylorPrefix_zero_eq
    (base cutoff : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    finiteSlopeCoefficientSynthesisLinearMap N
        (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
          base cutoff 0) =
      canonicalCompletedC3DirichletGradientPrefixState (1 / 2 : ℂ) N := by
  dsimp only
  ext n
  by_cases hn : n <
      NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  · rw [finiteSlopeCoefficientSynthesisLinearMap_apply,
      finiteSlopeCoefficientState_apply_of_lt _ hn,
      canonicalCompletedC3DirichletGradientPrefixState_apply,
      if_pos hn]
    exact nativeDirichletSlopeTaylorCoefficient_zero n
  · rw [finiteSlopeCoefficientSynthesisLinearMap_apply,
      finiteSlopeCoefficientState_apply_of_le _ (Nat.le_of_not_gt hn),
      canonicalCompletedC3DirichletGradientPrefixState_apply,
      if_neg hn]

/-- The first finite Taylor synthesis is the quarter-turned logarithmic
companion prefix, with its derivative factor `-I` derived from the native
orbit. -/
theorem canonicalCompletedC3DirichletGradientTaylorPrefix_one_eq
    (base cutoff : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    finiteSlopeCoefficientSynthesisLinearMap N
        (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
          base cutoff 1) =
      (-Complex.I) • canonicalCompletedC3LogJetPrefixState (1 / 2 : ℂ) N := by
  dsimp only
  ext n
  simp only [lp.coeFn_smul, Pi.smul_apply]
  by_cases hn : n <
      NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  · rw [finiteSlopeCoefficientSynthesisLinearMap_apply,
      finiteSlopeCoefficientState_apply_of_lt _ hn,
      canonicalCompletedC3LogJetPrefixState_apply, if_pos hn]
    change nativeDirichletSlopeTaylorCoefficient 1 n =
      -Complex.I * positiveLogDirichletGradient (1 / 2 : ℂ) n
    exact nativeDirichletSlopeTaylorCoefficient_one n
  · rw [finiteSlopeCoefficientSynthesisLinearMap_apply,
      finiteSlopeCoefficientState_apply_of_le _ (Nat.le_of_not_gt hn),
      canonicalCompletedC3LogJetPrefixState_apply, if_neg hn]
    simp

/-- Cutoff completion of the zeroth raw Taylor vector is already the
ordinary completed TFVD state. -/
theorem canonicalCompletedC3DirichletGradientTaylorPrefix_zero_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    Tendsto
      (fun cutoff : ℕ =>
        let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
        finiteSlopeCoefficientSynthesisLinearMap N
          (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
            base cutoff 0))
      atTop
      (nhds (canonicalCompletedC3DirichletGradientState
        (1 / 2 : ℂ) (by norm_num))) := by
  have hprefix :=
    (canonicalCompletedC3DirichletGradientPrefixState_tendsto
      (s := (1 / 2 : ℂ)) (by norm_num)).comp
        (finiteCameraWindow_add_one_tendsto_atTop hbase)
  apply hprefix.congr'
  filter_upwards with cutoff
  exact (canonicalCompletedC3DirichletGradientTaylorPrefix_zero_eq
    base cutoff).symm

/-- Cutoff completion of the first raw Taylor vector is the retained
log-jet state with its exact quarter-turn. -/
theorem canonicalCompletedC3DirichletGradientTaylorPrefix_one_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    Tendsto
      (fun cutoff : ℕ =>
        let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
        finiteSlopeCoefficientSynthesisLinearMap N
          (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
            base cutoff 1))
      atTop
      (nhds ((-Complex.I) • canonicalCompletedC3LogJetState
        (1 / 2 : ℂ) (by norm_num))) := by
  have hprefix :=
    ((canonicalCompletedC3LogJetPrefixState_tendsto
      (s := (1 / 2 : ℂ)) (by norm_num)).const_smul (-Complex.I)).comp
        (finiteCameraWindow_add_one_tendsto_atTop hbase)
  apply hprefix.congr'
  filter_upwards with cutoff
  exact (canonicalCompletedC3DirichletGradientTaylorPrefix_one_eq
    base cutoff).symm

end

end CarrySelfAdjointOperator
