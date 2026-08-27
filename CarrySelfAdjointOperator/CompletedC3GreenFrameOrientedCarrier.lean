import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedC3AllCutoffHilbertState
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining
import Mathlib.Tactic

/-!
# Oriented completed C3/TFVD carrier in the concrete Green frame

The completed TFVD ledger already contains literal ordinary and logarithmic
vertical states. This file sends that ordered pair through the faithful
all-bases Green analysis and retains the precompression residual as a third
channel. The construction is oriented at source level: no Gram
factorization, phase choice, scalar readout, or zero condition is used.

The cutoff states converge in the resulting carrier. Thus the concrete
C3/TFVD completion fixes the vector orientation before any comparison with
the normalized completed-native `dslope` jet.
-/

open scoped Topology lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarryC3Crosswalk

noncomputable section

/-! ## Faithful pair intertwiner -/

/-- Apply the concrete all-bases Green analysis separately to the ordinary
and logarithmic completed TFVD channels. -/
def canonicalCompletedC3GreenFramePairIntertwiner :
    CanonicalCompletedC3HilbertState →L[ℂ]
      (CanonicalCompletedGreenFrameCarrier ×
        CanonicalCompletedGreenFrameCarrier) :=
  canonicalCompletedGreenFrameAnalysisCLM.prodMap
    canonicalCompletedGreenFrameAnalysisCLM

@[simp] theorem canonicalCompletedC3GreenFramePairIntertwiner_apply
    (state : CanonicalCompletedC3HilbertState) :
    canonicalCompletedC3GreenFramePairIntertwiner state =
      (canonicalCompletedGreenFrameAnalysisCLM state.1,
        canonicalCompletedGreenFrameAnalysisCLM state.2) :=
  rfl

/-- The pair intertwiner loses neither the ordinary channel nor the
logarithmic channel. -/
theorem canonicalCompletedC3GreenFramePairIntertwiner_injective :
    Function.Injective canonicalCompletedC3GreenFramePairIntertwiner :=
  canonicalCompletedGreenFrameAnalysisCLM_injective.prodMap
    canonicalCompletedGreenFrameAnalysisCLM_injective

/-! ## Exact extraction from the completed TFVD ledger -/

/-- The ordinary vertical leg of the seeded ledger is literally the
canonical C3 Dirichlet-gradient prefix. -/
@[simp] theorem seededCompletedTfvdGreenLedger_ordinary_vertical_eq_prefix
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.1.1 =
      canonicalCompletedC3DirichletGradientPrefixState s (3 * M) :=
  rfl

/-- The logarithmic vertical leg of the seeded ledger is literally the
canonical C3 log-jet prefix. -/
@[simp] theorem seededCompletedTfvdGreenLedger_logJet_vertical_eq_prefix
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.2.1 =
      canonicalCompletedC3LogJetPrefixState s (3 * M) :=
  rfl

/-- The ordinary vertical leg is the faithful Hilbert realization of the
ordinary provenance core stored beside it. -/
theorem seededCompletedTfvdGreenLedger_ordinary_vertical_eq_provenance
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.1.1 =
      nativeGpreCanonicalVerticalRealization
        (seededCompletedTfvdGreenLedger M s).1.1.2 :=
  rfl

/-- The log-jet vertical leg is the faithful Hilbert realization of the
logarithmic provenance core stored beside it. -/
theorem seededCompletedTfvdGreenLedger_logJet_vertical_eq_provenance
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.2.1 =
      nativeGpreCanonicalVerticalRealization
        (seededCompletedTfvdGreenLedger M s).1.2.2 :=
  rfl

/-- The ordered pair extracted from the seeded ledger is exactly the
previously completed all-cutoff Hilbert prefix state. -/
theorem seededCompletedTfvdGreenLedger_verticalPair_eq_prefix
    (M : ℕ) (s : ℂ) :
    ((seededCompletedTfvdGreenLedger M s).1.1.1,
        (seededCompletedTfvdGreenLedger M s).1.2.1) =
      canonicalCompletedC3HilbertPrefixState s (3 * M) := by
  rfl

/-! ## Oriented three-channel completion -/

/-- Green-analyzed ordinary/log-jet channels together with the retained
precompression residual. -/
abbrev CanonicalCompletedC3OrientedGreenFrameCarrier :=
  (CanonicalCompletedGreenFrameCarrier ×
      CanonicalCompletedGreenFrameCarrier) ×
    NativeGpreTfvdCompletedPrecompressionSource

/-- The actual cutoff ledger read in the oriented Green-frame carrier. -/
def canonicalCompletedC3OrientedGreenFramePrefixState
    (M : ℕ) (s : ℂ) :
    CanonicalCompletedC3OrientedGreenFrameCarrier :=
  (canonicalCompletedC3GreenFramePairIntertwiner
      ((seededCompletedTfvdGreenLedger M s).1.1.1,
        (seededCompletedTfvdGreenLedger M s).1.2.1),
    (seededCompletedTfvdGreenLedger M s).2)

/-- The completed oriented state. Its residual coefficient is the completed
reflected Green energy multiplying the same fixed residual generator used at
every cutoff. -/
def canonicalCompletedC3OrientedGreenFrameState
    (s : ℂ) (hs : s ∈ genuineCriticalStrip) :
    CanonicalCompletedC3OrientedGreenFrameCarrier :=
  (canonicalCompletedC3GreenFramePairIntertwiner
      (canonicalCompletedC3HilbertState s hs.1),
    infiniteReflectedGreenEnergy s • completedTfvdResidualGenerator)

/-- The Green-frame pair in the cutoff carrier is exactly the analysis of
the canonical all-cutoff prefix, with its source orientation unchanged. -/
theorem canonicalCompletedC3OrientedGreenFramePrefixState_fst
    (M : ℕ) (s : ℂ) :
    (canonicalCompletedC3OrientedGreenFramePrefixState M s).1 =
      canonicalCompletedC3GreenFramePairIntertwiner
        (canonicalCompletedC3HilbertPrefixState s (3 * M)) := by
  rw [canonicalCompletedC3OrientedGreenFramePrefixState,
    seededCompletedTfvdGreenLedger_verticalPair_eq_prefix]

/-- The residual stays a separate scalar multiple of one fixed generator at
every cutoff. -/
theorem canonicalCompletedC3OrientedGreenFramePrefixState_snd
    (M : ℕ) (s : ℂ) :
    (canonicalCompletedC3OrientedGreenFramePrefixState M s).2 =
      (finiteReflectedGradientPairing (3 * M) s).re •
        completedTfvdResidualGenerator := by
  exact seededCompletedTfvdGreenLedger_residual_eq_smul M s

/-- The concrete oriented ordinary/log-jet/residual state converges in its
single completed carrier. -/
theorem canonicalCompletedC3OrientedGreenFramePrefixState_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦ canonicalCompletedC3OrientedGreenFramePrefixState M s)
      atTop
      (nhds (canonicalCompletedC3OrientedGreenFrameState s hs)) := by
  have hpairSource :
      Tendsto
        (fun M : ℕ ↦ canonicalCompletedC3HilbertPrefixState s (3 * M))
        atTop
        (nhds (canonicalCompletedC3HilbertState s hs.1)) :=
    (canonicalCompletedC3HilbertPrefixState_tendsto hs.1).comp
      tendsto_three_mul_atTop
  have hpair :
      Tendsto
        (fun M : ℕ ↦ canonicalCompletedC3GreenFramePairIntertwiner
          (canonicalCompletedC3HilbertPrefixState s (3 * M)))
        atTop
        (nhds (canonicalCompletedC3GreenFramePairIntertwiner
          (canonicalCompletedC3HilbertState s hs.1))) :=
    canonicalCompletedC3GreenFramePairIntertwiner.continuous.continuousAt.tendsto.comp
      hpairSource
  have hresidualCoefficient :
      Tendsto
        (fun M : ℕ ↦ (finiteReflectedGradientPairing (3 * M) s).re)
        atTop
        (nhds (infiniteReflectedGreenEnergy s)) :=
    (finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hs).comp
      tendsto_three_mul_atTop
  have hresidual :
      Tendsto
        (fun M : ℕ ↦
          (finiteReflectedGradientPairing (3 * M) s).re •
            completedTfvdResidualGenerator)
        atTop
        (nhds
          (infiniteReflectedGreenEnergy s •
            completedTfvdResidualGenerator)) :=
    hresidualCoefficient.smul_const completedTfvdResidualGenerator
  apply (hpair.prodMk_nhds hresidual).congr'
  filter_upwards [] with M
  apply Prod.ext
  · exact canonicalCompletedC3OrientedGreenFramePrefixState_fst M s
  · exact (canonicalCompletedC3OrientedGreenFramePrefixState_snd M s).symm

/-! ## Real-axis specialization for the dslope sampling grids -/

/-- The oriented cutoff carrier evaluated at the spectral parameter attached
to a real centered height. -/
def canonicalCompletedC3RealAxisOrientedGreenFramePrefixState
    (M : ℕ) (x : ℝ) : CanonicalCompletedC3OrientedGreenFrameCarrier :=
  canonicalCompletedC3OrientedGreenFramePrefixState M
    (operatorHeightParameter (x : ℂ))

/-- The corresponding completed oriented carrier on the real height axis. -/
def canonicalCompletedC3RealAxisOrientedGreenFrameState
    (x : ℝ) : CanonicalCompletedC3OrientedGreenFrameCarrier :=
  canonicalCompletedC3OrientedGreenFrameState
    (operatorHeightParameter (x : ℂ))
    (ofReal_mem_completedNativeHeightDomain x)

/-- At every real sampling point used by the completed forward differences,
the concrete C3/TFVD cutoff carrier converges to its oriented completion. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFramePrefixState_tendsto
    (x : ℝ) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3RealAxisOrientedGreenFramePrefixState M x)
      atTop
      (nhds (canonicalCompletedC3RealAxisOrientedGreenFrameState x)) :=
  canonicalCompletedC3OrientedGreenFramePrefixState_tendsto
    (ofReal_mem_completedNativeHeightDomain x)

/-- Complex-argument wrapper for the real-axis cutoff carrier. Only the real
sampling coordinate is used, exactly as in the scalar real-axis kernel. -/
def canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3OrientedGreenFrameCarrier :=
  canonicalCompletedC3RealAxisOrientedGreenFramePrefixState M z.re

/-- Complex-argument wrapper for the completed real-axis carrier. -/
def canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex
    (z : ℂ) : CanonicalCompletedC3OrientedGreenFrameCarrier :=
  canonicalCompletedC3RealAxisOrientedGreenFrameState z.re

/-- The real-axis wrapper converges pointwise at every complex sampling
argument. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex_tendsto
    (z : ℂ) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex M z)
      atTop
      (nhds (canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z)) :=
  canonicalCompletedC3RealAxisOrientedGreenFramePrefixState_tendsto z.re

/-- Complex Green-frame pair extracted from the full oriented cutoff carrier.
The real residual remains in the full carrier and is not complexified. -/
def canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex
    (M : ℕ) (z : ℂ) :
    CanonicalCompletedGreenFrameCarrier ×
      CanonicalCompletedGreenFrameCarrier :=
  (canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex M z).1

/-- Completed complex Green-frame pair, with the residual still retained in
the separate full-carrier coordinate. -/
def canonicalCompletedC3RealAxisOrientedGreenFramePairStateComplex
    (z : ℂ) :
    CanonicalCompletedGreenFrameCarrier ×
      CanonicalCompletedGreenFrameCarrier :=
  (canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z).1

/-- Pointwise cutoff convergence of the complex ordinary/log-jet pair. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex_tendsto
    (z : ℂ) :
    Tendsto
      (fun M : ℕ ↦
        canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex M z)
      atTop
      (nhds
        (canonicalCompletedC3RealAxisOrientedGreenFramePairStateComplex z)) :=
  continuous_fst.continuousAt.tendsto.comp
    (canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex_tendsto z)

/-! ## Transport through finite forward differences -/

/-- Pointwise convergence of state-valued functions passes through every
finite iterated forward difference. -/
theorem completedGreenForwardDifference_iter_tendsto_of_pointwise
    {A E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [IsTopologicalAddGroup E]
    (l : Filter A) (state : A → ℂ → E) (limitState : ℂ → E)
    (hstate : ∀ z : ℂ, Tendsto (fun a ↦ state a z) l (nhds (limitState z)))
    (h : ℂ) (n : ℕ) (z : ℂ) :
    Tendsto
      (fun a ↦ (completedGreenForwardDifference h)^[n] (state a) z)
      l
      (nhds ((completedGreenForwardDifference h)^[n] limitState z)) := by
  induction n generalizing z with
  | zero => simpa using hstate z
  | succ n ih =>
      simpa [Function.iterate_succ_apply', completedGreenForwardDifference]
        using (ih (z + h)).sub (ih z)

/-- Every unnormalized iterated forward difference converges in the full
oriented carrier, including its separate real residual coordinate. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFrame_forwardDifferenceIter_tendsto
    (h : ℂ) (n : ℕ) (z : ℂ) :
    Tendsto
      (fun M : ℕ ↦
        (completedGreenForwardDifference h)^[n]
          (canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex M) z)
      atTop
      (nhds
        ((completedGreenForwardDifference h)^[n]
          canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z)) :=
  completedGreenForwardDifference_iter_tendsto_of_pointwise
    atTop
    canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex
    canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex
    canonicalCompletedC3RealAxisOrientedGreenFramePrefixStateComplex_tendsto
    h n z

/-- For every fixed step and order, the normalized forward-difference jet of
the complex ordinary/log-jet pair converges. The residual convergence remains
available independently in the full carrier theorem above. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFrame_forwardDifferenceJet_tendsto
    (h : ℂ) (n : ℕ) :
    Tendsto
      (fun M : ℕ ↦
        completedGreenForwardDifferenceJet
          (canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex M)
          h n)
      atTop
      (nhds
        (completedGreenForwardDifferenceJet
          canonicalCompletedC3RealAxisOrientedGreenFramePairStateComplex h n)) := by
  unfold completedGreenForwardDifferenceJet
  exact (completedGreenForwardDifference_iter_tendsto_of_pointwise
    atTop
    canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex
    canonicalCompletedC3RealAxisOrientedGreenFramePairStateComplex
    canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex_tendsto
    h n 0).const_smul
      (((Nat.factorial n : ℂ) * h ^ n)⁻¹)

/-- The same transported convergence in the parity-interleaved jet used by
the completed moment construction. -/
theorem canonicalCompletedC3RealAxisOrientedGreenFrame_forwardDifferenceParityJet_tendsto
    (k : ℕ) (i : ℕ ⊕ ℕ) :
    Tendsto
      (fun M : ℕ ↦
        completedGreenForwardDifferenceParityJet
          (canonicalCompletedC3RealAxisOrientedGreenFramePairPrefixStateComplex M)
          k i)
      atTop
      (nhds
        (completedGreenForwardDifferenceParityJet
          canonicalCompletedC3RealAxisOrientedGreenFramePairStateComplex k i)) := by
  cases i with
  | inl n =>
      exact
        canonicalCompletedC3RealAxisOrientedGreenFrame_forwardDifferenceJet_tendsto
          (canonicalGreenJetStep k) (2 * n)
  | inr n =>
      exact
        canonicalCompletedC3RealAxisOrientedGreenFrame_forwardDifferenceJet_tendsto
          (canonicalGreenJetStep k) (2 * n + 1)

end

end CarrySelfAdjointOperator
