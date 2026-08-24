import CarrySelfAdjointOperator.CausalBracketStateUniqueness
import CarrySelfAdjointOperator.CompletedC3RawGreenGamma
import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization
import CPFormal.Analytic.CpFiniteGenuineAngularGreenBudget
import CPFormal.Analytic.CpFiniteGenuineTfvdProvenanceGluing

/-!
# Lossless C3 bracket-to-completed-Green transport

The causal unit bracket reconstructs the value sequence from two seeds with
no selected inverse. Its discrete slopes are the ordinary Dirichlet-gradient
channel. The finite Genuine C3 Green boundary pair can therefore be read on
the finite prefixes of the already constructed all-cutoff `l2` state.

The radial, off-diagonal, seam, provenance, and completion channels remain
separate throughout this transport. No scalar Wronskian or spectral
scalarization is used in this file.
-/

open scoped Topology BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-! ## Lossless causal reconstruction -/

/-- Dirichlet values indexed from the positive endpoint `1`. -/
def canonicalC3CausalValueState (s : ℂ) : ℕ → ℂ :=
  positiveDirichletValue s

/-- The two seeds and every causal unit bracket of the Dirichlet value
state. -/
def canonicalC3CausalBracketData (s : ℂ) : CausalBracketData ℂ :=
  { leftSeed := canonicalC3CausalValueState s 0
    centerSeed := canonicalC3CausalValueState s 1
    bracket := causalUnitBracket (canonicalC3CausalValueState s) }

theorem canonicalC3CausalValueState_realizes (s : ℂ) :
    RealizesCausalBracketData
      (canonicalC3CausalBracketData s) (canonicalC3CausalValueState s) := by
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- The bracket ledger reconstructs the original value state exactly. -/
theorem canonicalC3CausalBracketReconstruction_eq_valueState (s : ℂ) :
    causalBracketReconstruction (canonicalC3CausalBracketData s) =
      canonicalC3CausalValueState s := by
  exact (causalBracketReconstruction_unique
    (canonicalC3CausalBracketData s) (canonicalC3CausalValueState s)
    (canonicalC3CausalValueState_realizes s)).symm

/-- There is exactly one value state carrying the two seeds and all causal
brackets. -/
theorem existsUnique_canonicalC3CausalValueState (s : ℂ) :
    ∃! x : ℕ → ℂ,
      RealizesCausalBracketData (canonicalC3CausalBracketData s) x :=
  existsUnique_realizesCausalBracketData (canonicalC3CausalBracketData s)

/-- Explicit right-leg reconstruction at each causal cell. -/
theorem canonicalC3CausalValueState_rightLeg (s : ℂ) (left : ℕ) :
    canonicalC3CausalValueState s (left + 2) =
      causalUnitBracket (canonicalC3CausalValueState s) left -
        canonicalC3CausalValueState s left +
          2 • canonicalC3CausalValueState s (left + 1) :=
  rightLeg_eq_bracket_sub_left_add_two_center
    (canonicalC3CausalValueState s) left

/-- The reconstructed slopes are exactly the ordinary gradient channel. -/
theorem canonicalC3CausalSlope_eq_positiveDirichletGradient
    (s : ℂ) (n : ℕ) :
    causalSlope (canonicalC3CausalValueState s) n =
      positiveDirichletGradient s n := by
  simp [causalSlope, canonicalC3CausalValueState,
    positiveDirichletGradient_eq_value_sub_value]

/-- Every saturated C3 bracket is one sampled causal unit bracket of the
lossless all-cell ledger. -/
theorem realCpSaturatedBracket_three_eq_causalUnitBracket
    (m : ℕ) (s : ℂ) :
    realCpSaturatedBracket 3 m s =
      causalUnitBracket (canonicalC3CausalValueState s) (3 * m + 1) := by
  rw [realCpSaturatedBracket_three_eq_values]
  simp [causalUnitBracket, canonicalC3CausalValueState,
    positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc]

/-! ## Finite Green Gram on completed prefixes -/

/-- The second coordinate of the finite Genuine port is literally the
ordinary completed-state prefix at the same edge. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_snd_eq_completedPrefix
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M s).2 n =
      canonicalCompletedC3DirichletGradientPrefixState s M (n : ℕ) := by
  rw [NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_snd_apply,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  simp [n.isLt]

/-- The first coordinate is the same prefix after the canonical phase
normalization has made the raw C3 eigenvalue radial and real. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_fst_eq_radial_mul_completedPrefix
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M s).1 n =
      (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) *
        canonicalCompletedC3DirichletGradientPrefixState s M (n : ℕ) := by
  rw [NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_fst_apply,
    phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
      3 (by norm_num),
    phaseNormalizedCpBlockGradient_eq_radial_mul 3 (by norm_num),
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  simp [n.isLt]

/-- The bracket-resolved port and the native finite C3 Green port are the
same pair before any Hilbert or scalar readout. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_eq_nativeGreenPair
    (M : ℕ) (s : ℂ) :
    NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M s =
      NativeCarryC3Crosswalk.finiteC3GreenBoundaryPair M s :=
  NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair
    M s

/-- The finite reflected gradient pairing is exactly the Hilbert inner
product of the corresponding all-cutoff prefix states. -/
theorem finiteReflectedGradientPairing_eq_inner_completedC3Prefixes
    (M : ℕ) (s : ℂ) :
    finiteReflectedGradientPairing M s =
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState s M)
        (canonicalCompletedC3DirichletGradientPrefixState
          (reflectedParameter s) M) := by
  change NativeCarryC3Crosswalk.c3RawGammaGram M s
      (reflectedParameter s) = _
  exact c3RawGammaGram_eq_inner_completedPrefix
    M s (reflectedParameter s)

/-- The Genuine-bracket Green form acts on the same finite `l2` prefixes;
the coefficient is still the radial C3 coefficient. -/
theorem greenForm_finiteC3GenuineBracket_eq_coefficient_mul_prefixGram
    (M : ℕ) (s : ℂ) :
    greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M s)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M
          (reflectedParameter s)) =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        inner ℂ
          (canonicalCompletedC3DirichletGradientPrefixState s M)
          (canonicalCompletedC3DirichletGradientPrefixState
            (reflectedParameter s) M) := by
  rw [NativeCarryC3Crosswalk.greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization,
    finiteReflectedGradientPairing_eq_inner_completedC3Prefixes]

/-! ## Channel-separated finite transport ledger -/

/-- Channels used by the finite transport. The completion coordinate keeps
both ordinary/log-jet prefix states for `s` and its reflected parameter. -/
structure CanonicalC3FiniteGreenGramTransportLedger where
  radial : ℂ
  offDiagonal : ℂ
  seam : ℂ
  provenance : ℂ
  completion :
    CanonicalCompletedC3HilbertState × CanonicalCompletedC3HilbertState

def canonicalC3FiniteGreenGramTransportLedger
    (M : ℕ) (s : ℂ) : CanonicalC3FiniteGreenGramTransportLedger :=
  { radial :=
      greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) s)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s))
    offDiagonal := finiteCanonicalAngularPairingOffDiagonal M s
    seam := finiteCanonicalAngularBracketCoupledBoundary M s
    provenance := finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s
    completion :=
      (canonicalCompletedC3HilbertPrefixState s (3 * M),
        canonicalCompletedC3HilbertPrefixState
          (reflectedParameter s) (3 * M)) }

/-- Only the radial coordinate is read here. The off-diagonal, seam, and
provenance coordinates remain present and unchanged. -/
theorem canonicalC3FiniteGreenGramTransportLedger_radial_eq
    (M : ℕ) (s : ℂ) :
    (canonicalC3FiniteGreenGramTransportLedger M s).radial =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        inner ℂ
          (canonicalC3FiniteGreenGramTransportLedger M s).completion.1.1
          (canonicalC3FiniteGreenGramTransportLedger M s).completion.2.1 := by
  unfold canonicalC3FiniteGreenGramTransportLedger
  dsimp only
  exact
    greenForm_finiteC3GenuineBracket_eq_coefficient_mul_prefixGram
      (3 * M) s

/-- The completion coordinate converges as a pair, while every non-radial
finite channel remains a separate ledger coordinate. -/
theorem canonicalC3FiniteGreenGramTransportLedger_completion_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        (canonicalC3FiniteGreenGramTransportLedger M s).completion)
      atTop
      (nhds
        (canonicalCompletedC3HilbertState s hs.1,
          canonicalCompletedC3HilbertState (reflectedParameter s)
            (by simpa [reflectedParameter] using sub_pos.mpr hs.2))) := by
  have hsReflected : 0 < (reflectedParameter s).re := by
    simpa [reflectedParameter] using sub_pos.mpr hs.2
  have hleft :=
    (canonicalCompletedC3HilbertPrefixState_tendsto hs.1).comp
      tendsto_three_mul_atTop
  have hright :=
    (canonicalCompletedC3HilbertPrefixState_tendsto hsReflected).comp
      tendsto_three_mul_atTop
  simpa [canonicalC3FiniteGreenGramTransportLedger] using
    hleft.prodMk_nhds hright

/-- The finite Genuine-bracket Green forms converge directly to the Gram
kernel of the completed ordinary states. -/
theorem greenForm_finiteC3GenuineBracket_tendsto_completedStateKernel
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ =>
        greenForm (𝕜 := ℂ)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M s)
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair M
            (reflectedParameter s)))
      atTop
      (nhds
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          inner ℂ
            (canonicalCompletedC3DirichletGradientState s hs.1)
            (canonicalCompletedC3DirichletGradientState
              (reflectedParameter s)
              (by simpa [reflectedParameter] using sub_pos.mpr hs.2)))) := by
  have hsReflected : 0 < (reflectedParameter s).re := by
    simpa [reflectedParameter] using sub_pos.mpr hs.2
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (canonicalCompletedC3DirichletGradientPrefixState_tendsto hs.1)
    (canonicalCompletedC3DirichletGradientPrefixState_tendsto hsReflected)
  have hscaled := hinner.const_mul
    (((cpRadialDifference 3
      (criticalDisplacement s.re) : ℝ) : ℂ))
  exact hscaled.congr' (Eventually.of_forall fun M =>
    (greenForm_finiteC3GenuineBracket_eq_coefficient_mul_prefixGram
      M s).symm)

/-- The completed reflected Gram kernel is the pre-existing infinite
reflected pairing, now realized inside the completed `l2` state. -/
theorem inner_completedC3ReflectedStates_eq_infinitePairing
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3DirichletGradientState s hs.1)
        (canonicalCompletedC3DirichletGradientState
          (reflectedParameter s)
          (by simpa [reflectedParameter] using sub_pos.mpr hs.2)) =
      infiniteReflectedGradientPairing s := by
  unfold infiniteReflectedGradientPairing finiteReflectedGradientEdge
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [RCLike.inner_apply, mul_comm]

/-- Compatibility check: the direct completed-state limit is exactly the
existing radial-factorization limit, with no scalar readout inserted. -/
theorem completedC3GenuineBracketKernel_eq_existingInfiniteFactorization
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        inner ℂ
          (canonicalCompletedC3DirichletGradientState s hs.1)
          (canonicalCompletedC3DirichletGradientState
            (reflectedParameter s)
            (by simpa [reflectedParameter] using sub_pos.mpr hs.2)) =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        infiniteReflectedGradientPairing s := by
  rw [inner_completedC3ReflectedStates_eq_infinitePairing hs]

end

end CarrySelfAdjointOperator
