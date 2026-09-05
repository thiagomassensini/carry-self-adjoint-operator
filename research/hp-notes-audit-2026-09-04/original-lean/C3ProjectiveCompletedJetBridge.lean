import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import CPFormal.Analytic.CpNativeGpreTfvdProjectiveAnalysis
import CPFormal.Analytic.CpNativeGpreTfvdGenuineCompression
import CPFormal.Analytic.CpNativeCarryWeightedSpectralState
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail

/-!
# C3 projective completion and all-order jet bridge

This file connects three already formalized layers without identifying objects
that live in different spaces:

* the finite weighted native state is the canonical finite-support truncation
  of one cutoff-free state in `CarryVerticalL2`;
* continuous projective TFVD--provenance analysis carries that strong limit to
  its closed projective range;
* at the scalar camera port, adding the exact analytic tail to every finite
  iterated jet gives a cutoff-independent completed jet in every order.

Thus the orthogonal finite visible/blind decomposition and the C3 head/tail
completion meet through the common completed state, rather than through an
ill-typed literal equality between a Hilbert projection and a scalar tail.
-/

open scoped BigOperators Topology lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The finite weighted state is exactly the canonical `l²` partial sum of
the cutoff-free weighted native state. -/
theorem nativeGpreFiniteWeightedRealSpectralState_eq_partialSum
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) (t : ℝ) :
    nativeGpreFiniteWeightedRealSpectralState q M t =
      ∑ n ∈ Finset.range (3 * M + 1),
        (lp.single 2 n
          (nativeCarryWeightedRealSpectralState q hq0 hq1 t n) :
            CarryVerticalL2) := by
  ext n
  by_cases hn : n < 3 * M + 1
  · simp only [nativeCarryWeightedRealSpectralState_apply]
    rw [nativeGpreFiniteWeightedRealSpectralState_apply_of_lt q M t n hn]
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
      Finset.sum_pi_single]
    simp [hn]
  · rw [nativeGpreFiniteWeightedRealSpectralState,
      nativeGpreCanonicalVerticalRealization_apply]
    have hle : ¬ n ≤ 3 * M := by omega
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
      Finset.sum_pi_single]
    simp [nativeGpreFiniteWeightedRealSpectralCore, hn, hle]

/-- The moving finite states converge strongly in `l²` to the single
cutoff-free weighted state. -/
theorem nativeGpreFiniteWeightedRealSpectralState_tendsto
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    Tendsto
      (fun M : ℕ ↦ nativeGpreFiniteWeightedRealSpectralState q M t)
      atTop
      (nhds (nativeCarryWeightedRealSpectralState q hq0 hq1 t)) := by
  let x := nativeCarryWeightedRealSpectralState q hq0 hq1 t
  have hsum : Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
        (lp.single 2 n (x n) : CarryVerticalL2))
      atTop (nhds x) :=
    (lp.hasSum_single ENNReal.ofNat_ne_top x).tendsto_sum_nat
  have hindex : Tendsto (fun M : ℕ ↦ 3 * M + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro bound
    filter_upwards [eventually_ge_atTop bound] with M hM
    omega
  have hfinite :
      (fun M : ℕ ↦ nativeGpreFiniteWeightedRealSpectralState q M t) =
        (fun M : ℕ ↦
          ∑ n ∈ Finset.range (3 * M + 1),
            (lp.single 2 n (x n) : CarryVerticalL2)) := by
    funext M
    exact nativeGpreFiniteWeightedRealSpectralState_eq_partialSum
      q hq0 hq1 M t
  rw [hfinite]
  change Tendsto
    ((fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      (lp.single 2 n (x n) : CarryVerticalL2)) ∘
        (fun M : ℕ ↦ 3 * M + 1))
    atTop (nhds x)
  exact hsum.comp hindex

/-- Continuity transports the strong state completion into the simultaneous
projective TFVD--provenance analysis. -/
theorem nativeGpreTfvdProjectiveAnalysis_finiteWeightedState_tendsto
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    Tendsto
      (fun M : ℕ ↦
        nativeGpreTfvdProjectiveAnalysis q
          (nativeGpreFiniteWeightedRealSpectralState q M t))
      atTop
      (nhds
        (nativeGpreTfvdProjectiveAnalysis q
          (nativeCarryWeightedRealSpectralState q hq0 hq1 t))) := by
  exact ((nativeGpreTfvdProjectiveAnalysis q).continuous.tendsto _).comp
    (nativeGpreFiniteWeightedRealSpectralState_tendsto q hq0 hq1 t)

/-- The completed infinite state produces a compatible family in every
finite provenance atlas. -/
theorem nativeGpreTfvdProjectiveAnalysis_completedState_compatible
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (t : ℝ) :
    NativeGpreTfvdProjectiveCompatible
      (nativeGpreTfvdProjectiveAnalysis q
        (nativeCarryWeightedRealSpectralState q hq0 hq1 t)) :=
  nativeGpreTfvdProjectiveAnalysis_compatible q _

end

end CPFormal.Analytic.Cp

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Exact all-order C3 jet completion: finite jet plus the derivative of its
analytic remainder. -/
def c3CompletedIteratedJet (cutoff order : ℕ) (s : ℂ) : ℂ :=
  iteratedDeriv order (finiteBracketCharacteristic 3 cutoff) s +
    iteratedDeriv order
      (fun z : ℂ ↦ bracketCharacteristic 3 z -
        finiteBracketCharacteristic 3 cutoff z) s

/-- Every completed finite C3 jet is literally the cutoff-free jet. -/
theorem c3CompletedIteratedJet_eq
    (cutoff order : ℕ) {s : ℂ} (hs : s ∈ bracketDomain) :
    c3CompletedIteratedJet cutoff order s =
      iteratedDeriv order (bracketCharacteristic 3) s := by
  have hinfinite : ContDiffAt ℂ order (bracketCharacteristic 3) s :=
    ((bracketCharacteristic_differentiableOn (by norm_num : 2 ≤ 3)).contDiffOn
      isOpen_bracketDomain).contDiffAt (isOpen_bracketDomain.mem_nhds hs)
  have hfinite : ContDiffAt ℂ order
      (finiteBracketCharacteristic 3 cutoff) s :=
    (finiteBracketCharacteristic_differentiable
      (by norm_num : 2 ≤ 3) cutoff).contDiff.contDiffAt
  unfold c3CompletedIteratedJet
  change iteratedDeriv order (finiteBracketCharacteristic 3 cutoff) s +
      iteratedDeriv order
        (bracketCharacteristic 3 - finiteBracketCharacteristic 3 cutoff) s =
    iteratedDeriv order (bracketCharacteristic 3) s
  rw [iteratedDeriv_sub hinfinite hfinite]
  ring

/-- Projective cutoff invariance of the completed jet, simultaneously for
every derivative order. -/
theorem c3CompletedIteratedJet_cutoff_invariant
    (M N order : ℕ) {s : ℂ} (hs : s ∈ bracketDomain) :
    c3CompletedIteratedJet M order s =
      c3CompletedIteratedJet N order s := by
  rw [c3CompletedIteratedJet_eq M order hs,
    c3CompletedIteratedJet_eq N order hs]

/-- The existing enriched value/log-jet head--tail readout is already
projectively independent of the finite cutoff. -/
theorem finiteC3CanonicalEnrichedTfvdPairTailReadout_cutoff_invariant
    (M N : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : -1 < s.re) :
    finiteC3CanonicalEnrichedTfvdPairTailReadout M kappa omega s =
      finiteC3CanonicalEnrichedTfvdPairTailReadout N kappa omega s := by
  rw [finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      M hkappa omega homega hs,
    finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      N hkappa omega homega hs]

/-- The typed enriched TFVD/Green defect inherits the same exact projective
cutoff invariance. -/
theorem finiteC3EnrichedTfvdPairTailDefect_cutoff_invariant
    (M N : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : -1 < s.re) :
    finiteC3EnrichedTfvdPairTailDefect M kappa omega s =
      finiteC3EnrichedTfvdPairTailDefect N kappa omega s := by
  rw [finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
      M hkappa omega homega s,
    finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
      N hkappa omega homega s]
  exact finiteC3GenuineTailGreenDefect_cutoff_invariant M N hs

end

end NativeCarryC3Crosswalk

#print axioms CPFormal.Analytic.Cp.nativeGpreFiniteWeightedRealSpectralState_tendsto
#print axioms CPFormal.Analytic.Cp.nativeGpreTfvdProjectiveAnalysis_finiteWeightedState_tendsto
#print axioms NativeCarryC3Crosswalk.c3CompletedIteratedJet_cutoff_invariant
#print axioms NativeCarryC3Crosswalk.finiteC3CanonicalEnrichedTfvdPairTailReadout_cutoff_invariant
#print axioms NativeCarryC3Crosswalk.finiteC3EnrichedTfvdPairTailDefect_cutoff_invariant
