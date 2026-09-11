import CarrySelfAdjointOperator.CompletedNativePolarizedTfvdGreenMomentKernel
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyCollapse
import Mathlib.Tactic

/-!
# Primus same-edge recovery to the polarized native Green Gram

The old `CPFormal`/Primus same-edge construction recovers the reflected
Dirichlet gradient from the ordinary gradient and its logarithmic jet before
any prime-camera scalar readout.  The current completed C3 development already
uses the ordinary Dirichlet-gradient prefixes as the raw two-variable Green
Gram carrier.

This module identifies those two constructions directly.  The reflected leg
of the current mixed C3 Gram is rebuilt from the Primus same-edge inversion,
coordinate by coordinate, and only afterwards paired with the direct leg.
No moment sequence, Hankel matrix, fixed-time profile transport, or target Gram
is used to define the recovered state.
-/

open scoped BigOperators ComplexConjugate Topology lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- Finite reflected C3 prefix reconstructed directly from the Primus
ordinary/log-jet same-edge data.  The state is defined before comparing it with
any pre-existing Green prefix. -/
def canonicalC3SameEdgeRecoveredReflectedPrefixState
    (M : ℕ) (z : ℂ) : CarryVerticalL2 :=
  ∑ n ∈ Finset.range M,
    lp.single 2 n
      (sameEdgeRecoveredReflectedGradient n
        (positiveDirichletGradient z n)
        (positiveLogDirichletGradient z n))

/-- The Primus same-edge recovered prefix is literally the reflected ordinary
Dirichlet-gradient prefix already used by the completed C3 Green carrier. -/
theorem canonicalC3SameEdgeRecoveredReflectedPrefixState_eq_completedPrefix
    (M : ℕ) (z : ℂ) :
    canonicalC3SameEdgeRecoveredReflectedPrefixState M z =
      canonicalCompletedC3DirichletGradientPrefixState
        (reflectedParameter z) M := by
  rw [canonicalCompletedC3DirichletGradientPrefixState_eq_sum_single]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sameEdgeRecoveredReflectedGradient_canonical]

/-- The raw two-variable C3 gamma Gram can therefore be read directly against
the same-edge reconstructed reflected leg. -/
theorem c3RawGammaGram_eq_inner_sameEdgeRecoveredReflectedPrefix
    (M : ℕ) (z w : ℂ) :
    c3RawGammaGram M w (reflectedParameter z) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientPrefixState w M)
        (canonicalC3SameEdgeRecoveredReflectedPrefixState M z) := by
  rw [c3RawGammaGram_eq_inner_completedPrefix,
    canonicalC3SameEdgeRecoveredReflectedPrefixState_eq_completedPrefix]

/-- Exact finite polarized Green form with its reflected Hilbert leg sourced
from the Primus ordinary/log-jet same-edge reconstruction. -/
theorem
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_sameEdgeGram
    (M : ℕ) (z w : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M w)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z)) =
      canonicalC3MixedRadialCoefficient z w *
        inner ℂ
          (canonicalCompletedC3DirichletGradientPrefixState w M)
          (canonicalC3SameEdgeRecoveredReflectedPrefixState M z) := by
  rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
    c3RawGammaGram_eq_inner_sameEdgeRecoveredReflectedPrefix]

/-- The completed mixed Wronskian ledger can be rewritten with the explicit
same-edge recovered Green Gram at every finite cutoff.  All previously named
structural and completion defects remain unchanged. -/
theorem canonicalCompletedC3RawMixedWronskian_eq_sameEdgeGreenGram_add_totalDefect
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      canonicalC3MixedRadialCoefficient z w *
          inner ℂ
            (canonicalCompletedC3DirichletGradientPrefixState w (3 * M))
            (canonicalC3SameEdgeRecoveredReflectedPrefixState (3 * M) z) +
        canonicalC3FiniteMixedTotalDefect M z w := by
  rw [canonicalCompletedC3RawMixedWronskian_eq_green_add_totalDefect
      M hz hw,
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_sameEdgeGram]

/-- The reconstructed reflected prefixes converge to the same completed
reflected C3 state, so the same-edge provenance survives completion. -/
theorem canonicalC3SameEdgeRecoveredReflectedPrefixState_tendsto
    {z : ℂ} (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ => canonicalC3SameEdgeRecoveredReflectedPrefixState M z)
      atTop
      (nhds
        (canonicalCompletedC3DirichletGradientState
          (reflectedParameter z) hzReflected)) := by
  simpa only
      [canonicalC3SameEdgeRecoveredReflectedPrefixState_eq_completedPrefix] using
    (canonicalCompletedC3DirichletGradientPrefixState_tendsto hzReflected)

/-- The polarized same-edge Gram itself has the existing completed raw gamma
Gram as its norm-limit kernel. -/
theorem c3SameEdgeRecoveredMixedGram_tendsto_completed
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ =>
        inner ℂ
          (canonicalCompletedC3DirichletGradientPrefixState w M)
          (canonicalC3SameEdgeRecoveredReflectedPrefixState M z))
      atTop
      (nhds
        (canonicalCompletedC3RawGammaGram
          w (reflectedParameter z) hw hzReflected)) := by
  have hgram := c3RawGammaGram_tendsto_completed hw hzReflected
  exact hgram.congr'
    (Eventually.of_forall fun M =>
      (c3RawGammaGram_eq_inner_sameEdgeRecoveredReflectedPrefix M z w))

/-- Along the native `3M` block cutoffs, the exact same-edge Green Gram tends
to the completed mixed radial Green kernel already used by the polarized
TFVD/Green ledger. -/
theorem finiteC3SameEdgeRecoveredMixedGreen_tendsto_completed
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ =>
        canonicalC3MixedRadialCoefficient z w *
          inner ℂ
            (canonicalCompletedC3DirichletGradientPrefixState w (3 * M))
            (canonicalC3SameEdgeRecoveredReflectedPrefixState (3 * M) z))
      atTop
      (nhds
        (canonicalCompletedC3MixedRadialGreenKernel
          z w hw hzReflected)) := by
  have hgreen := finiteC3MixedRadialGreen_tendsto_completed hw hzReflected
  exact hgreen.congr'
    (Eventually.of_forall fun M =>
      (greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_sameEdgeGram
        (3 * M) z w))

end

end CarrySelfAdjointOperator
