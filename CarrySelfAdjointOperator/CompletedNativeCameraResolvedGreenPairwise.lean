import CarrySelfAdjointOperator.CompletedNativeTfvdSixChannelJet
import Mathlib.Tactic

/-!
# Pairwise Green expansion for a camera-resolved source

The completed six-source readout keeps a Green pairing of a direct and a
reflected port.  This file records the purely algebraic fact needed before a
future full camera resolution of those ports: if both ports are synthesized
from finite camera families, their Green contribution is a double sum.  In
particular, no diagonal-only camera formula follows from linear synthesis.

This is deliberately independent of moment, Hankel, or spectral claims.  It
does not assert that the current camera-resolved log-jet carrier resolves both
ordinary ports; it only fixes the unavoidable shape once such a resolution is
provided by geometry.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open C3TraceDynamics
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Additivity of the Green form in a finite sum in its first, conjugate-linear
argument. -/
theorem greenForm_finset_sum_left
    {𝕜 H ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : Finset ι) (x : ι → H × H) (y : H × H) :
    greenForm (𝕜 := 𝕜) (∑ i ∈ A, x i) y =
      ∑ i ∈ A, greenForm (𝕜 := 𝕜) (x i) y := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha hA =>
      rw [Finset.sum_insert ha, greenForm_add_left, hA,
        Finset.sum_insert ha]

/-- Additivity of the Green form in a finite sum in its second, linear
argument. -/
theorem greenForm_finset_sum_right
    {𝕜 H ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (x : H × H) (A : Finset ι) (y : ι → H × H) :
    greenForm (𝕜 := 𝕜) x (∑ i ∈ A, y i) =
      ∑ i ∈ A, greenForm (𝕜 := 𝕜) x (y i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha hA =>
      rw [Finset.sum_insert ha, greenForm_add_right, hA,
        Finset.sum_insert ha]

/-- Exact camera-pair expansion of a Green boundary term.  The off-diagonal
terms are retained literally: the right side ranges independently over the
two finite camera atlases. -/
theorem greenForm_finset_sum_pairwise
    {𝕜 H ι κ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : Finset ι) (B : Finset κ)
    (direct : ι → H × H) (reflected : κ → H × H) :
    greenForm (𝕜 := 𝕜) (∑ r ∈ A, direct r) (∑ q ∈ B, reflected q) =
      ∑ r ∈ A, ∑ q ∈ B,
        greenForm (𝕜 := 𝕜) (direct r) (reflected q) := by
  rw [greenForm_finset_sum_left]
  apply Finset.sum_congr rfl
  intro r hr
  exact greenForm_finset_sum_right (direct r) B reflected

/-- The corrected six-source final readout has a genuinely mixed structural
shape: a Green term of two reconstructed ports, retained provenance and
off-diagonal terms, a tail completion, and an archimedean chart.  This is an
unfolding theorem, rather than an illicit linearization of the readout. -/
theorem canonicalC3AllCutoffMixedSourceTfvdFinalReadout_eq_components
    (M : ℕ) (z w : ℂ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset CPFormal.Analytic.Cp.NativeGpreBoundaryContext)
    (data : CanonicalC3AllCutoffMixedSourceTfvdAnalysisData S) :
    canonicalC3AllCutoffMixedSourceTfvdFinalReadout M z w q hq0 hq1 S data =
      let structural := canonicalC3AllCutoffMixedSourceTfvdStructuralReadout M
        (operatorHeightParameter w)
        (reflectedParameter (operatorHeightParameter z)) q hq0 hq1 S data
      mixedHermitianWeight nativeXiCompletionFactor z w *
          (canonicalC3AllCutoffMixedSourceTfvdCorrectedBoundary M
              (operatorHeightParameter z) (operatorHeightParameter w)
              q hq0 hq1 S data +
            canonicalC3MixedStructuralScalarReadout structural +
            canonicalC3MixedHeightTailCompletionDefect M z w) +
        canonicalCompletedC3ArchimedeanChartMixedChannel z w := rfl

end

end CarrySelfAdjointOperator
