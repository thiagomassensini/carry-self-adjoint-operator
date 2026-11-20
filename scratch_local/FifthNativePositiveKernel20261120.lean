import scratch_local.FifthNativeSourceClosed20261120
import Mathlib.Tactic

/-!
# Fifth positive channel of the completed native C3 source

The fifth Taylor/Schur identity is unconditional (previous file).
This module accepts *only* the geometric third-even-pivot sign, whose
source-derived C3 proof lives in GoN PR #324, and constructs the
actual fifth positive source channel plus its complete residual.

A finite Gram of positive channels is not an all-order positive
native Green kernel: the exact fifth residual remains.
-/

namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

theorem chainAxis_four_real_eq_sourceScale :
    chainAxis 4 0 = (chainScale 4 : ℂ) := by
  rw [chainAxis_four_eq_native_det_ratio, chainScale_four_eq_native_det_ratio]
  unfold nativeD2 nativeD3 nativeOddD2 nativeD2Real nativeD3Real nativeOddD2Real
  push_cast
  ring

theorem chain_first_five_real_scales (j : ℕ) (hj : j < 5) :
    chainAxis j 0 = (chainScale j : ℂ) := by
  by_cases h : j < 4
  · exact chain_first_four_real_scales j h
  · have hj4 : j = 4 := by omega
    subst j
    exact chainAxis_four_real_eq_sourceScale

theorem chain_first_five_scales_pos
    (hThird : 0 < sourceMomentSchur m 0 2)
    (j : ℕ) (hj : j < 5) :
    0 < chainScale j := by
  by_cases h : j < 4
  · exact chain_first_four_scales_pos j h
  · have hj4 : j = 4 := by omega
    subst j
    exact chainScale_four_pos_of_C3EvenThirdPivot hThird

theorem chain_first_five_regular_local
    (hThird : 0 < sourceMomentSchur m 0 2) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ j < 5, chainAxis j z ≠ 0 := by
  rcases chain_first_four_regular_local with ⟨U, hUopen, hUzero, hOld⟩
  have hPos : 0 < chainScale 4 :=
    chainScale_four_pos_of_C3EvenThirdPivot hThird
  have h4 : ∀ᶠ z : ℂ in nhds 0, chainAxis 4 z ≠ 0 := by
    apply chainAxis_four_analyticAt_zero.continuousAt.eventually_ne
    rw [chainAxis_four_real_eq_sourceScale]
    exact Complex.ofReal_ne_zero.mpr hPos.ne'
  obtain ⟨V, hVsub, hVopen, hVzero⟩ := mem_nhds_iff.mp h4
  refine ⟨U ∩ V, hUopen.inter hVopen, ⟨hUzero, hVzero⟩, ?_⟩
  intro z hz j hj
  by_cases h : j < 4
  · exact hOld z hz.1 j h
  · have hj4 : j = 4 := by omega
    subst j
    exact hVsub hz.2

/-- Native source fifth positive channel with all two-variable crossings
retained and its exact unchanged residual. The sign gate is solely the
source-derived even third Schur pivot; none of the moment positivity
at orders >= 4 is assumed. -/
theorem sourceKernel_five_positive_channels_local
    (hThird : 0 < sourceMomentSchur m 0 2) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        sourceKernel z w =
          chainPrefixKernel 5 z w +
          conj (chainWeight 5 z) * chainWeight 5 w *
            chainKernel 5 z w := by
  rcases chain_first_five_regular_local hThird with ⟨U, hU, h0, hreg⟩
  refine ⟨U, hU, h0, ?_⟩
  intro z hz w hw hsep
  exact chainKernel_prefix 5 chain_first_five_centers
    chain_first_five_real_scales
    (chain_first_five_scales_pos hThird) z w (hreg z hz) (hreg w hw) hsep

/-- Fully completed native C3 Wronskian response, rather than only an
auxiliary positive kernel, with the FIFTH residual shown explicitly. -/
theorem nativeKernel_five_positive_channels_local
    (hThird : 0 < sourceMomentSchur m 0 2) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
          conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z)) / (w - conj z) =
          chainPrefixKernel 5 z w +
          conj (chainWeight 5 z) * chainWeight 5 w *
            chainKernel 5 z w := by
  rcases sourceKernel_five_positive_channels_local hThird
    with ⟨U, hU, h0U, hsource⟩
  rcases sourceKernel_eq_native_local with ⟨V, hV, h0V, hnative⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨h0U, h0V⟩, ?_⟩
  intro z hz w hw hsep
  rw [← (hnative z hz.2 w hw.2).2.2]
  exact hsource z hz.1 w hw.1 hsep

end
end CarrySelfAdjointOperator.SourcePositiveReduction

#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.chainAxis_four_real_eq_sourceScale
#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.nativeKernel_five_positive_channels_local
