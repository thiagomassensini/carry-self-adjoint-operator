import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedNativeTfvdEnrichedTaylorMomentIdentification
import Mathlib.Tactic

/-!
# Low-order audit of the enriched TFVD Taylor carrier

The current enriched carrier is the orthogonal sum of the ordinary TFVD
Taylor channel and its logarithmic Taylor channel.  This module tests the
first diagonal entry of its complex Gram against the canonical native moment.
The test is intentionally stopped at order zero when the exact central
calibration gives a strict mismatch.  No camera atlas, cutoff limit, phase
choice, or scalar normalization is introduced.
-/

open scoped ComplexOrder InnerProductSpace lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The real central defect of the enriched zeroth Gram relative to the
canonical native zeroth moment.  A positive value means that the carrier
already fails the `(0,0)` polarized moment equation. -/
def enrichedTfvdTaylorZeroZeroDefect : ℝ :=
  (inner ℂ
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
      (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re -
    canonicalCompletedNativeLogDerivativeMoment 0

/-- The ordinary channel contribution to the real zeroth Gram is exactly the
reflected Green energy at the central height. -/
theorem enrichedTfvdTaylorZeroZeroOrdinaryGram_re_eq_reflectedGreen :
    (inner ℂ
      (canonicalCompletedNativeTfvdTaylorCoefficientState 0)
      (canonicalCompletedNativeTfvdTaylorCoefficientState 0)).re =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) := by
  rw [canonicalCompletedNativeTfvdTaylorCoefficientState_zero]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  exact (infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq).symm

/-- The logarithmic channel contribution to the real zeroth Gram is its
central log-jet norm square. -/
theorem enrichedTfvdTaylorZeroZeroLogGram_re_eq_logJetNormSq :
    (inner ℂ
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)
      (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)).re =
      ‖canonicalCompletedC3LogJetState
          (1 / 2 : ℂ) (by norm_num)‖ ^ 2 := by
  rw [canonicalCompletedNativeTfvdLogTaylorCoefficientState_zero]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The exact zeroth enriched Gram, opened into its ordinary reflected Green
energy and logarithmic channel energy. -/
theorem enrichedTfvdTaylorZeroZeroGram_re_eq_reflectedGreen_add_logJet :
    (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
        ‖canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num)‖ ^ 2 := by
  exact inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet

/-- The full complex self-Gram is the canonical real scalar obtained from
that channel sum.  The real-part theorem is upgraded using the standard fact
that a self-inner product has zero imaginary part. -/
theorem enrichedTfvdTaylorZeroZeroGram_eq_ofReal :
    inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) =
      ((infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
        ‖canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num)‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  apply Complex.ofReal_inj.mpr
  have h :=
    inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet_zero_zero_re_eq_reflectedGreen_add_logJet
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h

/-- The same central defect written channel by channel.  This is an exact
identity, not a fitted or asymptotic calibration. -/
theorem enrichedTfvdTaylorZeroZeroDefect_eq_channelGrams_sub_native :
    enrichedTfvdTaylorZeroZeroDefect =
      (inner ℂ
        (canonicalCompletedNativeTfvdTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdTaylorCoefficientState 0)).re +
      (inner ℂ
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState 0)).re -
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  unfold enrichedTfvdTaylorZeroZeroDefect
  rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet]
  simp only [Complex.add_re]

/-- The named central defect is exactly the reflected Green energy plus the
log-jet energy, minus the canonical native moment. -/
theorem enrichedTfvdTaylorZeroZeroDefect_eq_reflectedGreen_add_logJet_sub_native :
    enrichedTfvdTaylorZeroZeroDefect =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) +
        ‖canonicalCompletedC3LogJetState
            (1 / 2 : ℂ) (by norm_num)‖ ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  unfold enrichedTfvdTaylorZeroZeroDefect
  rw [enrichedTfvdTaylorZeroZeroGram_re_eq_reflectedGreen_add_logJet]

/-- The enriched zeroth defect is strictly positive.  The proof uses only the
already formalized bounds `h₀ < 1/16` and reflected Green energy `> 1/16`,
together with nonnegativity of the log-jet norm square. -/
theorem enrichedTfvdTaylorZeroZeroDefect_pos :
    0 < enrichedTfvdTaylorZeroZeroDefect := by
  rw [enrichedTfvdTaylorZeroZeroDefect_eq_reflectedGreen_add_logJet_sub_native]
  have hE := infiniteReflectedGreenEnergy_half_gt_sixteenth
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith [sq_nonneg
    ‖canonicalCompletedC3LogJetState (1 / 2 : ℂ) (by norm_num)‖]

/-- In particular, the explicit central defect is nonzero. -/
theorem enrichedTfvdTaylorZeroZeroDefect_ne_zero :
    enrichedTfvdTaylorZeroZeroDefect ≠ 0 :=
  ne_of_gt enrichedTfvdTaylorZeroZeroDefect_pos

/-- The real part of the enriched zeroth Gram is strictly larger than the
canonical native zeroth moment. -/
theorem enrichedTfvdTaylor_zero_zero_gram_re_gt_native :
    canonicalCompletedNativeLogDerivativeMoment 0 <
      (inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)).re := by
  have hdef := enrichedTfvdTaylorZeroZeroDefect_pos
  unfold enrichedTfvdTaylorZeroZeroDefect at hdef
  linarith

/-- The enriched carrier therefore cannot realize the complex `(0,0)` moment
coefficient.  This is stronger than a failure of a real-part-only audit: the
complex equality itself is impossible. -/
theorem enrichedTfvdTaylor_zero_zero_ne_moment :
    inner ℂ
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
        (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) ≠
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  have hgt := enrichedTfvdTaylor_zero_zero_gram_re_gt_native
  rw [Complex.ofReal_re] at hr
  exact (ne_of_gt hgt) hr

/-- The full polarized coefficient-vector equation for the enriched carrier is
refuted already by its zeroth diagonal entry. -/
theorem not_hasPolarizedCoefficientVectorEquation_enrichedTfvdTaylor :
    ¬ HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet := by
  intro h
  have h00 := enrichedTfvdTaylorEquation_zero_zero h
  have hraw :
      inner ℂ
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0)
          (canonicalCompletedNativeTfvdEnrichedTaylorRawJet 0) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    rw [inner_canonicalCompletedNativeTfvdEnrichedTaylorRawJet]
    exact h00
  exact enrichedTfvdTaylor_zero_zero_ne_moment hraw

end
end CarrySelfAdjointOperator
