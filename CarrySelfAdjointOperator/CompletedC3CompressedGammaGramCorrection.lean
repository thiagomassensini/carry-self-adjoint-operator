import CarrySelfAdjointOperator.CompletedC3TfvdResolventTraceBridge
import Mathlib.Tactic

/-!
# Compressed C3 Gram versus the canonical Gamma Gram

The completed compressed state and the canonical Gamma state are not
identified by assumption.  The former is the all-cutoff ambient response;
the latter is the logarithmic resolvent response to the canonical TFVD source.
The exact source correction constructed previously therefore gives an exact
polarized expansion of their Gram difference.

This module keeps the three resulting Hilbert channels separate: Gamma against
correction, correction against Gamma, and correction against correction.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The all-cutoff ambient response in the canonical complex Naimark Hilbert
structure. -/
def canonicalCompletedC3AmbientResponseState
    (z : ℂ) (hs : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (completedC3SymplecticNaimarkState (operatorHeightParameter z) hs)

/-- The resolved ambient-to-TFVD source correction in the same complex
Naimark Hilbert structure. -/
def canonicalCompletedC3AmbientTfvdResolvedCorrectionState
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (realifiedLogarithmicDomainEmbedding
      (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hs))

/-- Embedding the canonical TFVD maximal-domain response gives literally the
canonical positive Gamma state. -/
theorem canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaNaimarkView
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdResolventDomainVector z hz)) =
      canonicalCompletedC3PolarizedGammaState z hz := by
  rw [canonicalCompletedC3TfvdResolventDomainVector_eq_gamma]
  rfl

/-- Exact vector identity in one complex Hilbert carrier. -/
theorem canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientResponseState z hs =
      canonicalCompletedC3PolarizedGammaState z hz +
        canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hs := by
  unfold canonicalCompletedC3AmbientResponseState
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState
  rw [← canonicalCompletedC3AmbientResolventDomainVector_embedding z hz hs,
    canonicalCompletedC3AmbientResolventDomainVector_eq_tfvd_add_correction,
    map_add, canonicalCompletedC3GammaNaimarkView_add,
    canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState]

/-- Polarized Gram kernel of the full ambient all-cutoff responses. -/
def canonicalCompletedC3AmbientResponseKernel
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
    (canonicalCompletedC3AmbientResponseState z hzHalf)
    (canonicalCompletedC3AmbientResponseState w hwHalf)

/-- Gamma in the first slot and the resolved correction in the second. -/
def canonicalCompletedC3GammaCorrectionKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3AmbientTfvdResolvedCorrectionState w hw hwHalf)

/-- Resolved correction in the first slot and Gamma in the second. -/
def canonicalCompletedC3CorrectionGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) : ℂ :=
  inner ℂ
    (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hzHalf)
    (canonicalCompletedC3PolarizedGammaState w hw)

/-- Polarized Gram kernel of the resolved correction itself. -/
def canonicalCompletedC3CorrectionKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
    (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hzHalf)
    (canonicalCompletedC3AmbientTfvdResolvedCorrectionState w hw hwHalf)

/-! ## Division-free boundary realization of the cross channels -/

/-- The Gamma--correction cross channel is the full ambient boundary skew of
the canonical TFVD response against the resolved source correction. -/
theorem canonicalCompletedC3AmbientDefectBoundary_tfvd_correction_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3AmbientTfvdResolvedCorrection w hw hwHalf) =
      (w - conj z) *
        canonicalCompletedC3GammaCorrectionKernel
          z w hz hw hwHalf := by
  rw [canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3GammaCorrectionKernel
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState
  rw [canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState]

/-- The reverse correction--Gamma cross channel is likewise an exact ambient
boundary skew, with no division by the spectral separation. -/
theorem canonicalCompletedC3AmbientDefectBoundary_correction_tfvd_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hzHalf)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) =
      (w - conj z) *
        canonicalCompletedC3CorrectionGammaKernel
          z w hz hw hzHalf := by
  rw [canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3CorrectionGammaKernel
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState
  rw [canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState]

/-- The positive correction Gram is also represented by the ambient boundary
skew of the resolved correction against itself. -/
theorem canonicalCompletedC3AmbientDefectBoundary_correction_correction_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hzHalf)
        (canonicalCompletedC3AmbientTfvdResolvedCorrection w hw hwHalf) =
      (w - conj z) *
        canonicalCompletedC3CorrectionKernel
          z w hz hw hzHalf hwHalf := by
  rw [canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel]
  rfl

/-- Polarizing the exact state factorization produces all three correction
channels, with no omitted cross term. -/
theorem canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf =
      canonicalCompletedC3PolarizedGammaKernel z w hz hw +
        canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf +
        canonicalCompletedC3CorrectionGammaKernel z w hz hw hzHalf +
        canonicalCompletedC3CorrectionKernel
          z w hz hw hzHalf hwHalf := by
  unfold canonicalCompletedC3AmbientResponseKernel
    canonicalCompletedC3PolarizedGammaKernel
    canonicalCompletedC3GammaCorrectionKernel
    canonicalCompletedC3CorrectionGammaKernel
    canonicalCompletedC3CorrectionKernel
  rw [canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
      z hz hzHalf,
    canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
      w hw hwHalf,
    inner_add_left, inner_add_right, inner_add_right]
  ring

/-- The direct compressed camera Gram is exactly the ambient-response Gram,
because the Naimark port is an isometry on both retained quadratures. -/
theorem inner_completedC3SymplecticCameraState_eq_ambientResponseKernel
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
            (operatorHeightParameter z) hzHalf))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
            (operatorHeightParameter w) hwHalf)) =
      canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf := by
  unfold canonicalCompletedC3AmbientResponseKernel
    canonicalCompletedC3AmbientResponseState
    completedC3SymplecticNaimarkState
  exact
    (inner_complex_gammaNaimarkView_port_port
      (completedC3SymplecticCameraState
        (operatorHeightParameter z) hzHalf)
      (completedC3SymplecticCameraState
        (operatorHeightParameter w) hwHalf)).symm

/-- Exact Hilbert expansion of the concrete Gram difference isolated by the
boundary correction ledger. -/
theorem canonicalCompletedC3CompressedGram_sub_gamma_eq_threeHilbertChannels
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter z) (operatorHeightParameter w) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter z) (operatorHeightParameter w)
          hzHalf hwHalf).re : ℂ) -
        canonicalCompletedC3PolarizedGammaKernel z w hz hw =
      canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf +
        canonicalCompletedC3CorrectionGammaKernel z w hz hw hzHalf +
        canonicalCompletedC3CorrectionKernel
          z w hz hw hzHalf hwHalf := by
  rw [← inner_completedC3SymplecticCameraState_eq_compressedCoefficient,
    inner_completedC3SymplecticCameraState_eq_ambientResponseKernel,
    canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections
      z w hz hw hzHalf hwHalf]
  ring

/-- On the diagonal, the correction--Gamma channel is the conjugate of the
Gamma--correction channel. -/
theorem canonicalCompletedC3CorrectionGammaKernel_diagonal_eq_conj
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CorrectionGammaKernel z z hz hz hzHalf =
      conj (canonicalCompletedC3GammaCorrectionKernel
        z z hz hz hzHalf) := by
  unfold canonicalCompletedC3CorrectionGammaKernel
    canonicalCompletedC3GammaCorrectionKernel
  exact (inner_conj_symm _ _).symm

/-- The diagonal correction kernel is exactly the squared norm of the
resolved correction state. -/
theorem canonicalCompletedC3CorrectionKernel_diagonal_eq_norm_sq
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CorrectionKernel
        z z hz hz hzHalf hzHalf =
      ((‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf‖ : ℝ) : ℂ) ^ 2 := by
  unfold canonicalCompletedC3CorrectionKernel
  exact inner_self_eq_norm_sq_to_K
    (𝕜 := ℂ)
    (canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hzHalf)

/-- The complex Hilbert correction state vanishes exactly when its full
ambient source correction vanishes. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrectionState_eq_zero_iff_source
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hzHalf = 0 ↔
      canonicalCompletedC3AmbientTfvdSourceCorrection z hzHalf = 0 := by
  constructor
  · intro hstate
    have hembedding :
        realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hzHalf) =
          0 := by
      change canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3AmbientTfvdResolvedCorrection
              z hz hzHalf)) = 0 at hstate
      exact hstate
    have hdomain :
        canonicalCompletedC3AmbientTfvdResolvedCorrection z hz hzHalf = 0 := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg WithLp.fst hembedding
      · apply Subtype.ext
        exact congrArg WithLp.snd hembedding
    exact
      (canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_zero_iff_source
        z hz hzHalf).mp hdomain
  · intro hsource
    have hdomain :=
      (canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_zero_iff_source
        z hz hzHalf).mpr hsource
    unfold canonicalCompletedC3AmbientTfvdResolvedCorrectionState
    rw [hdomain, map_zero]
    rfl

/-- A nonzero source correction gives a strictly positive diagonal correction
Gram.  This uses resolvent injectivity and Hilbert positivity only. -/
theorem canonicalCompletedC3CorrectionKernel_diagonal_re_pos_of_source_ne_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hsource : canonicalCompletedC3AmbientTfvdSourceCorrection
      z hzHalf ≠ 0) :
    0 < (canonicalCompletedC3CorrectionKernel
      z z hz hz hzHalf hzHalf).re := by
  rw [canonicalCompletedC3CorrectionKernel_diagonal_eq_norm_sq]
  have hstate :
      canonicalCompletedC3AmbientTfvdResolvedCorrectionState
          z hz hzHalf ≠ 0 := by
    exact
      (not_congr
        (canonicalCompletedC3AmbientTfvdResolvedCorrectionState_eq_zero_iff_source
          z hz hzHalf)).mpr hsource
  have hnorm :
      0 < ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf‖ := norm_pos_iff.mpr hstate
  norm_num [pow_two, Complex.mul_re]
  positivity

/-- Real diagonal form of the Gram correction.  This displays the only
possible cancellation: the positive correction norm can be offset only by
the real Gamma--correction cross channel. -/
theorem canonicalCompletedC3CompressedGram_sub_gamma_diagonal_re
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter z) (operatorHeightParameter z) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter z) (operatorHeightParameter z)
          hzHalf hzHalf).re : ℂ) -
        canonicalCompletedC3PolarizedGammaKernel z z hz hz).re =
      2 * (canonicalCompletedC3GammaCorrectionKernel
        z z hz hz hzHalf).re +
        ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
          z hz hzHalf‖ ^ 2 := by
  have h := congrArg Complex.re
    (canonicalCompletedC3CompressedGram_sub_gamma_eq_threeHilbertChannels
      z z hz hz hzHalf hzHalf)
  rw [canonicalCompletedC3CorrectionGammaKernel_diagonal_eq_conj,
    canonicalCompletedC3CorrectionKernel_diagonal_eq_norm_sq] at h
  simp only [Complex.add_re, Complex.conj_re] at h
  norm_num [pow_two, Complex.mul_re] at h
  norm_num [pow_two, Complex.mul_re]
  nlinarith

end

end CarrySelfAdjointOperator
