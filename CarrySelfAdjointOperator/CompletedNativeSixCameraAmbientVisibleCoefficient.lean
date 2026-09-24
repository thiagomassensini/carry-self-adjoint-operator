import CarrySelfAdjointOperator.CompletedNativeSixCameraAmbientEnergyTest
import Mathlib.Tactic

/-!
# Finite-coordinate formula for the ambient six-camera visible channel

The historical six-camera projection already gives an exact visible/halo
Pythagorean splitting of the normalized ambient response.  Its remaining
central test was left as the Hilbert-space equality

`‖visible 0‖² = h₀`.

This module removes one more layer from that test.  The visible pairing is
exactly the Hermitian pairing of the two six-coordinate whitened analyses of
the realified ambient state.  In particular, the central visible energy is a
finite sum of twelve real squares.  No moment equality, positivity premise,
or fitted factorization is used.
-/

open scoped BigOperators InnerProductSpace Matrix

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Whitened six-camera coefficients of the first real quadrature of the
actual normalized ambient state. -/
def canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) : Fin 6 → ℝ :=
  sixCameraWhitenedNaimarkAnalysis
    (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).fst

/-- Whitened six-camera coefficients of the second real quadrature of the
actual normalized ambient state. -/
def canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) : Fin 6 → ℝ :=
  sixCameraWhitenedNaimarkAnalysis
    (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).snd

/-- The orthogonal six-camera projection pairing is exactly the Euclidean
pairing of its whitened analysis coordinates. -/
theorem inner_sixCameraWhitenedNaimarkProjectionCLM_eq_analysis
    (x y : NaimarkSpace) :
    inner ℝ (sixCameraWhitenedNaimarkProjectionCLM x)
        (sixCameraWhitenedNaimarkProjectionCLM y) =
      sixCameraWhitenedNaimarkAnalysis x ⬝ᵥ
        sixCameraWhitenedNaimarkAnalysis y := by
  rw [sixCameraWhitenedNaimarkProjectionCLM_apply,
    sixCameraWhitenedNaimarkProjectionCLM_apply]
  unfold sixCameraWhitenedNaimarkProjection
  exact sixCameraWhitenedNaimarkSynthesis_inner _ _

/-- The full polarized visible kernel is a finite six-coordinate Hermitian
pairing.  This is the concrete coefficient formula behind the historical
six-camera projection. -/
theorem inner_canonicalCompletedC3NormalizedAmbientSixCameraVisibleState_eq_analysis
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ
        (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState z hzHalf)
        (canonicalCompletedC3NormalizedAmbientSixCameraVisibleState w hwHalf) =
      ((canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis z hzHalf ⬝ᵥ
          canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis w hwHalf +
        canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis z hzHalf ⬝ᵥ
          canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis w hwHalf : ℝ) : ℂ) +
      Complex.I *
        ((canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis z hzHalf ⬝ᵥ
            canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis w hwHalf -
          canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis z hzHalf ⬝ᵥ
            canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis w hwHalf : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [canonicalCompletedC3NormalizedAmbientSixCameraVisibleState,
      canonicalCompletedC3GammaNaimarkView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, Complex.ofReal_im, sub_zero]
    rw [WithLp.ofLp_fst, WithLp.ofLp_fst,
      WithLp.ofLp_snd, WithLp.ofLp_snd]
    rw [canonicalCompletedC3SixCameraProjection_fst,
      canonicalCompletedC3SixCameraProjection_fst,
      canonicalCompletedC3SixCameraProjection_snd,
      canonicalCompletedC3SixCameraProjection_snd]
    change
      inner ℝ
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).fst)
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState w hwHalf).fst) +
        inner ℝ
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).snd)
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState w hwHalf).snd) = _
    rw [inner_sixCameraWhitenedNaimarkProjectionCLM_eq_analysis,
      inner_sixCameraWhitenedNaimarkProjectionCLM_eq_analysis]
    simp [canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis,
      canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis]
  · simp only [canonicalCompletedC3NormalizedAmbientSixCameraVisibleState,
      canonicalCompletedC3GammaNaimarkView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, Complex.ofReal_re, zero_add]
    rw [WithLp.ofLp_fst, WithLp.ofLp_snd,
      WithLp.ofLp_snd, WithLp.ofLp_fst]
    rw [canonicalCompletedC3SixCameraProjection_fst,
      canonicalCompletedC3SixCameraProjection_snd,
      canonicalCompletedC3SixCameraProjection_snd,
      canonicalCompletedC3SixCameraProjection_fst]
    change
      inner ℝ
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).fst)
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState w hwHalf).snd) -
        inner ℝ
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState z hzHalf).snd)
          (sixCameraWhitenedNaimarkProjectionCLM
            (canonicalCompletedC3NormalizedAmbientRealifiedState w hwHalf).fst) = _
    rw [inner_sixCameraWhitenedNaimarkProjectionCLM_eq_analysis,
      inner_sixCameraWhitenedNaimarkProjectionCLM_eq_analysis]
    simp [canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis,
      canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis]

/-- At the center, the visible energy is the sum of the Euclidean energies
of the two concrete whitened six-camera coefficient vectors. -/
theorem norm_sq_canonicalCompletedC3NormalizedAmbientSixCameraVisibleState_zero_eq_analysis :
    ‖canonicalCompletedC3NormalizedAmbientSixCameraVisibleState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 =
      canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis 0
          (by norm_num [operatorHeightParameter]) ⬝ᵥ
        canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis 0
          (by norm_num [operatorHeightParameter]) +
      canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis 0
          (by norm_num [operatorHeightParameter]) ⬝ᵥ
        canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis 0
          (by norm_num [operatorHeightParameter]) := by
  have h :=
    inner_canonicalCompletedC3NormalizedAmbientSixCameraVisibleState_eq_analysis
      0 0 (by norm_num [operatorHeightParameter])
      (by norm_num [operatorHeightParameter])
  have hreal := congrArg Complex.re h
  rw [inner_self_eq_norm_sq_to_K] at hreal
  simpa [pow_two, dotProduct_comm] using hreal

/-- Fully finite-coordinate form of the sole central gate for the concrete
ambient six-camera proposal. -/
theorem canonicalCompletedC3SixCameraHorizontal_central_energy_eq_excess_iff_analysis :
    ‖canonicalCompletedC3NormalizedAmbientSixCameraHorizontalState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 =
      canonicalCompletedC3NormalizedAmbientCentralExcess ↔
    canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis 0
          (by norm_num [operatorHeightParameter]) ⬝ᵥ
        canonicalCompletedC3NormalizedAmbientSixCameraFstAnalysis 0
          (by norm_num [operatorHeightParameter]) +
      canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis 0
          (by norm_num [operatorHeightParameter]) ⬝ᵥ
        canonicalCompletedC3NormalizedAmbientSixCameraSndAnalysis 0
          (by norm_num [operatorHeightParameter]) =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [canonicalCompletedC3SixCameraHorizontal_central_energy_eq_excess_iff,
    norm_sq_canonicalCompletedC3NormalizedAmbientSixCameraVisibleState_zero_eq_analysis]

end

end CarrySelfAdjointOperator
