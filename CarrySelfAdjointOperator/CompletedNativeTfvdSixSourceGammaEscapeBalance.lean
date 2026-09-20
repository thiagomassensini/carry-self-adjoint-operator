import CarrySelfAdjointOperator.CompletedC3CompressedGammaGramCorrection
import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import Mathlib.Tactic

/-!
# Polarized Cauchy--Gamma-escape balance for the six-source defect route

The completed Gamma response admits two exact decompositions in the same
complex Naimark Hilbert space:

* `Gamma = projectedPort + escape`;
* `resolvedCorrection = ambientPortDifference - escape`.

This module records the two-parameter balance that is left after retaining
these channels literally.  It does not assert that the balance is positive,
Hermitian, or equal to the Pick defect.  Those are separate questions.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- Polarized Cauchy--escape balance.  The first summand is the port/Cauchy
cross channel after the resolvent; the second is the honest Gamma escape
Gram.  The convention follows `inner ℂ`, hence the spectral parameter in the
first slot is conjugate-linear. -/
def canonicalCompletedC3GammaCauchyEscapeBalanceKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3ProjectedGammaPortState z hz)
      (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) -
    inner ℂ
      (canonicalCompletedC3GammaPortEscapeState z hz)
      (canonicalCompletedC3GammaPortEscapeState w hw)

/-- The diagonal real part is exactly the pre-existing Cauchy-port excess
minus the positive Gamma-escape energy.  This validates the orientation of
the polarized kernel without making a diagonal identity look polarized. -/
theorem canonicalCompletedC3GammaCauchyEscapeBalanceKernel_diagonal_re
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3GammaCauchyEscapeBalanceKernel
      z z hz hz hzHalf).re =
      (inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState
          z hz hzHalf)).re -
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  have hnorm :
      (inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3GammaPortEscapeState z hz)).re =
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ)
        (canonicalCompletedC3GammaPortEscapeState z hz)).symm
  unfold canonicalCompletedC3GammaCauchyEscapeBalanceKernel
  rw [Complex.sub_re, hnorm]

/-- Vanishing of the diagonal real balance is precisely the existing
response-level Pythagorean condition. -/
theorem canonicalCompletedC3GammaCauchyEscapeBalanceKernel_diagonal_re_eq_zero_iff
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3GammaCauchyEscapeBalanceKernel
      z z hz hz hzHalf).re = 0 ↔
      ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            z hz hzHalf‖ ^ 2 := by
  rw [canonicalCompletedC3GammaCauchyEscapeBalanceKernel_diagonal_re,
    canonicalCompletedC3AmbientResponse_pythagoras_iff_portBalance]
  constructor <;> intro h <;> nlinarith

/-- Polarized camera realization of the port side of the balance.  This is
proved directly from the common Naimark port, rather than by extrapolating
the previously available diagonal statement. -/
theorem inner_projectedGammaPort_ambientPortDifference_eq_cauchyCamera_polarized
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) =
      inner ℂ
        (canonicalCompletedC3GammaCameraView
          (NativeCarrySpectralWeyl.Infinite.allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter w) hwHalf -
            NativeCarrySpectralWeyl.Infinite.allBasesCauchyBlock w hw
              (canonicalCompletedC3SixCameraSource w))) := by
  rw [canonicalCompletedC3ProjectedGammaPortState_eq_cauchyPort]
  unfold canonicalCompletedC3AmbientPortDifferenceState
    canonicalCompletedC3AmbientResponseState
    completedC3SymplecticNaimarkState
  rw [canonicalCompletedC3ProjectedGammaPortState_eq_cauchyPort]
  simp only [← canonicalCompletedC3GammaNaimarkView_sub, ← map_sub]
  rw [inner_complex_gammaNaimarkView_port_port]

/-- The balance is literally the Cauchy-camera cross channel after the
resolvent, less the full Gamma-escape Gram. -/
theorem canonicalCompletedC3GammaCauchyEscapeBalanceKernel_eq_cauchyCamera_sub_escape
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCauchyEscapeBalanceKernel
        z w hz hw hwHalf =
      inner ℂ
        (canonicalCompletedC3GammaCameraView
          (NativeCarrySpectralWeyl.Infinite.allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter w) hwHalf -
            NativeCarrySpectralWeyl.Infinite.allBasesCauchyBlock w hw
              (canonicalCompletedC3SixCameraSource w))) -
        inner ℂ
          (canonicalCompletedC3GammaPortEscapeState z hz)
          (canonicalCompletedC3GammaPortEscapeState w hw) := by
  unfold canonicalCompletedC3GammaCauchyEscapeBalanceKernel
  rw [inner_projectedGammaPort_ambientPortDifference_eq_cauchyCamera_polarized
    z w hz hw hwHalf]

/-- The only possible failure of Hermiticity of the balance is the
port/difference skew channel.  The escape Gram cancels identically here. -/
theorem canonicalCompletedC3GammaCauchyEscapeBalanceKernel_swap_sub_conj
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCauchyEscapeBalanceKernel z w hz hw hwHalf -
      conj (canonicalCompletedC3GammaCauchyEscapeBalanceKernel
        w z hw hz hzHalf) =
      inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) -
      inner ℂ
        (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf)
        (canonicalCompletedC3ProjectedGammaPortState w hw) := by
  unfold canonicalCompletedC3GammaCauchyEscapeBalanceKernel
  rw [map_sub, inner_conj_symm, inner_conj_symm]
  ring

/-- The diagonal imaginary part is not silently discarded: it is exactly
the imaginary part of the Cauchy-port cross channel.  Consequently neither
diagonal reality nor Hermiticity follows from projection orthogonality alone. -/
theorem canonicalCompletedC3GammaCauchyEscapeBalanceKernel_diagonal_im
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3GammaCauchyEscapeBalanceKernel
      z z hz hz hzHalf).im =
      (inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf)).im := by
  unfold canonicalCompletedC3GammaCauchyEscapeBalanceKernel
  rw [Complex.sub_im]
  have hnormim :
      (inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3GammaPortEscapeState z hz)).im = 0 := by
    simpa only [RCLike.im_eq_complex_im] using
      (inner_self_im (𝕜 := ℂ)
        (canonicalCompletedC3GammaPortEscapeState z hz))
  rw [hnormim, sub_zero]

/-- Polarized logarithmic-leak scaling.  This records the exact
`conj z * w` factor that may later be needed to meet a resolvent spectral
separation; it makes no positivity assertion. -/
theorem inner_canonicalCompletedC3GammaLogarithmicLeak_eq_conj_mul_mul_inner_escape
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    inner ℂ
        (canonicalCompletedC3GammaLogarithmicLeakState z hz)
        (canonicalCompletedC3GammaLogarithmicLeakState w hw) =
      conj z * w *
        inner ℂ
          (canonicalCompletedC3GammaPortEscapeState z hz)
          (canonicalCompletedC3GammaPortEscapeState w hw) := by
  rw [canonicalCompletedC3GammaLogarithmicLeakState_eq_smul_escape,
    canonicalCompletedC3GammaLogarithmicLeakState_eq_smul_escape,
    inner_smul_left, inner_smul_right]
  ring

/-! ## Literal Gamma--correction polarization -/

/-- Orthogonality of a projected Gamma port at `z` against the escape of an
independent Gamma response at `w`.  This is the fully polarized form of the
orthogonal-projection/complement law; it has no diagonal specialization. -/
theorem inner_canonicalCompletedC3ProjectedGammaPort_gammaEscape_eq_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3GammaPortEscapeState w hw) = 0 := by
  exact inner_canonicalCompletedC3AmbientPortProjection_sub_eq_zero
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3PolarizedGammaState w hw)

/-- The ambient port difference at `z` is orthogonal to the independent
Gamma escape at `w`.  Both pieces of the difference lie in the projected
Naimark port before the second argument is projected away. -/
theorem inner_canonicalCompletedC3AmbientPortDifference_gammaEscape_eq_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    inner ℂ
        (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf)
        (canonicalCompletedC3GammaPortEscapeState w hw) = 0 := by
  have hambient :
      inner ℂ
          (canonicalCompletedC3AmbientResponseState z hzHalf)
          (canonicalCompletedC3GammaPortEscapeState w hw) = 0 := by
    rw [show canonicalCompletedC3AmbientResponseState z hzHalf =
        canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3AmbientPortProjection
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter z) hzHalf)) by
      unfold canonicalCompletedC3AmbientResponseState
      rw [canonicalCompletedC3AmbientPortProjection_completedSymplecticState]]
    exact inner_canonicalCompletedC3AmbientPortProjection_sub_eq_zero
      (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hzHalf)
      (canonicalCompletedC3PolarizedGammaState w hw)
  have hport :=
    inner_canonicalCompletedC3ProjectedGammaPort_gammaEscape_eq_zero
      z w hz hw
  unfold canonicalCompletedC3AmbientPortDifferenceState
  rw [inner_sub_left, hambient, hport, sub_zero]

/-- Reversing the preceding polarized orthogonality gives the exact second
mixed term that occurs in the Gamma--correction expansion. -/
theorem inner_canonicalCompletedC3GammaEscape_ambientPortDifference_eq_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) = 0 := by
  exact inner_eq_zero_symm.mp
    (inner_canonicalCompletedC3AmbientPortDifference_gammaEscape_eq_zero
      w z hw hz hwHalf)

/-- The two mixed terms left by the literal four-term expansion of the
Gamma--correction kernel.  It is named before being simplified so the
geometric content of the polarization remains inspectable. -/
def canonicalCompletedC3GammaEscapeCrossDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  - inner ℂ
      (canonicalCompletedC3ProjectedGammaPortState z hz)
      (canonicalCompletedC3GammaPortEscapeState w hw) +
    inner ℂ
      (canonicalCompletedC3GammaPortEscapeState z hz)
      (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf)

/-- Literal, unsimplified four-channel expansion of the old
Gamma--resolved-correction kernel.  The order of the inner-product arguments
matches the complex convention fixed by `inner ℂ`. -/
theorem canonicalCompletedC3GammaCorrectionKernel_eq_four_channel_expansion
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf =
      inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) -
      inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3GammaPortEscapeState w hw) +
      inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState w hw hwHalf) -
      inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3GammaPortEscapeState w hw) := by
  unfold canonicalCompletedC3GammaCorrectionKernel
  rw [canonicalCompletedC3PolarizedGammaState_eq_port_add_escape z hz,
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState_eq_portDifference_sub_escape
      w hw hwHalf,
    inner_add_left, inner_sub_right, inner_sub_right]
  ring

/-- The four-channel expansion is the balance kernel plus the explicitly
named mixed-channel residual. -/
theorem canonicalCompletedC3GammaCorrectionKernel_eq_gammaCauchyEscapeBalance_add_crossDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf =
      canonicalCompletedC3GammaCauchyEscapeBalanceKernel z w hz hw hwHalf +
        canonicalCompletedC3GammaEscapeCrossDefect z w hz hw hwHalf := by
  rw [canonicalCompletedC3GammaCorrectionKernel_eq_four_channel_expansion]
  unfold canonicalCompletedC3GammaCauchyEscapeBalanceKernel
    canonicalCompletedC3GammaEscapeCrossDefect
  ring

/-- The mixed-channel residual vanishes for every regular pair `(z,w)`, not
merely on the diagonal.  The cancellation is a projection fact, not a
positivity or Pick argument. -/
theorem canonicalCompletedC3GammaEscapeCrossDefect_eq_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaEscapeCrossDefect z w hz hw hwHalf = 0 := by
  unfold canonicalCompletedC3GammaEscapeCrossDefect
  rw [inner_canonicalCompletedC3ProjectedGammaPort_gammaEscape_eq_zero
      z w hz hw,
    inner_canonicalCompletedC3GammaEscape_ambientPortDifference_eq_zero
      z w hz hw hwHalf]
  ring

/-- Therefore the Gamma--correction kernel is exactly the polarized
Cauchy--escape balance at arbitrary regular pairs.  This identifies an old
kernel name for the residual without turning it into a positive Gram. -/
theorem canonicalCompletedC3GammaCorrectionKernel_eq_gammaCauchyEscapeBalance
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf =
      canonicalCompletedC3GammaCauchyEscapeBalanceKernel
        z w hz hw hwHalf := by
  rw [canonicalCompletedC3GammaCorrectionKernel_eq_gammaCauchyEscapeBalance_add_crossDefect,
    canonicalCompletedC3GammaEscapeCrossDefect_eq_zero, add_zero]

end

end CarrySelfAdjointOperator
