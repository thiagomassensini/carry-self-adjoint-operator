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
open Filter
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

/-! ## Source-level form of the Gamma--correction channel -/

/-- The concrete source skew pairing the canonical TFVD/Gamma response with
the full ambient-to-TFVD source correction. -/
def canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3PolarizedGammaState z hz)
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientTfvdSourceCorrection w hwHalf)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)))
      (canonicalCompletedC3AmbientTfvdResolvedCorrectionState w hw hwHalf)

/-- Expanding both exact defect equations identifies the ambient cross
boundary with the concrete TFVD-source/source-correction skew. -/
theorem canonicalCompletedC3AmbientDefectBoundary_tfvd_correction_eq_source
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3AmbientTfvdResolvedCorrection w hw hwHalf) =
      canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z w hz hw hwHalf := by
  unfold canonicalCompletedC3AmbientDefectBoundaryReadout
    canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState
  rw [canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState]
  simp only [canonicalCompletedC3AmbientTfvdResolvedCorrection,
    canonicalCompletedC3TfvdResolventDomainVector,
    realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]

/-- Division-free source realization of the Gamma--correction kernel. -/
theorem canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z w hz hw hwHalf =
      (w - conj z) *
        canonicalCompletedC3GammaCorrectionKernel
          z w hz hw hwHalf := by
  rw [← canonicalCompletedC3AmbientDefectBoundary_tfvd_correction_eq_source]
  exact canonicalCompletedC3AmbientDefectBoundary_tfvd_correction_eq_kernel
    z w hz hw hwHalf

/-- On the diagonal, the imaginary part of the source boundary skew is
exactly twice the spectral imaginary coordinate times the real cross Gram.
This is the division-free form needed for a cancellation audit. -/
theorem canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_diagonal_im
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z z hz hz hzHalf).im =
      2 * z.im *
        (canonicalCompletedC3GammaCorrectionKernel
          z z hz hz hzHalf).re := by
  have h := congrArg Complex.im
    (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_eq_kernel
      z z hz hz hzHalf)
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im] at h
  nlinarith

/-! ## Finite-cutoff source boundary and its strong limit -/

/-- The finite induced logarithmic source minus the same canonical TFVD
source used by the completed Gamma response. -/
def canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) : RealifiedNaimarkComplexification :=
  canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
      hbase cutoff z -
    realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)

/-- Resolve the finite source correction in the same ambient logarithmic
resolvent and view it in the canonical complex Hilbert structure. -/
def canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (realifiedLogarithmicDomainEmbedding
      (logarithmicResolventIntoDomain z hz
        (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
          hbase cutoff z)))

/-- The finite resolved correction is exactly the finite TFVD state minus
the canonical Gamma state.  This uses the resolvent left inverse, not a norm
or scalar boundary argument. -/
theorem canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState_eq_sub
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
        hbase cutoff z hz =
      canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3CausalResponseBoundaryDomainVector
              hbase cutoff (operatorHeightParameter z))) -
        canonicalCompletedC3PolarizedGammaState z hz := by
  unfold canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
    canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
    canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
  rw [map_sub,
    logarithmicResolvent_apply_realifiedLambdaMinus,
    map_sub, canonicalCompletedC3GammaNaimarkView_sub]
  change _ -
      canonicalCompletedC3GammaNaimarkView
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdResolventDomainVector z hz)) = _
  rw [canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState]

/-- The finite source corrections converge strongly to the completed source
correction. -/
theorem canonicalCompletedC3FiniteAmbientTfvdSourceCorrection_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3AmbientTfvdSourceCorrection z hzHalf)) := by
  simpa [canonicalCompletedC3FiniteAmbientTfvdSourceCorrection,
    canonicalCompletedC3AmbientTfvdSourceCorrection] using
    (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_tendsto_ambientLimit
      hbase z hzHalf).sub_const
        (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z))

/-- Boundedness of the ambient resolvent transports the finite source limit
to the resolved correction states. -/
theorem canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
          hbase cutoff z hz)
      atTop
      (nhds (canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf)) := by
  have hsource :=
    canonicalCompletedC3FiniteAmbientTfvdSourceCorrection_tendsto
      hbase z hzHalf
  have hresolved :=
    (logarithmicResolventBlock z hz).continuous.continuousAt.tendsto.comp
      hsource
  change Tendsto
    (fun cutoff : ℕ =>
      logarithmicResolventBlock z hz
        (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
          hbase cutoff z))
    atTop
    (nhds (logarithmicResolventBlock z hz
      (canonicalCompletedC3AmbientTfvdSourceCorrection z hzHalf)))
  exact hresolved

/-- Finite source-boundary skew in precisely the same orientation as the
completed Gamma--correction source readout. -/
def canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ
      (canonicalCompletedC3PolarizedGammaState z hz)
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
          hbase cutoff w)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)))
      (canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
        hbase cutoff w hw)

/-- At every cutoff, the finite source-boundary skew is spectral separation
times the Gamma/finite-correction cross Gram. -/
theorem canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_eq_kernel
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
        hbase cutoff z w hz hw =
      (w - conj z) *
        inner ℂ
          (canonicalCompletedC3PolarizedGammaState z hz)
          (canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
            hbase cutoff w hw) := by
  let correctionW : RealifiedLogarithmicDomain :=
    logarithmicResolventIntoDomain w hw
      (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
        hbase cutoff w)
  have hboundary :=
    canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel
      z w (canonicalCompletedC3TfvdResolventDomainVector z hz) correctionW
  unfold canonicalCompletedC3AmbientDefectBoundaryReadout at hboundary
  rw [canonicalCompletedC3TfvdResolventDomainVector_embedding_eq_gammaState
    z hz] at hboundary
  have htfvdSource :
      realifiedLambdaMinusLogarithmicMultiplication z
          (canonicalCompletedC3TfvdResolventDomainVector z hz) =
        realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z) := by
    unfold canonicalCompletedC3TfvdResolventDomainVector
    rw [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]
  rw [htfvdSource] at hboundary
  simp only [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent,
    correctionW] at hboundary
  unfold canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
    canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
  exact hboundary

/-- Finite-cutoff diagonal form of the source-boundary identity. -/
theorem canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_diagonal_im
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
        hbase cutoff z z hz hz).im =
      2 * z.im *
        (inner ℂ
          (canonicalCompletedC3PolarizedGammaState z hz)
          (canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
            hbase cutoff z hz)).re := by
  have h := congrArg Complex.im
    (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_eq_kernel
      hbase cutoff z z hz hz)
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im] at h
  nlinarith

/-- The finite source-boundary readouts converge to the completed concrete
source-boundary readout. -/
theorem canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
          hbase cutoff z w hz hw)
      atTop
      (nhds (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z w hz hw hwHalf)) := by
  have hsource :=
    canonicalCompletedC3FiniteAmbientTfvdSourceCorrection_tendsto
      hbase w hwHalf
  have hsourceView : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
            hbase cutoff w))
      atTop
      (nhds (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientTfvdSourceCorrection w hwHalf))) := by
    change Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3AmbientTfvdSourceCorrection w hwHalf))
    exact hsource
  have hresolved :=
    canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState_tendsto
      hbase w hw hwHalf
  have hfirst : Tendsto
      (fun cutoff : ℕ => inner ℂ
        (canonicalCompletedC3PolarizedGammaState z hz)
        (canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3FiniteAmbientTfvdSourceCorrection
            hbase cutoff w)))
      atTop
      (nhds (inner ℂ
        (canonicalCompletedC3PolarizedGammaState z hz)
        (canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3AmbientTfvdSourceCorrection w hwHalf)))) :=
    Filter.Tendsto.inner (𝕜 := ℂ) tendsto_const_nhds hsourceView
  have hsecond : Tendsto
      (fun cutoff : ℕ => inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)))
        (canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
          hbase cutoff w hw))
      atTop
      (nhds (inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)))
        (canonicalCompletedC3AmbientTfvdResolvedCorrectionState
          w hw hwHalf))) :=
    Filter.Tendsto.inner (𝕜 := ℂ) tendsto_const_nhds hresolved
  simpa [canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout,
    canonicalCompletedC3GammaCorrectionSourceBoundaryReadout] using
      hfirst.sub hsecond

/-- The finite diagonal cancellation balance, retaining both the source
boundary skew and the positive resolved-correction channel. -/
def canonicalCompletedC3FiniteGammaCorrectionBalance
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) (hz : z.im ≠ 0) : ℝ :=
  (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
      hbase cutoff z z hz hz).im +
    z.im *
      ‖canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
        hbase cutoff z hz‖ ^ 2

/-- The completed diagonal cancellation balance isolated by the exact
Gamma-correction decomposition. -/
def canonicalCompletedC3GammaCorrectionBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) : ℝ :=
  (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
      z z hz hz hzHalf).im +
    z.im *
      ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf‖ ^ 2

/-- At every cutoff, the cancellation balance is exactly the imaginary
spectral coordinate times the finite-TFVD/Gamma energy difference.  Thus the
remaining finite gate is an equality of two concrete state norms. -/
theorem canonicalCompletedC3FiniteGammaCorrectionBalance_eq_energyDifference
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3FiniteGammaCorrectionBalance hbase cutoff z hz =
      z.im *
        (‖canonicalCompletedC3GammaNaimarkView
            (realifiedLogarithmicDomainEmbedding
              (canonicalCompletedC3CausalResponseBoundaryDomainVector
                hbase cutoff (operatorHeightParameter z)))‖ ^ 2 -
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2) := by
  let finiteState : CarryGammaComplexNaimark :=
    canonicalCompletedC3GammaNaimarkView
      (realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3CausalResponseBoundaryDomainVector
          hbase cutoff (operatorHeightParameter z)))
  let gammaState : CarryGammaComplexNaimark :=
    canonicalCompletedC3PolarizedGammaState z hz
  let correctionState : CarryGammaComplexNaimark :=
    canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
      hbase cutoff z hz
  have hcorrection : correctionState = finiteState - gammaState := by
    exact canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState_eq_sub
      hbase cutoff z hz
  have hboundary :=
    canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_diagonal_im
      hbase cutoff z hz
  change
    (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
        hbase cutoff z z hz hz).im + z.im * ‖correctionState‖ ^ 2 =
      z.im * (‖finiteState‖ ^ 2 - ‖gammaState‖ ^ 2)
  change
    (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
        hbase cutoff z z hz hz).im =
      2 * z.im * (inner ℂ gammaState correctionState).re at hboundary
  rw [hboundary, hcorrection, norm_sub_sq (𝕜 := ℂ)]
  simp only [inner_sub_right, ← RCLike.re_eq_complex_re, map_sub,
    inner_self_eq_norm_sq]
  rw [inner_re_symm]
  ring

/-- The finite ambient TFVD energy is the ordinary carry-gradient prefix
energy with the radial first-leg factor exposed.  This is an isometric
packing computation and does not use a Green or Gamma sewing statement. -/
theorem canonicalCompletedC3FiniteAmbientTfvdEnergy_eq_prefix
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : ℕ) (z : ℂ) :
    ‖canonicalCompletedC3GammaNaimarkView
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3CausalResponseBoundaryDomainVector
            hbase cutoff (operatorHeightParameter z)))‖ ^ 2 =
      (completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
        ‖canonicalCompletedC3DirichletGradientPrefixState
          (operatorHeightParameter z)
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)‖ ^ 2 := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  let s := operatorHeightParameter z
  let x := NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair N s
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding]
  change (inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (finiteC3SymplecticNaimarkRealization N x))
      (canonicalCompletedC3GammaNaimarkView
        (finiteC3SymplecticNaimarkRealization N x))).re = _
  rw [show finiteC3SymplecticNaimarkRealization N x =
      realifiedNaimarkPort (finiteC3SymplecticCameraPacking N x) by rfl,
    inner_complex_gammaNaimarkView_port_port,
    inner_canonicalCompletedC3GammaCameraView_re]
  rw [finiteC3SymplecticCameraPacking_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, inner_neg_left,
    inner_neg_right, neg_neg]
  rw [finiteC3GenuineFirstLegCamera_eq_radial_completedPrefix,
    finiteC3GenuineSecondLegCamera_eq_completedPrefix]
  simp only [real_inner_self_eq_norm_sq]
  unfold completedC3LegCameraState
  simp only [norm_smul, completedC3GlobalLegCameraIsometry.norm_map,
    Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  dsimp [s, N]
  simp only [Nat.add_comm]
  ring

/-- Completed form of the same isometric packing computation. -/
theorem canonicalCompletedC3AmbientResponseEnergy_eq_gradient
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
      (completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
        ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter z) hzHalf‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  unfold canonicalCompletedC3AmbientResponseState
    completedC3SymplecticNaimarkState
  rw [inner_complex_gammaNaimarkView_port_port,
    RCLike.re_eq_complex_re,
    inner_canonicalCompletedC3GammaCameraView_re]
  unfold completedC3SymplecticCameraState
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, inner_neg_left,
    inner_neg_right, neg_neg, real_inner_self_eq_norm_sq]
  unfold completedC3LegCameraState
  simp only [norm_smul, completedC3GlobalLegCameraIsometry.norm_map,
    Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

/-- The same energy-difference identity after completion.  This is obtained
from the exact Hilbert-space state factorization, independently of the
finite-limit theorem. -/
theorem canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3GammaCorrectionBalance z hz hzHalf =
      z.im *
        (‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2) := by
  rw [canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
    z hz hzHalf]
  unfold canonicalCompletedC3GammaCorrectionBalance
  rw [canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_diagonal_im,
    norm_add_sq (𝕜 := ℂ)]
  unfold canonicalCompletedC3GammaCorrectionKernel
  simp only [← RCLike.re_eq_complex_re]
  ring

/-- Because the centered spectral coordinate is nonreal, vanishing of the
completed correction balance is exactly equality of the two canonical
energies. -/
theorem canonicalCompletedC3GammaCorrectionBalance_eq_zero_iff_energy
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3GammaCorrectionBalance z hz hzHalf = 0 ↔
      ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference]
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hz)
  · intro h
    rw [h, sub_self, mul_zero]

/-- Fully geometric spelling of the completed cancellation gate.  The left
energy is now an ordinary carry-gradient norm; the right energy remains the
canonical Gamma/Cauchy response norm. -/
theorem canonicalCompletedC3GammaCorrectionBalance_eq_zero_iff_gradientEnergy
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3GammaCorrectionBalance z hz hzHalf = 0 ↔
      (completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
          ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter z) hzHalf‖ ^ 2 =
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3GammaCorrectionBalance_eq_zero_iff_energy,
    canonicalCompletedC3AmbientResponseEnergy_eq_gradient]

/-- The exact finite cancellation balances converge to the completed
balance.  In particular, no nonzero finite channel is discarded when the
cutoff is removed. -/
theorem canonicalCompletedC3FiniteGammaCorrectionBalance_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteGammaCorrectionBalance
          hbase cutoff z hz)
      atTop
      (nhds (canonicalCompletedC3GammaCorrectionBalance z hz hzHalf)) := by
  have hboundaryComplex :=
    canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout_tendsto
      hbase z z hz hz hzHalf
  have hboundary : Tendsto
      (fun cutoff : ℕ =>
        (canonicalCompletedC3FiniteGammaCorrectionSourceBoundaryReadout
          hbase cutoff z z hz hz).im)
      atTop
      (nhds ((canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z z hz hz hzHalf).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp hboundaryComplex
  have hresolved :=
    canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState_tendsto
      hbase z hz hzHalf
  have hnormSq : Tendsto
      (fun cutoff : ℕ =>
        ‖canonicalCompletedC3FiniteAmbientTfvdResolvedCorrectionState
          hbase cutoff z hz‖ ^ 2)
      atTop
      (nhds (‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf‖ ^ 2)) :=
    hresolved.norm.pow 2
  simpa [canonicalCompletedC3FiniteGammaCorrectionBalance,
    canonicalCompletedC3GammaCorrectionBalance] using
      hboundary.add (hnormSq.const_mul z.im)

/-- Direct finite-to-completed passage for the concrete TFVD/Gamma energy
difference.  This is the scalar consequence of strong vector convergence;
there is no assumption that the limit vanishes. -/
theorem canonicalCompletedC3FiniteTfvdGammaEnergyDifference_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        z.im *
          (‖canonicalCompletedC3GammaNaimarkView
              (realifiedLogarithmicDomainEmbedding
                (canonicalCompletedC3CausalResponseBoundaryDomainVector
                  hbase cutoff (operatorHeightParameter z)))‖ ^ 2 -
            ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2))
      atTop
      (nhds (z.im *
        (‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2))) := by
  have hbalance :=
    canonicalCompletedC3FiniteGammaCorrectionBalance_tendsto
      hbase z hz hzHalf
  convert hbalance using 1
  · funext cutoff
    exact
      (canonicalCompletedC3FiniteGammaCorrectionBalance_eq_energyDifference
        hbase cutoff z hz).symm
  · exact
      congrArg nhds
        (canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference
          z hz hzHalf).symm

/-- The finite-to-completed limit with the TFVD side expanded entirely into
the ordinary carry-gradient prefix. -/
theorem canonicalCompletedC3FiniteGradientGammaEnergyDifference_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        z.im *
          ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
              ‖canonicalCompletedC3DirichletGradientPrefixState
                (operatorHeightParameter z)
                (NativeCarrySpectralWeyl.Limits.finiteCameraWindow
                  base cutoff + 1)‖ ^ 2 -
            ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2))
      atTop
      (nhds (z.im *
        ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
            ‖canonicalCompletedC3DirichletGradientState
              (operatorHeightParameter z) hzHalf‖ ^ 2 -
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2))) := by
  have hlimit :=
    canonicalCompletedC3FiniteTfvdGammaEnergyDifference_tendsto
      hbase z hz hzHalf
  convert hlimit using 1
  · funext cutoff
    rw [canonicalCompletedC3FiniteAmbientTfvdEnergy_eq_prefix]
  · exact congrArg nhds (congrArg (fun energy : ℝ =>
      z.im * (energy -
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2))
      (canonicalCompletedC3AmbientResponseEnergy_eq_gradient z hzHalf).symm)

/-- An exact finite-cutoff cancellation identity passes to the completed
balance.  This is the non-asymptotic interface expected from the native
head/tail geometry. -/
theorem canonicalCompletedC3GammaCorrectionBalance_eq_zero_of_finite
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hfinite : ∀ cutoff : ℕ,
      canonicalCompletedC3FiniteGammaCorrectionBalance
        hbase cutoff z hz = 0) :
    canonicalCompletedC3GammaCorrectionBalance z hz hzHalf = 0 := by
  have hlimit :=
    canonicalCompletedC3FiniteGammaCorrectionBalance_tendsto
      hbase z hz hzHalf
  have hzero : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteGammaCorrectionBalance
          hbase cutoff z hz)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) using 1
    funext cutoff
    exact hfinite cutoff
  exact tendsto_nhds_unique hlimit hzero

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

/-- Multiplying the diagonal Gram difference by `im z` exposes its exact
source-boundary balance.  No division or sign premise is used. -/
theorem canonicalCompletedC3CompressedGram_sub_gamma_diagonal_re_mul_im
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    z.im *
        (canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter z) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter z)
              hzHalf hzHalf).re : ℂ) -
            canonicalCompletedC3PolarizedGammaKernel z z hz hz).re =
      (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
          z z hz hz hzHalf).im +
        z.im *
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            z hz hzHalf‖ ^ 2 := by
  rw [canonicalCompletedC3CompressedGram_sub_gamma_diagonal_re,
    canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_diagonal_im]
  ring

/-- Exact noncircular cancellation criterion.  Equality of the compressed
and Gamma diagonal energies is equivalent to one explicit source-boundary
balance; the nonzero imaginary coordinate is the only cancellation used. -/
theorem canonicalCompletedC3CompressedGram_diagonal_eq_gamma_iff_sourceBoundary
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3CompressedGramCoefficient
            (operatorHeightParameter z) (operatorHeightParameter z) *
          ((canonicalCompletedC3RawGammaGram
            (operatorHeightParameter z) (operatorHeightParameter z)
            hzHalf hzHalf).re : ℂ) -
          canonicalCompletedC3PolarizedGammaKernel z z hz hz).re = 0 ↔
      (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
          z z hz hz hzHalf).im +
        z.im *
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            z hz hzHalf‖ ^ 2 = 0 := by
  constructor
  · intro hzero
    rw [← canonicalCompletedC3CompressedGram_sub_gamma_diagonal_re_mul_im]
    rw [hzero, mul_zero]
  · intro hboundary
    have hmul :=
      canonicalCompletedC3CompressedGram_sub_gamma_diagonal_re_mul_im
        z hz hzHalf
    rw [hboundary] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hz

/-! ## The canonical nonzero-leak witness -/

/-- At the established geometric witness, the correction Gram is strictly
positive.  This transports the already proved source mismatch through the
injective ambient resolvent. -/
theorem canonicalCompletedC3CorrectionKernel_noLeakWitness_diagonal_re_pos
    : 0 < (canonicalCompletedC3CorrectionKernel
      noLeakWitnessHeight noLeakWitnessHeight
      (by rw [noLeakWitnessHeight_im]; norm_num)
      (by rw [noLeakWitnessHeight_im]; norm_num)
      (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
      (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)).re := by
  let hz : noLeakWitnessHeight.im ≠ 0 := by
    rw [noLeakWitnessHeight_im]
    norm_num
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  change 0 < (canonicalCompletedC3CorrectionKernel
    noLeakWitnessHeight noLeakWitnessHeight hz hz hs hs).re
  apply canonicalCompletedC3CorrectionKernel_diagonal_re_pos_of_source_ne_zero
  intro hsource
  have hzero : canonicalCompletedC3AmbientTfvdResolvedCorrection
      noLeakWitnessHeight hz hs = 0 :=
    (canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_zero_iff_source
      noLeakWitnessHeight hz hs).mpr hsource
  exact canonicalCompletedC3AmbientTfvdResolvedCorrection_ne_zero_at_witness
    hbase hzero

/-- At the same witness, diagonal cancellation is equivalent to one literal
positive-target identity: the imaginary source-boundary skew must equal one
quarter of the squared correction norm. -/
theorem canonicalCompletedC3CompressedGram_noLeakWitness_eq_gamma_iff
    : (canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter noLeakWitnessHeight)
          (operatorHeightParameter noLeakWitnessHeight) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter noLeakWitnessHeight)
          (operatorHeightParameter noLeakWitnessHeight)
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)).re : ℂ) -
        canonicalCompletedC3PolarizedGammaKernel
          noLeakWitnessHeight noLeakWitnessHeight
          (by rw [noLeakWitnessHeight_im]; norm_num)
          (by rw [noLeakWitnessHeight_im]; norm_num)).re = 0 ↔
      (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
          noLeakWitnessHeight noLeakWitnessHeight
          (by rw [noLeakWitnessHeight_im]; norm_num)
          (by rw [noLeakWitnessHeight_im]; norm_num)
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)).im =
        (1 / 4 : ℝ) *
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            noLeakWitnessHeight
            (by rw [noLeakWitnessHeight_im]; norm_num)
            (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)‖ ^ 2 := by
  let hz : noLeakWitnessHeight.im ≠ 0 := by
    rw [noLeakWitnessHeight_im]
    norm_num
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  change
    (canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter noLeakWitnessHeight)
          (operatorHeightParameter noLeakWitnessHeight) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter noLeakWitnessHeight)
          (operatorHeightParameter noLeakWitnessHeight) hs hs).re : ℂ) -
        canonicalCompletedC3PolarizedGammaKernel
          noLeakWitnessHeight noLeakWitnessHeight hz hz).re = 0 ↔
      (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        noLeakWitnessHeight noLeakWitnessHeight hz hz hs).im =
        (1 / 4 : ℝ) *
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            noLeakWitnessHeight hz hs‖ ^ 2
  rw [canonicalCompletedC3CompressedGram_diagonal_eq_gamma_iff_sourceBoundary]
  rw [noLeakWitnessHeight_im]
  constructor <;> intro h <;> nlinarith

end

end CarrySelfAdjointOperator
