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

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

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

/-- Every finite section of the actual all-cutoff ambient-response kernel is
positive semidefinite.  The source may depend on the spectral parameter; all
response vectors nevertheless inhabit the same completed Naimark space. -/
theorem canonicalCompletedC3AmbientResponseKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ)
    (hhalf : ∀ i, 0 < (operatorHeightParameter (point i)).re) :
    (Matrix.of fun i j =>
      canonicalCompletedC3AmbientResponseKernel
        (point i) (point j) (hhalf i) (hhalf j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3AmbientResponseState (point i) (hhalf i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

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

/-! ## Exact Pythagorean criterion at the response level -/

/-- Gamma paired with the resolvent response to the intrinsic compressed-port
source discrepancy. -/
def canonicalCompletedC3GammaPortCorrectionKernel
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf) : ℂ :=
  inner ℂ
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3GammaNaimarkView
      (realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3CompressedTfvdPortResolvedCorrection
          z hz hzHalf hbound)))

/-- Gamma paired with the resolvent response to the complementary ambient
Naimark leak. -/
def canonicalCompletedC3GammaLeakCorrectionKernel
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf) : ℂ :=
  inner ℂ
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3GammaNaimarkView
      (realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3AmbientLeakResolvedCorrection
          z hz hzHalf hbound)))

/-- The response cross Gram retains both source channels.  Linearity of the
ambient resolvent gives this decomposition without an orthogonality premise. -/
theorem canonicalCompletedC3GammaCorrectionKernel_eq_port_add_leak
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf) :
    canonicalCompletedC3GammaCorrectionKernel z z hz hz hzHalf =
      canonicalCompletedC3GammaPortCorrectionKernel
          z hz hzHalf hbound +
        canonicalCompletedC3GammaLeakCorrectionKernel
          z hz hzHalf hbound := by
  unfold canonicalCompletedC3GammaCorrectionKernel
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState
    canonicalCompletedC3GammaPortCorrectionKernel
    canonicalCompletedC3GammaLeakCorrectionKernel
  rw [canonicalCompletedC3AmbientTfvdResolvedCorrection_eq_port_add_leak
      z hz hzHalf hbound,
    map_add, canonicalCompletedC3GammaNaimarkView_add, inner_add_right]

/-- Before resolving, the canonical port source is exactly orthogonal to the
completed complementary leak.  This records the genuine source-level
Pythagorean input separately from the response-level question. -/
theorem canonicalCompletedC3TfvdSource_inner_ambientLeak_eq_zero
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hsource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hbound))) :
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)))
        (canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3AmbientNaimarkLeakLimit
            z hzHalf hbound)) = 0 := by
  rw [inner_complex_gammaNaimarkView_port_eq_adjoint,
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
      hbase z hzHalf hbound hsource]
  simp

/-- Orthogonal projection onto the realified Naimark-port range. -/
def canonicalCompletedC3AmbientPortProjection :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedNaimarkPort ∘L realifiedNaimarkAdjoint

/-- Compressing after the canonical ambient-port projection returns the
original compression. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3AmbientPortProjection
    (x : RealifiedNaimarkComplexification) :
    realifiedNaimarkAdjoint
        (canonicalCompletedC3AmbientPortProjection x) =
      realifiedNaimarkAdjoint x := by
  change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
      (realifiedNaimarkAdjoint x) = realifiedNaimarkAdjoint x
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- The canonical ambient-port map is an actual projection. -/
theorem canonicalCompletedC3AmbientPortProjection_idempotent
    (x : RealifiedNaimarkComplexification) :
    canonicalCompletedC3AmbientPortProjection
        (canonicalCompletedC3AmbientPortProjection x) =
      canonicalCompletedC3AmbientPortProjection x := by
  change realifiedNaimarkPort
      (realifiedNaimarkAdjoint
        (canonicalCompletedC3AmbientPortProjection x)) =
    realifiedNaimarkPort (realifiedNaimarkAdjoint x)
  rw [realifiedNaimarkAdjoint_canonicalCompletedC3AmbientPortProjection]

/-- The ambient-port projection fixes every promoted camera vector. -/
theorem canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort
    (u : RealifiedCameraComplexification) :
    canonicalCompletedC3AmbientPortProjection (realifiedNaimarkPort u) =
      realifiedNaimarkPort u := by
  unfold canonicalCompletedC3AmbientPortProjection
  change realifiedNaimarkPort
      ((realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) u) = _
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- The real orthogonal projection acts identically on both quadratures, so
it commutes with the real block representing complex scalar multiplication. -/
theorem canonicalCompletedC3AmbientPortProjection_realifiedNaimarkScalar
    (z : ℂ) (x : RealifiedNaimarkComplexification) :
    canonicalCompletedC3AmbientPortProjection (realifiedNaimarkScalar z x) =
      realifiedNaimarkScalar z
        (canonicalCompletedC3AmbientPortProjection x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [canonicalCompletedC3AmbientPortProjection,
      realifiedNaimarkPort, realifiedNaimarkAdjoint,
      realifiedNaimarkScalar, realifiedContinuousLinearBlock,
      ContinuousLinearMap.comp_apply]
  · simp [canonicalCompletedC3AmbientPortProjection,
      realifiedNaimarkPort, realifiedNaimarkAdjoint,
      realifiedNaimarkScalar, realifiedContinuousLinearBlock,
      ContinuousLinearMap.comp_apply]

/-- The complementary component has zero camera compression. -/
theorem realifiedNaimarkAdjoint_sub_canonicalCompletedC3AmbientPortProjection
    (x : RealifiedNaimarkComplexification) :
    realifiedNaimarkAdjoint
        (x - canonicalCompletedC3AmbientPortProjection x) = 0 := by
  rw [map_sub,
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientPortProjection,
    sub_self]

/-- The projected ambient range is orthogonal to every complementary
component in the full two-quadrature complex Hilbert structure. -/
theorem inner_canonicalCompletedC3AmbientPortProjection_sub_eq_zero
    (x y : RealifiedNaimarkComplexification) :
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (canonicalCompletedC3AmbientPortProjection x))
        (canonicalCompletedC3GammaNaimarkView
          (y - canonicalCompletedC3AmbientPortProjection y)) = 0 := by
  change inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort (realifiedNaimarkAdjoint x)))
      (canonicalCompletedC3GammaNaimarkView
        (y - canonicalCompletedC3AmbientPortProjection y)) = 0
  rw [inner_complex_gammaNaimarkView_port_eq_adjoint,
    realifiedNaimarkAdjoint_sub_canonicalCompletedC3AmbientPortProjection]
  simp

/-- The completed ambient TFVD response already belongs to the Naimark-port
range. -/
theorem canonicalCompletedC3AmbientPortProjection_completedSymplecticState
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientPortProjection
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf) =
      completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hzHalf := by
  unfold canonicalCompletedC3AmbientPortProjection
    completedC3SymplecticNaimarkState
  change realifiedNaimarkPort
      ((realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
        (completedC3SymplecticCameraState
          (operatorHeightParameter z) hzHalf)) = _
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- Port component of the concrete Gamma response. -/
def canonicalCompletedC3ProjectedGammaPortState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (canonicalCompletedC3AmbientPortProjection
      (canonicalCompletedC3PolarizedGammaState z hz))

/-- Complementary Naimark component of the concrete Gamma response. -/
def canonicalCompletedC3GammaPortEscapeState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  canonicalCompletedC3PolarizedGammaState z hz -
    canonicalCompletedC3ProjectedGammaPortState z hz

/-- Difference internal to the Naimark port between the completed ambient
response and the projected Gamma response. -/
def canonicalCompletedC3AmbientPortDifferenceState
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    CarryGammaComplexNaimark :=
  canonicalCompletedC3AmbientResponseState z hzHalf -
    canonicalCompletedC3ProjectedGammaPortState z hz

/-- The compression of the concrete Gamma response is its canonical Cauchy
boundary value. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3PolarizedGammaState
    (z : ℂ) (hz : z.im ≠ 0) :
    realifiedNaimarkAdjoint
        (canonicalCompletedC3PolarizedGammaState z hz) =
      allBasesCauchyBlock z hz
        (canonicalCompletedC3SixCameraSource z) := by
  simpa [canonicalCompletedC3PolarizedGammaState,
    carryGammaComplexState, carryDefectGammaZero,
    ContinuousLinearMap.comp_apply] using
      (carryDefectGammaZero_apply z hz
        (canonicalCompletedC3SixCameraSource z))

/-- The projected Gamma vector is exactly the Naimark promotion of its
compressed Cauchy boundary value. -/
theorem canonicalCompletedC3ProjectedGammaPortState_eq_cauchyPort
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3ProjectedGammaPortState z hz =
      canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z))) := by
  unfold canonicalCompletedC3ProjectedGammaPortState
    canonicalCompletedC3AmbientPortProjection
  rw [ContinuousLinearMap.comp_apply,
    realifiedNaimarkAdjoint_canonicalCompletedC3PolarizedGammaState]

/-- The Gamma response is the orthogonal sum of its port and escape
components. -/
theorem canonicalCompletedC3PolarizedGammaState_eq_port_add_escape
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaState z hz =
      canonicalCompletedC3ProjectedGammaPortState z hz +
        canonicalCompletedC3GammaPortEscapeState z hz := by
  unfold canonicalCompletedC3GammaPortEscapeState
  abel

/-- The resolved TFVD correction contains the internal port difference and
the opposite Gamma escape component. -/
theorem canonicalCompletedC3AmbientTfvdResolvedCorrectionState_eq_portDifference_sub_escape
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState z hz hzHalf =
      canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf -
        canonicalCompletedC3GammaPortEscapeState z hz := by
  unfold canonicalCompletedC3AmbientPortDifferenceState
    canonicalCompletedC3GammaPortEscapeState
  rw [canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
    z hz hzHalf]
  abel

/-- The projected Gamma component is orthogonal to its escape component. -/
theorem inner_canonicalCompletedC3ProjectedGammaPort_escape_eq_zero
    (z : ℂ) (hz : z.im ≠ 0) :
    inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3GammaPortEscapeState z hz) = 0 := by
  exact inner_canonicalCompletedC3AmbientPortProjection_sub_eq_zero
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3PolarizedGammaState z hz)

/-- The internal port difference is also orthogonal to the Gamma escape. -/
theorem inner_canonicalCompletedC3AmbientPortDifference_escape_eq_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    inner ℂ
        (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf)
        (canonicalCompletedC3GammaPortEscapeState z hz) = 0 := by
  have hambient :
      inner ℂ
          (canonicalCompletedC3AmbientResponseState z hzHalf)
          (canonicalCompletedC3GammaPortEscapeState z hz) = 0 := by
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
      (canonicalCompletedC3PolarizedGammaState z hz)
  unfold canonicalCompletedC3AmbientPortDifferenceState
  rw [inner_sub_left, hambient,
    inner_canonicalCompletedC3ProjectedGammaPort_escape_eq_zero,
    sub_zero]

/-- The port part of the cross channel is a literal camera-space Cauchy
pairing.  No ambient or spectral scalarization remains on this side. -/
theorem inner_projectedGammaPort_ambientPortDifference_eq_cauchyCamera
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf) =
      inner ℂ
        (canonicalCompletedC3GammaCameraView
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter z) hzHalf -
            allBasesCauchyBlock z hz
              (canonicalCompletedC3SixCameraSource z))) := by
  rw [canonicalCompletedC3ProjectedGammaPortState_eq_cauchyPort]
  unfold canonicalCompletedC3AmbientPortDifferenceState
    canonicalCompletedC3AmbientResponseState
    completedC3SymplecticNaimarkState
  rw [canonicalCompletedC3ProjectedGammaPortState_eq_cauchyPort]
  simp only [← canonicalCompletedC3GammaNaimarkView_sub, ← map_sub]
  rw [inner_complex_gammaNaimarkView_port_port]

/-- The Gamma escape is precisely the failure of the ambient logarithmic
resolvent response to remain in the Naimark port. -/
theorem canonicalCompletedC3GammaPortEscapeState_eq_resolvent_sub_projection
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaPortEscapeState z hz =
      canonicalCompletedC3GammaNaimarkView
        (logarithmicResolventBlock z hz
            (realifiedNaimarkPort
              (canonicalCompletedC3SixCameraSource z)) -
          canonicalCompletedC3AmbientPortProjection
            (logarithmicResolventBlock z hz
              (realifiedNaimarkPort
                (canonicalCompletedC3SixCameraSource z)))) := by
  unfold canonicalCompletedC3GammaPortEscapeState
    canonicalCompletedC3ProjectedGammaPortState
    canonicalCompletedC3PolarizedGammaState carryGammaComplexState
    carryGammaSource
  simp only [ContinuousLinearMap.comp_apply,
    canonicalCompletedC3GammaNaimarkView_sub]
  rfl

/-- Vanishing of the Gamma escape is exactly invariance of the concrete
canonical-source resolvent response under the Naimark-port projection. -/
theorem canonicalCompletedC3GammaPortEscapeState_eq_zero_iff_resolvent_in_port
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaPortEscapeState z hz = 0 ↔
      canonicalCompletedC3AmbientPortProjection
          (logarithmicResolventBlock z hz
            (realifiedNaimarkPort
              (canonicalCompletedC3SixCameraSource z))) =
        logarithmicResolventBlock z hz
          (realifiedNaimarkPort
            (canonicalCompletedC3SixCameraSource z)) := by
  rw [canonicalCompletedC3GammaPortEscapeState_eq_resolvent_sub_projection]
  change logarithmicResolventBlock z hz
          (realifiedNaimarkPort
            (canonicalCompletedC3SixCameraSource z)) -
        canonicalCompletedC3AmbientPortProjection
          (logarithmicResolventBlock z hz
            (realifiedNaimarkPort
              (canonicalCompletedC3SixCameraSource z))) = 0 ↔ _
  rw [sub_eq_zero]
  exact eq_comm

/-- Complementary logarithmic image of the canonical Gamma domain response.
This is the concrete off-port vector that must be detected to prove that the
Gamma resolvent response really escapes the camera port. -/
def canonicalCompletedC3GammaLogarithmicLeakState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  canonicalCompletedC3GammaNaimarkView
    (realifiedLogarithmicMultiplication
        (canonicalCompletedC3TfvdResolventDomainVector z hz) -
      canonicalCompletedC3AmbientPortProjection
        (realifiedLogarithmicMultiplication
          (canonicalCompletedC3TfvdResolventDomainVector z hz)))

/-- Applying the complementary port projection to the exact resolvent
equation identifies the logarithmic leak with `z` times the Gamma escape.
No Gram identity or positivity input is used. -/
theorem canonicalCompletedC3GammaLogarithmicLeakState_eq_smul_escape
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaLogarithmicLeakState z hz =
      z • canonicalCompletedC3GammaPortEscapeState z hz := by
  let x : RealifiedNaimarkComplexification :=
    realifiedLogarithmicDomainEmbedding
      (canonicalCompletedC3TfvdResolventDomainVector z hz)
  let y : RealifiedNaimarkComplexification :=
    realifiedLogarithmicMultiplication
      (canonicalCompletedC3TfvdResolventDomainVector z hz)
  let u : RealifiedNaimarkComplexification :=
    realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)
  have hdef : realifiedNaimarkScalar z x = y + u := by
    exact canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation
      z hz
  have hprojected := congrArg canonicalCompletedC3AmbientPortProjection hdef
  rw [map_add,
    canonicalCompletedC3AmbientPortProjection_realifiedNaimarkScalar,
    canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort] at hprojected
  have hy : y = realifiedNaimarkScalar z x - u := by
    rw [hdef]
    abel
  have hpy : canonicalCompletedC3AmbientPortProjection y =
      realifiedNaimarkScalar z
          (canonicalCompletedC3AmbientPortProjection x) - u := by
    rw [hprojected]
    abel
  have hleak :
      y - canonicalCompletedC3AmbientPortProjection y =
        realifiedNaimarkScalar z
          (x - canonicalCompletedC3AmbientPortProjection x) := by
    rw [hpy, hy, map_sub]
    abel
  unfold canonicalCompletedC3GammaLogarithmicLeakState
  change canonicalCompletedC3GammaNaimarkView
      (y - canonicalCompletedC3AmbientPortProjection y) = _
  rw [hleak,
    canonicalCompletedC3GammaNaimarkView_realifiedNaimarkScalar]
  rw [canonicalCompletedC3GammaPortEscapeState_eq_resolvent_sub_projection]
  have hx : x =
      logarithmicResolventBlock z hz
        (realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)) := by
    dsimp [x, canonicalCompletedC3TfvdResolventDomainVector]
    rw [realifiedLogarithmicDomainEmbedding_resolventDomainElement,
      canonicalCompletedC3TfvdCameraSource_eq_canonicalSource]
  rw [hx]

/-- Since the resolvent parameter is off the real axis, its scalar action is
injective.  Thus the concrete logarithmic leak and the Gamma escape vanish
simultaneously. -/
theorem canonicalCompletedC3GammaLogarithmicLeakState_eq_zero_iff_escape
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaLogarithmicLeakState z hz = 0 ↔
      canonicalCompletedC3GammaPortEscapeState z hz = 0 := by
  rw [canonicalCompletedC3GammaLogarithmicLeakState_eq_smul_escape]
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hz
    rw [hzero]
    rfl
  simp [hz0]

theorem canonicalCompletedC3GammaLogarithmicLeakState_ne_zero_iff_escape
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GammaLogarithmicLeakState z hz ≠ 0 ↔
      canonicalCompletedC3GammaPortEscapeState z hz ≠ 0 := by
  exact not_congr
    (canonicalCompletedC3GammaLogarithmicLeakState_eq_zero_iff_escape z hz)

/-- Norm form of the exact logarithmic-leak/escape identity. -/
theorem canonicalCompletedC3GammaLogarithmicLeakState_norm_sq
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖canonicalCompletedC3GammaLogarithmicLeakState z hz‖ ^ 2 =
      ‖z‖ ^ 2 * ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3GammaLogarithmicLeakState_eq_smul_escape,
    norm_smul]
  ring

/-- Exact signed decomposition of the diagonal Gamma--correction cross
channel.  The complementary escape contributes with the fixed negative sign;
all remaining cancellation is internal to the camera port. -/
theorem canonicalCompletedC3GammaCorrectionKernel_diagonal_re_eq_port_sub_escape
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3GammaCorrectionKernel
        z z hz hz hzHalf).re =
      (inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState
          z hz hzHalf)).re -
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  have hportEscape :=
    inner_canonicalCompletedC3ProjectedGammaPort_escape_eq_zero z hz
  have hportDifferenceEscape :=
    inner_canonicalCompletedC3AmbientPortDifference_escape_eq_zero
      z hz hzHalf
  have hescapePortDifference :
      inner ℂ
          (canonicalCompletedC3GammaPortEscapeState z hz)
          (canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf) = 0 :=
    inner_eq_zero_symm.mp hportDifferenceEscape
  unfold canonicalCompletedC3GammaCorrectionKernel
  rw [canonicalCompletedC3PolarizedGammaState_eq_port_add_escape z hz,
    canonicalCompletedC3AmbientTfvdResolvedCorrectionState_eq_portDifference_sub_escape
      z hz hzHalf,
    inner_add_left, inner_sub_right, inner_sub_right,
    hportEscape, hescapePortDifference]
  simp only [sub_zero, zero_sub, Complex.add_re, Complex.neg_re]
  have hnorm :
      (inner ℂ
        (canonicalCompletedC3GammaPortEscapeState z hz)
        (canonicalCompletedC3GammaPortEscapeState z hz)).re =
      ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ)
        (canonicalCompletedC3GammaPortEscapeState z hz)).symm
  rw [hnorm]
  ring

/-- On the concrete induced source, failure of the ambient resolvent to
commute with the Naimark-port projection is exactly the resolved leak.  Thus
the response-level obstruction is not an unnamed defect: it is the return of
the source channel that was orthogonal before applying the resolvent. -/
theorem canonicalCompletedC3AmbientPortProjection_resolvent_commutator_eq_leak
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hsource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hbound))) :
    canonicalCompletedC3AmbientPortProjection
          (logarithmicResolventBlock z hz
            (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf)) -
        logarithmicResolventBlock z hz
          (canonicalCompletedC3AmbientPortProjection
            (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf)) =
      realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3AmbientLeakResolvedCorrection
          z hz hzHalf hbound) := by
  have hleakAdjoint :=
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
      hbase z hzHalf hbound hsource
  have hadjointPort (u : RealifiedCameraComplexification) :
      realifiedNaimarkAdjoint (realifiedNaimarkPort u) = u := by
    change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) u = u
    rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
    rfl
  have hprojectionSource :
      canonicalCompletedC3AmbientPortProjection
          (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf) =
        realifiedNaimarkPort
          (canonicalCompletedC3CompressedHilbertSource
            z hzHalf hbound) := by
    unfold canonicalCompletedC3AmbientPortProjection
    rw [ContinuousLinearMap.comp_apply,
      canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
        z hzHalf hbound,
      map_add, hadjointPort, hleakAdjoint, add_zero]
  have hresolventSource :
      logarithmicResolventBlock z hz
          (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf) =
        completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf := by
    have h := canonicalCompletedC3AmbientResolventDomainVector_embedding
      z hz hzHalf
    unfold canonicalCompletedC3AmbientResolventDomainVector at h
    change realifiedLogarithmicDomainEmbedding
        (logarithmicResolventDomainElement z hz
          (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf)) = _ at h
    rw [realifiedLogarithmicDomainEmbedding_resolventDomainElement] at h
    exact h
  have hprojectionState :
      canonicalCompletedC3AmbientPortProjection
          (completedC3SymplecticNaimarkState
            (operatorHeightParameter z) hzHalf) =
        completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf := by
    unfold canonicalCompletedC3AmbientPortProjection
      completedC3SymplecticNaimarkState
    rw [ContinuousLinearMap.comp_apply, hadjointPort]
  have hsourceSplit :=
    canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
      z hzHalf hbound
  have hresolventSplit := congrArg (logarithmicResolventBlock z hz) hsourceSplit
  simp only [map_add] at hresolventSplit
  have hleakResolved :
      realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3AmbientLeakResolvedCorrection
            z hz hzHalf hbound) =
        logarithmicResolventBlock z hz
          (canonicalCompletedC3AmbientNaimarkLeakLimit
            z hzHalf hbound) := by
    unfold canonicalCompletedC3AmbientLeakResolvedCorrection
    change realifiedLogarithmicDomainEmbedding
        (logarithmicResolventDomainElement z hz
          (canonicalCompletedC3AmbientNaimarkLeakLimit
            z hzHalf hbound)) = _
    rw [realifiedLogarithmicDomainEmbedding_resolventDomainElement]
  rw [hresolventSource, hprojectionState, hprojectionSource]
  rw [hleakResolved]
  rw [hresolventSource] at hresolventSplit
  rw [hresolventSplit]
  abel

/-- At the established geometric witness the projection/resolvent
commutator is genuinely nonzero.  The source-level Pythagorean decomposition
therefore cannot be transported to the response by a reducing-subspace
argument. -/
theorem exists_canonicalCompletedC3AmbientPortProjection_resolvent_commutator_ne_zero_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    ∃ hbound : CanonicalCompletedC3CompressedSourceFormBounded
        noLeakWitnessHeight
        (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num),
      ∃ _hsource : Tendsto
        (fun cutoff : ℕ =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff noLeakWitnessHeight)
        atTop
        (nhds (canonicalCompletedC3CompressedHilbertSource
          noLeakWitnessHeight
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)
          hbound)),
      canonicalCompletedC3AmbientPortProjection
            (logarithmicResolventBlock noLeakWitnessHeight
              (by rw [noLeakWitnessHeight_im]; norm_num)
              (canonicalCompletedC3AmbientInducedSourceLimit
                noLeakWitnessHeight
                (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num))) -
          logarithmicResolventBlock noLeakWitnessHeight
            (by rw [noLeakWitnessHeight_im]; norm_num)
            (canonicalCompletedC3AmbientPortProjection
              (canonicalCompletedC3AmbientInducedSourceLimit
                noLeakWitnessHeight
                (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num))) ≠ 0 := by
  let hz : noLeakWitnessHeight.im ≠ 0 := by
    rw [noLeakWitnessHeight_im]
    norm_num
  let hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  rcases exists_canonicalCompletedC3AmbientNaimarkLeakLimit_ne_zero_at_witness
      hbase with ⟨hbound, hsource, hleak⟩
  refine ⟨hbound, hsource, ?_⟩
  change canonicalCompletedC3AmbientPortProjection
          (logarithmicResolventBlock noLeakWitnessHeight hz
            (canonicalCompletedC3AmbientInducedSourceLimit
              noLeakWitnessHeight hs)) -
        logarithmicResolventBlock noLeakWitnessHeight hz
          (canonicalCompletedC3AmbientPortProjection
            (canonicalCompletedC3AmbientInducedSourceLimit
              noLeakWitnessHeight hs)) ≠ 0
  rw [canonicalCompletedC3AmbientPortProjection_resolvent_commutator_eq_leak
    hbase noLeakWitnessHeight hz hs hbound hsource]
  intro hembedding
  have hdomain :
      canonicalCompletedC3AmbientLeakResolvedCorrection
        noLeakWitnessHeight hz hs hbound = 0 := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg WithLp.fst hembedding
    · apply Subtype.ext
      exact congrArg WithLp.snd hembedding
  have hsourceZero :
      canonicalCompletedC3AmbientNaimarkLeakLimit
        noLeakWitnessHeight hs hbound = 0 := by
    apply logarithmicResolventIntoDomain_injective noLeakWitnessHeight hz
    change logarithmicResolventIntoDomain noLeakWitnessHeight hz
        (canonicalCompletedC3AmbientNaimarkLeakLimit
          noLeakWitnessHeight hs hbound) = 0 at hdomain
    exact hdomain.trans
      (map_zero (logarithmicResolventIntoDomain noLeakWitnessHeight hz)).symm
  exact hleak hsourceZero

/-- The ambient response admits the expected Pythagorean decomposition
precisely when the real Gamma/correction cross Gram vanishes.  Orthogonality
of the source port and source leak is not used here and is not silently
transported through the resolvent. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_crossOrthogonal
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      (inner ℂ
        (canonicalCompletedC3PolarizedGammaState z hz)
        (canonicalCompletedC3AmbientTfvdResolvedCorrectionState
          z hz hzHalf)).re = 0 := by
  rw [canonicalCompletedC3AmbientResponseState_eq_gamma_add_correction
      z hz hzHalf,
    norm_add_sq (𝕜 := ℂ)]
  simp only [← RCLike.re_eq_complex_re]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- Response-level Pythagoras is equivalently the vanishing of the concrete
source-boundary skew channel.  This is the exact extra condition required to
transport the source orthogonality through the logarithmic resolvent. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_sourceBoundary_im
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      (canonicalCompletedC3GammaCorrectionSourceBoundaryReadout
        z z hz hz hzHalf).im = 0 := by
  rw [canonicalCompletedC3AmbientResponse_pythagoras_iff_crossOrthogonal
      z hz hzHalf,
    canonicalCompletedC3GammaCorrectionSourceBoundaryReadout_diagonal_im
      z hz hzHalf]
  let cross : ℝ :=
    (canonicalCompletedC3GammaCorrectionKernel
      z z hz hz hzHalf).re
  change cross = 0 ↔ 2 * z.im * cross = 0
  constructor
  · intro hcross
    rw [hcross, mul_zero]
  · intro hproduct
    exact (mul_eq_zero.mp hproduct).resolve_left
      (mul_ne_zero (by norm_num) hz)

/-- Channel-separated response criterion.  Source orthogonality alone only
controls the unresolved source vectors; after the resolvent, both the port
discrepancy and returned leak cross terms remain visible. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_port_add_leak_cross
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      (canonicalCompletedC3GammaPortCorrectionKernel
          z hz hzHalf hbound).re +
        (canonicalCompletedC3GammaLeakCorrectionKernel
          z hz hzHalf hbound).re = 0 := by
  rw [canonicalCompletedC3AmbientResponse_pythagoras_iff_crossOrthogonal
      z hz hzHalf]
  change (canonicalCompletedC3GammaCorrectionKernel
    z z hz hz hzHalf).re = 0 ↔ _
  rw [canonicalCompletedC3GammaCorrectionKernel_eq_port_add_leak
    z hz hzHalf hbound, Complex.add_re]

/-- The response-level cross channel vanishes exactly when its internal
Cauchy-port pairing pays the full positive cost of the Gamma escape. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_portBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      (inner ℂ
        (canonicalCompletedC3ProjectedGammaPortState z hz)
        (canonicalCompletedC3AmbientPortDifferenceState
          z hz hzHalf)).re =
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3AmbientResponse_pythagoras_iff_crossOrthogonal
      z hz hzHalf]
  change (canonicalCompletedC3GammaCorrectionKernel
    z z hz hz hzHalf).re = 0 ↔ _
  rw [canonicalCompletedC3GammaCorrectionKernel_diagonal_re_eq_port_sub_escape]
  constructor <;> intro h <;> nlinarith

/-- Camera-space form of the exact cancellation criterion.  This is the
first point at which the remaining gate is expressed solely through the
compressed Cauchy response and the orthogonal resolvent escape. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_cauchyCameraBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      (inner ℂ
        (canonicalCompletedC3GammaCameraView
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter z) hzHalf -
            allBasesCauchyBlock z hz
              (canonicalCompletedC3SixCameraSource z)))).re =
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3AmbientResponse_pythagoras_iff_portBalance,
    inner_projectedGammaPort_ambientPortDifference_eq_cauchyCamera]

/-- Division-free operator-domain form of the exact cancellation criterion.
The escape norm is replaced by the complementary logarithmic image computed
directly from the Gamma maximal-domain vector. -/
theorem canonicalCompletedC3AmbientResponse_pythagoras_iff_logarithmicLeakBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2 ↔
      ‖z‖ ^ 2 *
          (inner ℂ
            (canonicalCompletedC3GammaCameraView
              (allBasesCauchyBlock z hz
                (canonicalCompletedC3SixCameraSource z)))
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                  (operatorHeightParameter z) hzHalf -
                allBasesCauchyBlock z hz
                  (canonicalCompletedC3SixCameraSource z)))).re =
        ‖canonicalCompletedC3GammaLogarithmicLeakState z hz‖ ^ 2 := by
  rw [canonicalCompletedC3AmbientResponse_pythagoras_iff_cauchyCameraBalance,
    canonicalCompletedC3GammaLogarithmicLeakState_norm_sq]
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hz
    rw [hzero]
    rfl
  have hnorm : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0)
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ hnorm h

/-- Negated form of the same exact criterion.  This is the honest remaining
noncancellation statement; neither a sign nor an escape hypothesis is hidden
in its interface. -/
theorem canonicalCompletedC3AmbientResponse_not_pythagoras_iff_logarithmicLeak_imbalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (¬ ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
          ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
            ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
              z hz hzHalf‖ ^ 2) ↔
      ‖z‖ ^ 2 *
          (inner ℂ
            (canonicalCompletedC3GammaCameraView
              (allBasesCauchyBlock z hz
                (canonicalCompletedC3SixCameraSource z)))
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                  (operatorHeightParameter z) hzHalf -
                allBasesCauchyBlock z hz
                  (canonicalCompletedC3SixCameraSource z)))).re ≠
        ‖canonicalCompletedC3GammaLogarithmicLeakState z hz‖ ^ 2 := by
  exact not_congr
    (canonicalCompletedC3AmbientResponse_pythagoras_iff_logarithmicLeakBalance
      z hz hzHalf)

/-- The previously separated resolved port and leak cross channels combine
to the same signed camera/escape formula. -/
theorem canonicalCompletedC3GammaPort_add_leak_cross_eq_cauchy_sub_escape
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf) :
    (canonicalCompletedC3GammaPortCorrectionKernel
        z hz hzHalf hbound).re +
      (canonicalCompletedC3GammaLeakCorrectionKernel
        z hz hzHalf hbound).re =
      (inner ℂ
        (canonicalCompletedC3GammaCameraView
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter z) hzHalf -
            allBasesCauchyBlock z hz
              (canonicalCompletedC3SixCameraSource z)))).re -
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  rw [← Complex.add_re,
    ← canonicalCompletedC3GammaCorrectionKernel_eq_port_add_leak
      z hz hzHalf hbound,
    canonicalCompletedC3GammaCorrectionKernel_diagonal_re_eq_port_sub_escape,
    inner_projectedGammaPort_ambientPortDifference_eq_cauchyCamera]

/-- If the internal camera cross pairing is nonpositive and the resolvent
really escapes the Naimark port, response-level Pythagoras is impossible. -/
theorem canonicalCompletedC3AmbientResponse_not_pythagoras_of_cauchyCross_nonpos
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hcross :
      (inner ℂ
        (canonicalCompletedC3GammaCameraView
          (allBasesCauchyBlock z hz
            (canonicalCompletedC3SixCameraSource z)))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState
              (operatorHeightParameter z) hzHalf -
            allBasesCauchyBlock z hz
              (canonicalCompletedC3SixCameraSource z)))).re ≤ 0)
    (hescape : canonicalCompletedC3GammaPortEscapeState z hz ≠ 0) :
    ¬ ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            z hz hzHalf‖ ^ 2 := by
  intro hpythagoras
  have hbalance :=
    (canonicalCompletedC3AmbientResponse_pythagoras_iff_cauchyCameraBalance
      z hz hzHalf).mp hpythagoras
  have hnorm : 0 < ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hescape) 2
  nlinarith

/-- If response-level Pythagoras holds and the correction state is nonzero,
the ambient and Gamma energies are necessarily different.  Thus Pythagoras
prevents cancellation; it cannot by itself prove the sewing equality. -/
theorem canonicalCompletedC3AmbientResponse_energy_ne_gamma_of_pythagoras
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hpythagoras :
      ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 +
          ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
            z hz hzHalf‖ ^ 2)
    (hcorrection :
      canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf ≠ 0) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 ≠
      ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 := by
  have hnorm : 0 <
      ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
        z hz hzHalf‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hcorrection) 2
  nlinarith

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
