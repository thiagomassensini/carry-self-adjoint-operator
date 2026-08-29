import CarrySelfAdjointOperator.CompletedC3AmbientSourceTailControl
import CarrySelfAdjointOperator.CompletedC3AllOrderGammaWronskianLimitGate
import CarrySelfAdjointOperator.CompletedC3CompressedBoundaryReadout
import CarrySelfAdjointOperator.RealLinearPMapComplexification
import Mathlib.Tactic

/-!
# Boundary readout of the full ambient C3 source

The completed all-order TFVD state is a resolvent response to its full
ambient source.  That source contains both the intrinsic camera port and the
complementary Naimark leak.  This file defines the uncompressed response-source
skew and proves its exact Green identity before comparing it with the scalar
completed Wronskian.
-/

open scoped ComplexConjugate InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Universal ambient Green identity -/

/-- Type-only view of the native ambient realification in its canonical
complex Hilbert structure.  No coordinate is changed. -/
def canonicalCompletedC3GammaNaimarkView
    (u : RealifiedNaimarkComplexification) :
    RealHilbertComplexification NaimarkSpace :=
  u

@[simp] theorem canonicalCompletedC3GammaNaimarkView_sub
    (u v : RealifiedNaimarkComplexification) :
    canonicalCompletedC3GammaNaimarkView (u - v) =
      canonicalCompletedC3GammaNaimarkView u -
        canonicalCompletedC3GammaNaimarkView v :=
  rfl

@[simp] theorem canonicalCompletedC3GammaNaimarkView_add
    (u v : RealifiedNaimarkComplexification) :
    canonicalCompletedC3GammaNaimarkView (u + v) =
      canonicalCompletedC3GammaNaimarkView u +
        canonicalCompletedC3GammaNaimarkView v :=
  rfl

/-- The complex ambient pairing with a Naimark port is exactly the complex
camera pairing with its adjoint compression. -/
theorem inner_complex_gammaNaimarkView_port_eq_adjoint
    (u : RealifiedCameraComplexification)
    (x : RealifiedNaimarkComplexification) :
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u))
        (canonicalCompletedC3GammaNaimarkView x) =
      inner ℂ
        (canonicalCompletedC3GammaCameraView u)
        (canonicalCompletedC3GammaCameraView
          (realifiedNaimarkAdjoint x)) := by
  have h11 :
      inner ℝ (naimarkIsometry u.fst) x.fst =
        inner ℝ u.fst (naimarkAdjoint x.fst) := by
    rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl]
    exact
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right _ _).symm
  have h12 :
      inner ℝ (naimarkIsometry u.fst) x.snd =
        inner ℝ u.fst (naimarkAdjoint x.snd) := by
    rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl]
    exact
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right _ _).symm
  have h21 :
      inner ℝ (naimarkIsometry u.snd) x.fst =
        inner ℝ u.snd (naimarkAdjoint x.fst) := by
    rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl]
    exact
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right _ _).symm
  have h22 :
      inner ℝ (naimarkIsometry u.snd) x.snd =
        inner ℝ u.snd (naimarkAdjoint x.snd) := by
    rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl]
    exact
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right _ _).symm
  apply Complex.ext
  · simp only [canonicalCompletedC3GammaNaimarkView,
      canonicalCompletedC3GammaCameraView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      WithLp.ofLp_fst, WithLp.ofLp_snd,
      realifiedNaimarkPort_fst, realifiedNaimarkPort_snd,
      realifiedNaimarkAdjoint_fst, realifiedNaimarkAdjoint_snd]
    exact congrArg₂ (· + ·) h11 h22
  · simp only [canonicalCompletedC3GammaNaimarkView,
      canonicalCompletedC3GammaCameraView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      WithLp.ofLp_fst, WithLp.ofLp_snd,
      realifiedNaimarkPort_fst, realifiedNaimarkPort_snd,
      realifiedNaimarkAdjoint_fst, realifiedNaimarkAdjoint_snd]
    exact congrArg₂ (· - ·) h12 h21

/-- The Naimark port preserves the full complex inner product of both camera
quadratures. -/
theorem inner_complex_gammaNaimarkView_port_port
    (u v : RealifiedCameraComplexification) :
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u))
        (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort v)) =
      inner ℂ
        (canonicalCompletedC3GammaCameraView u)
        (canonicalCompletedC3GammaCameraView v) := by
  rw [inner_complex_gammaNaimarkView_port_eq_adjoint]
  change
    inner ℂ
        (canonicalCompletedC3GammaCameraView u)
        (canonicalCompletedC3GammaCameraView
          ((realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) v)) = _
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- The realified scalar block is literal complex scalar multiplication on
the canonical two-quadrature ambient Hilbert space. -/
theorem canonicalCompletedC3GammaNaimarkView_realifiedNaimarkScalar
    (z : ℂ) (u : RealifiedNaimarkComplexification) :
    canonicalCompletedC3GammaNaimarkView (realifiedNaimarkScalar z u) =
      z • canonicalCompletedC3GammaNaimarkView u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (realifiedNaimarkScalar z u).fst =
      z.re • u.fst - z.im • u.snd
    exact realifiedNaimarkScalar_fst z u
  · change (realifiedNaimarkScalar z u).snd =
      z.im • u.fst + z.re • u.snd
    exact realifiedNaimarkScalar_snd z u

/-- The full logarithmic multiplication is symmetric after retaining both
real quadratures in the canonical complex Hilbert structure. -/
theorem inner_complex_realifiedLogarithmicMultiplication_comm
    (u v : RealifiedLogarithmicDomain) :
    inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicMultiplication u))
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding v)) =
      inner ℂ
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicDomainEmbedding u))
        (canonicalCompletedC3GammaNaimarkView
          (realifiedLogarithmicMultiplication v)) := by
  have h11 := logarithmicMultiplication_isFormalAdjoint u.1 v.1
  have h12 := logarithmicMultiplication_isFormalAdjoint u.1 v.2
  have h21 := logarithmicMultiplication_isFormalAdjoint u.2 v.1
  have h22 := logarithmicMultiplication_isFormalAdjoint u.2 v.2
  apply Complex.ext
  · simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    exact congrArg₂ (· + ·) h11 h22
  · simp only [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im]
    exact congrArg₂ (· - ·) h12 h21

/-- Uncompressed two-point boundary skew of maximal-domain responses and
their actual ambient defect sources. -/
def canonicalCompletedC3AmbientDefectBoundaryReadout
    (z w : ℂ) (u v : RealifiedLogarithmicDomain) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedLogarithmicDomainEmbedding u))
      (canonicalCompletedC3GammaNaimarkView
        (realifiedLambdaMinusLogarithmicMultiplication w v)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedLambdaMinusLogarithmicMultiplication z u))
      (canonicalCompletedC3GammaNaimarkView
        (realifiedLogarithmicDomainEmbedding v))

/-- The full ambient skew is spectral separation times the positive Gram of
the same two response vectors.  No port projection or no-leak premise occurs. -/
theorem canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel
    (z w : ℂ) (u v : RealifiedLogarithmicDomain) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w u v =
      (w - conj z) *
        inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedLogarithmicDomainEmbedding u))
          (canonicalCompletedC3GammaNaimarkView
            (realifiedLogarithmicDomainEmbedding v)) := by
  unfold canonicalCompletedC3AmbientDefectBoundaryReadout
    realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe,
    canonicalCompletedC3GammaNaimarkView_sub,
    inner_sub_right, inner_sub_left]
  rw [canonicalCompletedC3GammaNaimarkView_realifiedNaimarkScalar,
    canonicalCompletedC3GammaNaimarkView_realifiedNaimarkScalar,
    inner_complex_realifiedLogarithmicMultiplication_comm]
  simp only [inner_smul_right, inner_smul_left]
  ring

/-! ## The canonical completed ambient response -/

/-- Domain-valued resolvent response to the full completed ambient source. -/
def canonicalCompletedC3AmbientResolventDomainVector
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    RealifiedLogarithmicDomain :=
  logarithmicResolventIntoDomain z hz
    (canonicalCompletedC3AmbientInducedSourceLimit z hs)

/-- The explicit ambient resolvent response is exactly the completed
all-order TFVD Naimark state. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_embedding
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3AmbientResolventDomainVector z hz hs) =
      completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hs := by
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  rcases exists_canonicalCompletedC3AmbientResolventResponse
      hbase z hz hs with ⟨candidate, hembedding, hcandidate⟩
  unfold canonicalCompletedC3AmbientResolventDomainVector
  rw [← hcandidate]
  exact hembedding

/-- Boundary skew of the completed TFVD response and its full induced ambient
source.  The complementary Naimark channel is retained in both source terms. -/
def canonicalCompletedC3AmbientBoundaryReadout
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf))
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientInducedSourceLimit w hwHalf)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientInducedSourceLimit z hzHalf))
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter w) hwHalf))

/-- The concrete completed readout is the universal ambient defect readout
of the two canonical resolvent-domain vectors. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_defect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout
        z w hzHalf hwHalf =
      canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalCompletedC3AmbientResolventDomainVector z hz hzHalf)
        (canonicalCompletedC3AmbientResolventDomainVector w hw hwHalf) := by
  unfold canonicalCompletedC3AmbientBoundaryReadout
    canonicalCompletedC3AmbientDefectBoundaryReadout
  rw [canonicalCompletedC3AmbientResolventDomainVector_embedding,
    canonicalCompletedC3AmbientResolventDomainVector_embedding]
  simp only [canonicalCompletedC3AmbientResolventDomainVector,
    realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]

/-- Exact completed Green identity for the full ambient source. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout
        z w hzHalf hwHalf =
      (w - conj z) *
        inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter z) hzHalf))
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter w) hwHalf)) := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_defect
      z w hz hw hzHalf hwHalf,
    canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel,
    canonicalCompletedC3AmbientResolventDomainVector_embedding z hz hzHalf,
    canonicalCompletedC3AmbientResolventDomainVector_embedding w hw hwHalf]

/-! ## Port/leak decomposition of the scalar readout -/

/-- Portion of the ambient readout carried by the intrinsic compressed
sources. -/
def canonicalCompletedC3AmbientPortBoundaryReadout
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf))
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort
          (canonicalCompletedC3CompressedHilbertSource w hwHalf hwBound))) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort
          (canonicalCompletedC3CompressedHilbertSource z hzHalf hzBound)))
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter w) hwHalf))

/-- Portion of the ambient readout carried by the complementary Naimark
sources. -/
def canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hzHalf))
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientNaimarkLeakLimit w hwHalf hwBound)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3AmbientNaimarkLeakLimit z hzHalf hzBound))
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter w) hwHalf))

/-- Exact scalar decomposition of the full source into its port and leak
channels.  No channel is deleted in this equality. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_port_add_leak
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf) :
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf =
      canonicalCompletedC3AmbientPortBoundaryReadout
          z w hzHalf hwHalf hzBound hwBound +
        canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout
          z w hzHalf hwHalf hzBound hwBound := by
  unfold canonicalCompletedC3AmbientBoundaryReadout
    canonicalCompletedC3AmbientPortBoundaryReadout
    canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout
  rw [canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
      z hzHalf hzBound,
    canonicalCompletedC3AmbientInducedSourceLimit_eq_port_add_leak
      w hwHalf hwBound,
    canonicalCompletedC3GammaNaimarkView_add,
    canonicalCompletedC3GammaNaimarkView_add,
    inner_add_right, inner_add_left]
  ring

/-- Strong convergence of the complementary source upgrades its finite
camera invisibility to exact invisibility after completion. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hzSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hzBound))) :
    realifiedNaimarkAdjoint
        (canonicalCompletedC3AmbientNaimarkLeakLimit
          z hzHalf hzBound) = 0 := by
  have hleak :=
    canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_tendsto_ambientLimit
      hbase z hzHalf hzBound hzSource
  have hadjoint :=
    realifiedNaimarkAdjoint.continuous.continuousAt.tendsto.comp hleak
  have hadjoint' :
      Tendsto
        (fun cutoff : ℕ =>
          realifiedNaimarkAdjoint
            (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
              hbase cutoff z))
        atTop
        (nhds (realifiedNaimarkAdjoint
          (canonicalCompletedC3AmbientNaimarkLeakLimit
            z hzHalf hzBound))) := by
    exact hadjoint.congr' (Eventually.of_forall fun _ => rfl)
  have hfiniteZero :
      (fun cutoff : ℕ =>
        realifiedNaimarkAdjoint
          (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
            hbase cutoff z)) =
        (fun _ : ℕ => (0 : RealifiedCameraComplexification)) := by
    funext cutoff
    exact
      realifiedNaimarkAdjoint_canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
        hbase cutoff z
  rw [hfiniteZero] at hadjoint'
  exact tendsto_nhds_unique hadjoint' tendsto_const_nhds

/-- The completed leak channel is retained as a vector but contributes zero
to the response-source scalar skew because every completed TFVD response lies
in the Naimark-port range. -/
theorem canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout_eq_zero
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf)
    (hzSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hzBound)))
    (hwSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwHalf hwBound))) :
    canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout
        z w hzHalf hwHalf hzBound hwBound = 0 := by
  have hzAdjoint :=
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
      hbase z hzHalf hzBound hzSource
  have hwAdjoint :=
    realifiedNaimarkAdjoint_canonicalCompletedC3AmbientNaimarkLeakLimit
      hbase w hwHalf hwBound hwSource
  have hfirst :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter z) hzHalf))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3AmbientNaimarkLeakLimit
              w hwHalf hwBound)) = 0 := by
    change
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedNaimarkPort
              (completedC3SymplecticCameraState
                (operatorHeightParameter z) hzHalf)))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3AmbientNaimarkLeakLimit
              w hwHalf hwBound)) = 0
    rw [inner_complex_gammaNaimarkView_port_eq_adjoint, hwAdjoint]
    simp
  have hportSecond :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter w) hwHalf))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3AmbientNaimarkLeakLimit
              z hzHalf hzBound)) = 0 := by
    change
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedNaimarkPort
              (completedC3SymplecticCameraState
                (operatorHeightParameter w) hwHalf)))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3AmbientNaimarkLeakLimit
              z hzHalf hzBound)) = 0
    rw [inner_complex_gammaNaimarkView_port_eq_adjoint, hzAdjoint]
    simp
  have hsecond :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3AmbientNaimarkLeakLimit
              z hzHalf hzBound))
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter w) hwHalf)) = 0 :=
    inner_eq_zero_symm.mp hportSecond
  unfold canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout
  rw [hfirst, hsecond, sub_self]

/-- Therefore the scalar readout of the full source equals its intrinsic port
readout, even though the completed leak vector itself need not vanish. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_port
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf)
    (hzSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hzBound)))
    (hwSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwHalf hwBound))) :
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf =
      canonicalCompletedC3AmbientPortBoundaryReadout
        z w hzHalf hwHalf hzBound hwBound := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_port_add_leak,
    canonicalCompletedC3AmbientNaimarkLeakBoundaryReadout_eq_zero
      hbase z w hzHalf hwHalf hzBound hwBound hzSource hwSource,
    add_zero]

/-- The ambient port term is literally the previously constructed intrinsic
compressed boundary readout. -/
theorem canonicalCompletedC3AmbientPortBoundaryReadout_eq_compressed
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf) :
    canonicalCompletedC3AmbientPortBoundaryReadout
        z w hzHalf hwHalf hzBound hwBound =
      canonicalCompletedC3CompressedBoundaryReadout
        z w hzHalf hwHalf hzBound hwBound := by
  unfold canonicalCompletedC3AmbientPortBoundaryReadout
    canonicalCompletedC3CompressedBoundaryReadout
    completedC3SymplecticNaimarkState
  rw [inner_complex_gammaNaimarkView_port_port,
    inner_complex_gammaNaimarkView_port_port]

/-- Final commutative square for the full ambient source: its scalar boundary
readout is exactly the intrinsic compressed readout.  The nonzero ambient leak
survives vectorially but is orthogonal to this scalar boundary functional. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_compressed
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re)
    (hzBound : CanonicalCompletedC3CompressedSourceFormBounded z hzHalf)
    (hwBound : CanonicalCompletedC3CompressedSourceFormBounded w hwHalf)
    (hzSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzHalf hzBound)))
    (hwSource : Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwHalf hwBound))) :
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf =
      canonicalCompletedC3CompressedBoundaryReadout
        z w hzHalf hwHalf hzBound hwBound := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_port
      hbase z w hzHalf hwHalf hzBound hwBound hzSource hwSource,
    canonicalCompletedC3AmbientPortBoundaryReadout_eq_compressed]

/-! ## Diagonal audit against the completed Wronskian -/

/-- The completed TFVD Naimark response is nonzero throughout the operator
image of the open critical strip. -/
theorem completedC3SymplecticNaimarkState_ne_zero_of_mem_genuineCriticalStrip
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hzStrip.1 ≠ 0 := by
  intro hzero
  have hcamera :
      completedC3SymplecticCameraState
          (operatorHeightParameter z) hzStrip.1 = 0 := by
    apply realifiedNaimarkPort_injective
    simpa [completedC3SymplecticNaimarkState] using hzero
  have hleg := congrArg
    (fun state : RealifiedCameraComplexification => state.snd) hcamera
  apply completedC3LegCameraState_dirichletGradient_ne_zero hzStrip
  simpa [completedC3SymplecticCameraState] using hleg

/-- Consequently the full ambient boundary readout has a nonzero diagonal
away from the real spectral axis. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_diagonal_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3AmbientBoundaryReadout
        z z hzStrip.1 hzStrip.1 ≠ 0 := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_kernel z z hz hz]
  apply mul_ne_zero
  · rw [sub_ne_zero]
    intro hconj
    have him := congrArg Complex.im hconj
    simp only [Complex.conj_im] at him
    exact hz (by linarith)
  · apply inner_self_ne_zero.mpr
    intro hview
    apply
      completedC3SymplecticNaimarkState_ne_zero_of_mem_genuineCriticalStrip
        hzStrip
    change completedC3SymplecticNaimarkState
      (operatorHeightParameter z) hzStrip.1 = 0 at hview
    exact hview

/-- At a hypothetical off-critical Genuine zero the full ambient Green skew
cannot equal the completed scalar Wronskian: the former is nonzero on the
diagonal while the latter vanishes with the characteristic. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_ne_rawWronskian_at_offCriticalGenuineZero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) (hoff : s.re ≠ 1 / 2) :
    canonicalCompletedC3AmbientBoundaryReadout
        (centeredHeightParameter s) (centeredHeightParameter s)
        (by simpa using hs.1) (by simpa using hs.1) ≠
      canonicalCompletedC3RawHeightMixedWronskian
        (centeredHeightParameter s) (centeredHeightParameter s) := by
  have hz : (centeredHeightParameter s).im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hzStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hambient :=
    canonicalCompletedC3AmbientBoundaryReadout_diagonal_ne_zero hz hzStrip
  have hwronskian :
      canonicalCompletedC3RawHeightMixedWronskian
          (centeredHeightParameter s) (centeredHeightParameter s) = 0 :=
    canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
      hs hzero
  intro heq
  exact hambient (heq.trans hwronskian)

end

end CarrySelfAdjointOperator
