import CarrySelfAdjointOperator.CompletedC3CompressedResolventClosure
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import CarrySelfAdjointOperator.CompletedC3AllOrderGammaWronskianLimitGate

/-!
# Boundary readout of the closed compressed C3 realization

The closed compressed resolvent has its own intrinsic source, obtained as the
strong limit of the finite logarithmic defects.  This module keeps that source
and defines the corresponding uncollapsed two-point boundary skew.  Both the
response and source converge strongly, so the finite boundary readings pass
to the completed camera Hilbert space without an ambient no-leak premise.
-/

open scoped ComplexConjugate InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- One-coordinate compression of logarithmic multiplication is symmetric on
its pullback domain. -/
theorem inner_naimarkAdjoint_logarithmicMultiplication_naimarkIsometry_comm
    (u v : CameraHilbert)
    (hu : naimarkIsometry u ∈ logarithmicMultiplication.domain)
    (hv : naimarkIsometry v ∈ logarithmicMultiplication.domain) :
    inner Real
        (naimarkAdjoint
          (logarithmicMultiplication ⟨naimarkIsometry u, hu⟩)) v =
      inner Real u
        (naimarkAdjoint
          (logarithmicMultiplication ⟨naimarkIsometry v, hv⟩)) := by
  rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl,
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_left,
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right]
  exact logarithmicMultiplication_isFormalAdjoint
    ⟨naimarkIsometry u, hu⟩ ⟨naimarkIsometry v, hv⟩

/-- Formal symmetry of the compression retains both complex quadratures. -/
theorem inner_complex_compressedLogarithmicMultiplication_comm
    (u v : realifiedCompressedLogarithmicMultiplication.domain) :
    inner Complex
        (canonicalCompletedC3GammaCameraView
          (realifiedCompressedLogarithmicMultiplication u))
        (canonicalCompletedC3GammaCameraView
          (v : RealifiedCameraComplexification)) =
      inner Complex
        (canonicalCompletedC3GammaCameraView
          (u : RealifiedCameraComplexification))
        (canonicalCompletedC3GammaCameraView
          (realifiedCompressedLogarithmicMultiplication v)) := by
  have huFst : naimarkIsometry
      (u : RealifiedCameraComplexification).fst ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_fst] using u.property.1
  have huSnd : naimarkIsometry
      (u : RealifiedCameraComplexification).snd ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_snd] using u.property.2
  have hvFst : naimarkIsometry
      (v : RealifiedCameraComplexification).fst ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_fst] using v.property.1
  have hvSnd : naimarkIsometry
      (v : RealifiedCameraComplexification).snd ∈
        logarithmicMultiplication.domain := by
    simpa only [realifiedNaimarkPort_snd] using v.property.2
  have huLiftFst : (realifiedCompressedLogarithmicDomainLift u).1 =
      (⟨naimarkIsometry (u : RealifiedCameraComplexification).fst,
        huFst⟩ : logarithmicMultiplication.domain) := by
    apply Subtype.ext
    change (realifiedNaimarkPort
      (u : RealifiedCameraComplexification)).fst = _
    rw [realifiedNaimarkPort_fst]
  have huLiftSnd : (realifiedCompressedLogarithmicDomainLift u).2 =
      (⟨naimarkIsometry (u : RealifiedCameraComplexification).snd,
        huSnd⟩ : logarithmicMultiplication.domain) := by
    apply Subtype.ext
    change (realifiedNaimarkPort
      (u : RealifiedCameraComplexification)).snd = _
    rw [realifiedNaimarkPort_snd]
  have hvLiftFst : (realifiedCompressedLogarithmicDomainLift v).1 =
      (⟨naimarkIsometry (v : RealifiedCameraComplexification).fst,
        hvFst⟩ : logarithmicMultiplication.domain) := by
    apply Subtype.ext
    change (realifiedNaimarkPort
      (v : RealifiedCameraComplexification)).fst = _
    rw [realifiedNaimarkPort_fst]
  have hvLiftSnd : (realifiedCompressedLogarithmicDomainLift v).2 =
      (⟨naimarkIsometry (v : RealifiedCameraComplexification).snd,
        hvSnd⟩ : logarithmicMultiplication.domain) := by
    apply Subtype.ext
    change (realifiedNaimarkPort
      (v : RealifiedCameraComplexification)).snd = _
    rw [realifiedNaimarkPort_snd]
  have h11 :=
    inner_naimarkAdjoint_logarithmicMultiplication_naimarkIsometry_comm
      (u : RealifiedCameraComplexification).fst
      (v : RealifiedCameraComplexification).fst huFst hvFst
  have h12 :=
    inner_naimarkAdjoint_logarithmicMultiplication_naimarkIsometry_comm
      (u : RealifiedCameraComplexification).fst
      (v : RealifiedCameraComplexification).snd huFst hvSnd
  have h21 :=
    inner_naimarkAdjoint_logarithmicMultiplication_naimarkIsometry_comm
      (u : RealifiedCameraComplexification).snd
      (v : RealifiedCameraComplexification).fst huSnd hvFst
  have h22 :=
    inner_naimarkAdjoint_logarithmicMultiplication_naimarkIsometry_comm
      (u : RealifiedCameraComplexification).snd
      (v : RealifiedCameraComplexification).snd huSnd hvSnd
  apply Complex.ext
  · simp only [canonicalCompletedC3GammaCameraView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    change
      inner Real
          (realifiedCompressedLogarithmicMultiplication u).fst
          (v : RealifiedCameraComplexification).fst +
        inner Real
          (realifiedCompressedLogarithmicMultiplication u).snd
          (v : RealifiedCameraComplexification).snd =
      inner Real (u : RealifiedCameraComplexification).fst
          (realifiedCompressedLogarithmicMultiplication v).fst +
        inner Real (u : RealifiedCameraComplexification).snd
          (realifiedCompressedLogarithmicMultiplication v).snd
    simp only [realifiedCompressedLogarithmicMultiplication_apply,
      realifiedLogarithmicMultiplication_fst,
      realifiedLogarithmicMultiplication_snd,
      realifiedNaimarkAdjoint_fst, realifiedNaimarkAdjoint_snd]
    rw [huLiftFst, huLiftSnd, hvLiftFst, hvLiftSnd]
    exact congrArg₂ (· + ·) h11 h22
  · simp only [canonicalCompletedC3GammaCameraView,
      RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_im]
    change
      inner Real
          (realifiedCompressedLogarithmicMultiplication u).fst
          (v : RealifiedCameraComplexification).snd -
        inner Real
          (realifiedCompressedLogarithmicMultiplication u).snd
          (v : RealifiedCameraComplexification).fst =
      inner Real (u : RealifiedCameraComplexification).fst
          (realifiedCompressedLogarithmicMultiplication v).snd -
        inner Real (u : RealifiedCameraComplexification).snd
          (realifiedCompressedLogarithmicMultiplication v).fst
    simp only [realifiedCompressedLogarithmicMultiplication_apply,
      realifiedLogarithmicMultiplication_fst,
      realifiedLogarithmicMultiplication_snd,
      realifiedNaimarkAdjoint_fst, realifiedNaimarkAdjoint_snd]
    rw [huLiftFst, huLiftSnd, hvLiftFst, hvLiftSnd]
    exact congrArg₂ (· - ·) h12 h21

/-- The transported compressed scalar block is literal complex scalar
multiplication on the two-quadrature camera carrier. -/
theorem canonicalCompletedC3GammaCameraView_compressedScalar
    (z : Complex) (u : RealifiedCameraComplexification) :
    canonicalCompletedC3GammaCameraView (realifiedCompressedScalar z u) =
      z • canonicalCompletedC3GammaCameraView u := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (realifiedCompressedScalar z u).fst =
      z.re • u.fst - z.im • u.snd
    exact realifiedCompressedScalar_fst z u
  · change (realifiedCompressedScalar z u).snd =
      z.im • u.fst + z.re • u.snd
    exact realifiedCompressedScalar_snd z u

/-- Two-point boundary skew generated by the intrinsic compressed defect
sources of arbitrary domain vectors. -/
def canonicalCompletedC3CompressedDefectBoundaryReadout
    (z w : Complex)
    (u v : realifiedCompressedLogarithmicMultiplication.domain) : Complex :=
  inner Complex
      (canonicalCompletedC3GammaCameraView
        (u : RealifiedCameraComplexification))
      (canonicalCompletedC3GammaCameraView
        (realifiedCompressedLogarithmicDefectSource w v)) -
    inner Complex
      (canonicalCompletedC3GammaCameraView
        (realifiedCompressedLogarithmicDefectSource z u))
      (canonicalCompletedC3GammaCameraView
        (v : RealifiedCameraComplexification))

/-- The intrinsic compressed boundary skew is exactly spectral separation
times the positive two-point Gram of the same response vectors. -/
theorem canonicalCompletedC3CompressedDefectBoundaryReadout_eq_kernel
    (z w : Complex)
    (u v : realifiedCompressedLogarithmicMultiplication.domain) :
    canonicalCompletedC3CompressedDefectBoundaryReadout z w u v =
      (w - conj z) *
        inner Complex
          (canonicalCompletedC3GammaCameraView
            (u : RealifiedCameraComplexification))
          (canonicalCompletedC3GammaCameraView
            (v : RealifiedCameraComplexification)) := by
  unfold canonicalCompletedC3CompressedDefectBoundaryReadout
    realifiedCompressedLogarithmicDefectSource
  rw [canonicalCompletedC3GammaCameraView_sub,
    canonicalCompletedC3GammaCameraView_sub,
    canonicalCompletedC3GammaCameraView_compressedScalar,
    canonicalCompletedC3GammaCameraView_compressedScalar,
    inner_sub_right, inner_sub_left,
    inner_complex_compressedLogarithmicMultiplication_comm]
  simp only [inner_smul_right, inner_smul_left]
  ring

/-- Boundary skew of the finite compressed response and its actual compressed
logarithmic defect source. -/
def canonicalCompletedC3FiniteCompressedBoundaryReadout
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z w : Complex) : Complex :=
  inner Complex
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)) -
    inner Complex
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff w : RealifiedCameraComplexification))

/-- The finite boundary readout uses exactly the intrinsic compressed defect
of each finite response vector. -/
theorem canonicalCompletedC3FiniteCompressedBoundaryReadout_eq_defect
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z w : Complex) :
    canonicalCompletedC3FiniteCompressedBoundaryReadout hbase cutoff z w =
      canonicalCompletedC3CompressedDefectBoundaryReadout z w
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z)
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff w) := by
  unfold canonicalCompletedC3FiniteCompressedBoundaryReadout
    canonicalCompletedC3CompressedDefectBoundaryReadout
  rw [← canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect
      hbase cutoff z,
    ← canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_eq_defect
      hbase cutoff w]

/-- Exact finite compressed Green identity, before passage to completion. -/
theorem canonicalCompletedC3FiniteCompressedBoundaryReadout_eq_kernel
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z w : Complex) :
    canonicalCompletedC3FiniteCompressedBoundaryReadout hbase cutoff z w =
      (w - conj z) *
        inner Complex
          (canonicalCompletedC3GammaCameraView
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff z : RealifiedCameraComplexification))
          (canonicalCompletedC3GammaCameraView
            (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
              hbase cutoff w : RealifiedCameraComplexification)) := by
  rw [canonicalCompletedC3FiniteCompressedBoundaryReadout_eq_defect]
  exact canonicalCompletedC3CompressedDefectBoundaryReadout_eq_kernel _ _ _ _

/-- Boundary skew of the completed compressed response and the Riesz vectors
representing the two intrinsic source limits. -/
def canonicalCompletedC3CompressedBoundaryReadout
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw) : Complex :=
  inner Complex
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter z) hz))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CompressedHilbertSource w hw hboundW)) -
    inner Complex
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CompressedHilbertSource z hz hboundZ))
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter w) hw))

/-- Strong convergence of response and source passes the finite compressed
boundary skew to its intrinsic completed readout. -/
theorem canonicalCompletedC3FiniteCompressedBoundaryReadout_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw)
    (hsourceZ : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hz hboundZ)))
    (hsourceW : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource w hw hboundW))) :
    Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3FiniteCompressedBoundaryReadout
          hbase cutoff z w)
      atTop
      (nhds (canonicalCompletedC3CompressedBoundaryReadout
        z w hz hw hboundZ hboundW)) := by
  have hstateZ :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase z hz
  have hstateW :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase w hw
  have hstateZG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter z) hz))) :=
    hstateZ
  have hstateWG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff w : RealifiedCameraComplexification))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter w) hw))) :=
    hstateW
  have hsourceZG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CompressedHilbertSource z hz hboundZ))) :=
    hsourceZ
  have hsourceWG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CompressedHilbertSource w hw hboundW))) :=
    hsourceW
  have hfirst := Filter.Tendsto.inner (𝕜 := Complex) hstateZG hsourceWG
  have hsecond := Filter.Tendsto.inner (𝕜 := Complex) hsourceZG hstateWG
  exact (hfirst.sub hsecond).congr'
    (Eventually.of_forall fun cutoff => rfl)

/-- The completed intrinsic boundary readout retains the same exact Green
identity as every finite cutoff. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw)
    (hsourceZ : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hz hboundZ)))
    (hsourceW : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource w hw hboundW))) :
    canonicalCompletedC3CompressedBoundaryReadout
        z w hz hw hboundZ hboundW =
      (w - conj z) *
        inner Complex
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter z) hz))
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter w) hw)) := by
  have hboundary :=
    canonicalCompletedC3FiniteCompressedBoundaryReadout_tendsto
      hbase z w hz hw hboundZ hboundW hsourceZ hsourceW
  have hstateZ :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase z hz
  have hstateW :=
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_tendsto
      hbase w hw
  have hstateZG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff z : RealifiedCameraComplexification))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter z) hz))) :=
    hstateZ
  have hstateWG : Tendsto
      (fun cutoff : Nat => canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
          hbase cutoff w : RealifiedCameraComplexification))
      atTop
      (nhds (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter w) hw))) :=
    hstateW
  have hkernel :=
    (Filter.Tendsto.inner (𝕜 := Complex) hstateZG hstateWG).const_mul
      (w - conj z)
  have hfinite : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3FiniteCompressedBoundaryReadout
          hbase cutoff z w)
      atTop
      (nhds ((w - conj z) *
        inner Complex
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter z) hz))
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter w) hw)))) :=
    hkernel.congr' (Eventually.of_forall fun cutoff =>
      (canonicalCompletedC3FiniteCompressedBoundaryReadout_eq_kernel
        hbase cutoff z w).symm)
  exact tendsto_nhds_unique hboundary hfinite

/-- The tail theorem therefore constructs both intrinsic completed sources
and proves convergence of their finite two-point boundary readings. -/
theorem exists_canonicalCompletedC3CompressedBoundaryReadout_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    ∃ hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz,
      ∃ hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw,
        Tendsto
          (fun cutoff : Nat =>
            canonicalCompletedC3FiniteCompressedBoundaryReadout
              hbase cutoff z w)
          atTop
          (nhds (canonicalCompletedC3CompressedBoundaryReadout
            z w hz hw hboundZ hboundW)) := by
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase z hz with ⟨hboundZ, hsourceZ⟩
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase w hw with ⟨hboundW, hsourceW⟩
  exact ⟨hboundZ, hboundW,
    canonicalCompletedC3FiniteCompressedBoundaryReadout_tendsto
      hbase z w hz hw hboundZ hboundW hsourceZ hsourceW⟩

/-- The same sources can be chosen so that both boundary convergence and the
completed Green identity are available together. -/
theorem exists_canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    ∃ hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz,
      ∃ hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw,
        canonicalCompletedC3CompressedBoundaryReadout
            z w hz hw hboundZ hboundW =
          (w - conj z) *
            inner Complex
              (canonicalCompletedC3GammaCameraView
                (completedC3SymplecticCameraState
                  (operatorHeightParameter z) hz))
              (canonicalCompletedC3GammaCameraView
                (completedC3SymplecticCameraState
                  (operatorHeightParameter w) hw)) := by
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase z hz with ⟨hboundZ, hsourceZ⟩
  rcases exists_canonicalCompletedC3CompressedHilbertSource_tendsto
      hbase w hw with ⟨hboundW, hsourceW⟩
  exact ⟨hboundZ, hboundW,
    canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
      hbase z w hz hw hboundZ hboundW hsourceZ hsourceW⟩

/-- Exact spelling of the remaining compressed boundary/Wronskian sewing.
After graph closure and source convergence, no domain or limit gate remains:
the desired equality is precisely the equality of the positive response Gram
with the completed scalar Wronskian. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_eq_wronskian_iff_kernel
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw)
    (hsourceZ : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hz hboundZ)))
    (hsourceW : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource w hw hboundW))) :
    canonicalCompletedC3CompressedBoundaryReadout
          z w hz hw hboundZ hboundW =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z ↔
      (w - conj z) *
          inner Complex
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                (operatorHeightParameter z) hz))
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                (operatorHeightParameter w) hw)) =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    hbase z w hz hw hboundZ hboundW hsourceZ hsourceW]

/-- The intrinsic compressed boundary is nonzero on the diagonal away from
the real height axis.  This follows from the nonzero completed TFVD source,
not from a characteristic-zero or spectral premise. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_diagonal_ne_zero
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {z : Complex} (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1)
    (hsource : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzStrip.1 hbound))) :
    canonicalCompletedC3CompressedBoundaryReadout
        z z hzStrip.1 hzStrip.1 hbound hbound ≠ 0 := by
  rw [canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    hbase z z hzStrip.1 hzStrip.1 hbound hbound hsource hsource]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro hconj
    apply hzIm
    exact Complex.conj_eq_iff_im.mp hconj.symm
  · apply inner_self_ne_zero.mpr
    intro hzero
    apply canonicalCompletedC3AllOrderSymplecticGammaCameraSource_ne_zero hzStrip
    change completedC3SymplecticCameraState
      (operatorHeightParameter z) hzStrip.1 =
        (0 : RealifiedCameraComplexification)
    exact hzero

/-- Therefore identifying the intrinsic compressed boundary with the
completed Wronskian at a hypothetical off-axis characteristic zero is
impossible.  The remaining sewing has exactly confinement strength; it is not
a consequence of graph closure alone. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_ne_wronskian_of_characteristicZero
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {z : Complex} (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1)
    (hsource : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzStrip.1 hbound))) :
    canonicalCompletedC3CompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 hbound hbound ≠
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z := by
  rw [show completedGreenWronskian
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion z z = 0 by
    simp [completedGreenWronskian, hzero]]
  exact canonicalCompletedC3CompressedBoundaryReadout_diagonal_ne_zero
    hbase hzIm hzStrip hbound hsource

/-- On the real height axis the intrinsic compressed diagonal boundary and
the completed Wronskian agree unconditionally: both vanish by Hermitian
separation and centered Schwarz reflection. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_ofReal_diagonal_eq_wronskian
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (t : Real)
    (hbound : CanonicalCompletedC3CompressedSourceFormBounded
      (t : Complex) (by norm_num [operatorHeightParameter]))
    (hsource : Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff (t : Complex))
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        (t : Complex) (by norm_num [operatorHeightParameter]) hbound))) :
    canonicalCompletedC3CompressedBoundaryReadout
          (t : Complex) (t : Complex)
          (by norm_num [operatorHeightParameter])
          (by norm_num [operatorHeightParameter]) hbound hbound =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (t : Complex) (t : Complex) := by
  have hstrip : operatorHeightParameter (t : Complex) ∈
      genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hvalue : conj (completedNativeOperatorCharacteristic (t : Complex)) =
      completedNativeOperatorCharacteristic (t : Complex) := by
    have hreflection :=
      completedNativeOperatorCharacteristic_centeredReflection_via_nativeConjugation
        hstrip
    simpa using hreflection.symm
  have hcompanion : conj
      (completedNativeOperatorBoundaryCompanion (t : Complex)) =
        completedNativeOperatorBoundaryCompanion (t : Complex) := by
    have hreflection :=
      completedNativeOperatorBoundaryCompanion_centeredReflection hstrip
    simpa using hreflection.symm
  rw [canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    hbase (t : Complex) (t : Complex)
      (by norm_num [operatorHeightParameter])
      (by norm_num [operatorHeightParameter])
      hbound hbound hsource hsource]
  have hsep : (t : Complex) - conj (t : Complex) = 0 := by simp
  rw [hsep, zero_mul]
  unfold completedGreenWronskian
  rw [hvalue, hcompanion]
  ring

end

end CarrySelfAdjointOperator
