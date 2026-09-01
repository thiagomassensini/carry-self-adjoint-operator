import CarrySelfAdjointOperator.CompletedC3CausalChiralSourceCoherence
import Mathlib.Tactic

/-!
# Causal chiral defect Gram gate

The positive Wronskian readout and the coisometric camera/chiral readout are
already defined on the same enriched completed C3 source.  This module states
the route-B contraction only on the real-linear span of the actual causal
source family and separates its two logically distinct parts:

1. kernel compatibility, which makes a response-from-positive-readout map
   well defined on the causal range;
2. the norm inequality, which says that this map is contractive.

The second condition is exactly nonpositivity of the existing indefinite
boundary form.  Its specialization to a canonical source contradicts the
strictly positive boundary defect already proved at an upper-half-plane
native closure.

The fixed-parameter kernel condition is also audited against the finite
dimension of the positive trace.  Thirteen independent intrinsic camera
responses would refute it, so it cannot be promoted to a theorem merely from
causal-span membership or Naimark coherence.

No contraction, positivity, zero, spectral, or confinement statement is
assumed or proved here.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The two source-level gates -/

/-- Necessary well-definedness condition for a causal transformation from
the positive Wronskian readout to the coisometric camera/chiral readout. -/
def CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt
    (z : ℂ) : Prop :=
  ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
    state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
      canonicalCompletedC3EnrichedPositiveChiralReadout z state = 0 →
        canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state = 0

/-- Route-B defect-Gram condition on the actual causal source span.  The
orientation says that the coisometric camera/chiral response is contractive
relative to the positive Wronskian response. -/
def CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt
    (z : ℂ) : Prop :=
  ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
    state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ ^ 2 ≤
        ‖canonicalCompletedC3EnrichedPositiveChiralReadout z state‖ ^ 2

/-- Any causal contraction first satisfies the necessary kernel
compatibility.  This implication uses no finite-dimensionality or selected
inverse. -/
theorem canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_defectGram
    {z : ℂ}
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  intro state hstate hpositive
  have hnorm := hdefect state hstate
  simp only [hpositive, norm_zero, pow_two, zero_mul] at hnorm
  have hzero :
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ = 0 := by
    nlinarith [norm_nonneg
      (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state)]
  exact norm_eq_zero.mp hzero

/-! ## Exact kernel audit on the causal span -/

/-- Positive Wronskian readout restricted to the actual causal source span. -/
def canonicalCompletedC3CausalPositiveChiralReadout
    (z : ℂ) :
    canonicalCompletedC3CausalChiralSourceSubmodule →L[ℝ]
      CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (canonicalCompletedC3EnrichedPositiveChiralReadout z).comp
    canonicalCompletedC3CausalChiralSourceSubmodule.subtypeL

/-- Coisometric camera/chiral readout restricted to the same causal span. -/
def canonicalCompletedC3CausalCoisometricCameraChiralReadout
    (z : ℂ) :
    canonicalCompletedC3CausalChiralSourceSubmodule →L[ℝ]
      CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier :=
  (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z).comp
    canonicalCompletedC3CausalChiralSourceSubmodule.subtypeL

@[simp] theorem canonicalCompletedC3CausalPositiveChiralReadout_apply
    (z : ℂ) (state : canonicalCompletedC3CausalChiralSourceSubmodule) :
    canonicalCompletedC3CausalPositiveChiralReadout z state =
      canonicalCompletedC3EnrichedPositiveChiralReadout z state :=
  rfl

@[simp] theorem canonicalCompletedC3CausalCoisometricCameraChiralReadout_apply
    (z : ℂ) (state : canonicalCompletedC3CausalChiralSourceSubmodule) :
    canonicalCompletedC3CausalCoisometricCameraChiralReadout z state =
      canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state :=
  rfl

/-- The pointwise implication used by the proposed causal factorization is
literally inclusion of the two kernels after both readouts are restricted to
the same source span. -/
theorem canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_iff_ker_le
    (z : ℂ) :
    CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z ↔
      LinearMap.ker
          (canonicalCompletedC3CausalPositiveChiralReadout z).toLinearMap ≤
        LinearMap.ker
          (canonicalCompletedC3CausalCoisometricCameraChiralReadout z).toLinearMap := by
  constructor
  · intro hcompat state hpositive
    change canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state = 0
    exact hcompat state state.property hpositive
  · intro hker state hstate hpositive
    let causalState : canonicalCompletedC3CausalChiralSourceSubmodule :=
      ⟨state, hstate⟩
    have hpositive' :
        canonicalCompletedC3CausalPositiveChiralReadout z causalState = 0 :=
      hpositive
    have hcamera := hker hpositive'
    exact hcamera

/-- Kernel compatibility transfers linear independence backwards: a finite
family of causal sources distinguishable by the full camera/chiral response
must already be distinguishable by the fixed-parameter positive trace. -/
theorem canonicalCompletedC3CausalPositiveChiralReadout_linearIndependent_of_camera
    {ι : Type*} [Fintype ι] (z : ℂ)
    (source : ι → CanonicalCompletedC3EnrichedChiralSourceCarrier)
    (hsource : ∀ i, source i ∈
      canonicalCompletedC3CausalChiralSourceSubmodule)
    (hcompat : CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z)
    (hcamera : LinearIndependent ℝ
      (fun i =>
        canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z
          (source i))) :
    LinearIndependent ℝ
      (fun i => canonicalCompletedC3EnrichedPositiveChiralReadout z (source i)) := by
  rw [Fintype.linearIndependent_iff] at hcamera ⊢
  intro coeff hpositive i
  let state : CanonicalCompletedC3EnrichedChiralSourceCarrier :=
    ∑ j, coeff j • source j
  have hstate : state ∈ canonicalCompletedC3CausalChiralSourceSubmodule := by
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (hsource j)
  have hpositiveState :
      canonicalCompletedC3EnrichedPositiveChiralReadout z state = 0 := by
    simpa [state] using hpositive
  have hcameraState :
      canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state = 0 :=
    hcompat state hstate hpositiveState
  apply hcamera coeff
  simpa [state] using hcameraState

/-- In the upper half-plane, linear independence of the intrinsic camera
responses already implies independence of the larger camera/chiral outputs.
The negative chirality is not used: projection to the first coordinate and
the nonzero canonical square-root factor suffice. -/
theorem canonicalCompletedC3EnrichedCoisometricCameraChiralReadout_linearIndependent_of_camera
    {ι : Type*} (z : ℂ) (hzIm : 0 < z.im)
    (source : ι → CanonicalCompletedC3EnrichedChiralSourceCarrier)
    (hcamera : LinearIndependent ℝ
      (fun i => canonicalCompletedC3EnrichedCameraReadout (source i))) :
    LinearIndependent ℝ
      (fun i =>
        canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z
          (source i)) := by
  let firstCoordinate :
      CanonicalCompletedC3CoisometricCameraChiralEnergyCarrier →ₗ[ℝ]
        RealifiedCameraComplexification :=
    (WithLp.fstL 2 ℝ
      RealifiedCameraComplexification
      CanonicalCompletedC3FullWronskianOperatorCarrier).toLinearMap
  apply LinearIndependent.of_comp firstCoordinate
  let scaleUnit : ℝˣ :=
    Units.mk0 (Real.sqrt (2 * z.im)) (by positivity)
  have hscaled := hcamera.units_smul (fun _ : ι => scaleUnit)
  change LinearIndependent ℝ
    (fun i => (scaleUnit : ℝ) •
      canonicalCompletedC3EnrichedCameraReadout (source i)) at hscaled
  convert hscaled using 1
  funext i
  rfl

/-- The full completed-Wronskian trace carrier has real dimension twelve:
three complex boundary pairs.  The positive projection lands in a smaller
subspace, but this coarse dimension is already enough for the audit below. -/
theorem finrank_real_canonicalCompletedC3FullWronskianOperatorCarrier :
    Module.finrank ℝ CanonicalCompletedC3FullWronskianOperatorCarrier = 12 := by
  change Module.finrank ℝ
      (WithLp 2
        (WithLp 2 (ℂ × ℂ) ×
          WithLp 2 (WithLp 2 (ℂ × ℂ) × WithLp 2 (ℂ × ℂ)))) = 12
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]
  rw [Module.finrank_prod]
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]
  rw [Module.finrank_prod]
  rw [Module.finrank_prod]
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]
  simp

/-- No thirteen vectors in the fixed-parameter positive trace carrier can be
real-linearly independent. -/
theorem not_linearIndependent_canonicalCompletedC3CausalPositiveChiralReadout_fin13
    (z : ℂ)
    (source : Fin 13 → CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    ¬ LinearIndependent ℝ
      (fun i => canonicalCompletedC3EnrichedPositiveChiralReadout z (source i)) := by
  intro hlinear
  have hcard := hlinear.fintype_card_le_finrank
  rw [finrank_real_canonicalCompletedC3FullWronskianOperatorCarrier] at hcard
  norm_num at hcard

/-- Concrete finite-rank obstruction to the proposed kernel gate.  Any
thirteen causal sources whose full camera/chiral responses are independent
refute fixed-parameter kernel compatibility.  Establishing such a family is
therefore the precise next test; no Gram or positivity premise is involved. -/
theorem not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_cameraIndependent
    (z : ℂ)
    (source : Fin 13 → CanonicalCompletedC3EnrichedChiralSourceCarrier)
    (hsource : ∀ i, source i ∈
      canonicalCompletedC3CausalChiralSourceSubmodule)
    (hcamera : LinearIndependent ℝ
      (fun i =>
        canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z
          (source i))) :
    ¬ CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  intro hcompat
  exact
    not_linearIndependent_canonicalCompletedC3CausalPositiveChiralReadout_fin13
      z source
      (canonicalCompletedC3CausalPositiveChiralReadout_linearIndependent_of_camera
        z source hsource hcompat hcamera)

/-- Intrinsic-camera spelling of the finite-rank obstruction.  Thus the
remaining concrete audit is only independence of thirteen canonical camera
responses; neither the negative chirality nor a Gram identity is needed. -/
theorem not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_intrinsicCameraIndependent
    (z : ℂ) (hzIm : 0 < z.im)
    (source : Fin 13 → CanonicalCompletedC3EnrichedChiralSourceCarrier)
    (hsource : ∀ i, source i ∈
      canonicalCompletedC3CausalChiralSourceSubmodule)
    (hcamera : LinearIndependent ℝ
      (fun i => canonicalCompletedC3EnrichedCameraReadout (source i))) :
    ¬ CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  exact
    not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_cameraIndependent
      z source hsource
      (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout_linearIndependent_of_camera
        z hzIm source hcamera)

/-- Canonical-source specialization of the obstruction.  It names the exact
remaining object: thirteen completed symplectic camera states sampled from
the genuine strip. -/
theorem not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_symplecticCameraIndependent
    (z : ℂ) (hzIm : 0 < z.im)
    (point : Fin 13 → ℂ)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈ genuineCriticalStrip)
    (hcamera : LinearIndependent ℝ
      (fun i => completedC3SymplecticCameraState
        (operatorHeightParameter (point i)) (hstrip i).1)) :
    ¬ CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  let source : Fin 13 → CanonicalCompletedC3EnrichedChiralSourceCarrier :=
    fun i => canonicalCompletedC3EnrichedChiralSourceState
      (point i) (hstrip i)
  apply
    not_canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_fin13_intrinsicCameraIndependent
      z hzIm source
  · intro i
    exact canonicalCompletedC3EnrichedChiralSourceState_mem_causalSubmodule
      (point i) (hstrip i)
  · simpa only [source,
      canonicalCompletedC3EnrichedCameraReadout_sourceState] using hcamera

/-! ## Exact boundary-form spelling -/

/-- On a readout of one enriched source, the indefinite boundary form is the
coisometric norm square minus the positive Wronskian norm square. -/
theorem canonicalCompletedC3CausalChiralBoundaryForm_readout_self
    (z : ℂ) (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state)
        (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state) =
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ ^ 2 -
        ‖canonicalCompletedC3EnrichedPositiveChiralReadout z state‖ ^ 2 := by
  unfold canonicalCompletedC3CausalChiralBoundaryForm
    canonicalCompletedC3EnrichedCausalChiralBoundaryReadout
  change
    inner ℝ
          (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state)
          (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state) -
        inner ℝ
          (canonicalCompletedC3EnrichedPositiveChiralReadout z state)
          (canonicalCompletedC3EnrichedPositiveChiralReadout z state) = _
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The source-level contraction is exactly nonpositivity of the existing
indefinite boundary form on the image of every causal source. -/
theorem canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_iff_boundaryForm
    (z : ℂ) :
    CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z ↔
      ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
        state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
          canonicalCompletedC3CausalChiralBoundaryForm
              (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state)
              (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state) ≤ 0 := by
  constructor
  · intro hdefect state hstate
    rw [canonicalCompletedC3CausalChiralBoundaryForm_readout_self]
    exact sub_nonpos.mpr (hdefect state hstate)
  · intro hform state hstate
    exact sub_nonpos.mp (by
      rw [← canonicalCompletedC3CausalChiralBoundaryForm_readout_self]
      exact hform state hstate)

/-! ## Canonical specialization and upper-half-plane exclusion -/

/-- A causal defect-Gram contraction makes the concrete canonical boundary
datum nonpositive. -/
theorem canonicalCompletedC3CausalChiralBoundaryForm_self_nonpos_of_defectGram
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedC3CausalChiralBoundaryState M z hzStrip.1)
        (canonicalCompletedC3CausalChiralBoundaryState M z hzStrip.1) ≤ 0 := by
  rw [← canonicalCompletedC3EnrichedCausalChiralBoundaryReadout_sourceState
    M z hzStrip]
  exact
    (canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_iff_boundaryForm
      z).mp hdefect
      (canonicalCompletedC3EnrichedChiralSourceState z hzStrip)
      (canonicalCompletedC3EnrichedChiralSourceState_mem_causalSubmodule
        z hzStrip)

/-- The causal defect-Gram contraction excludes a native bracket closure at
every strictly upper-half-plane point. -/
theorem not_nativeCarryLogWaveBoundaryCloses_of_causalChiralDefectGram
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    ¬ NativeCarryLogWaveBoundaryCloses z := by
  intro hclose
  have hpos :=
    canonicalCompletedC3CausalChiralBoundaryForm_self_pos_of_nativeCarryLogWaveBoundaryCloses
      M z hzIm hzStrip hclose
  have hnonpos :=
    canonicalCompletedC3CausalChiralBoundaryForm_self_nonpos_of_defectGram
      M z hzStrip hdefect
  linarith

/-- In the closed upper half-plane, a native bracket closure and the causal
defect-Gram contraction force the centered height to be real. -/
theorem nativeCarryLogWaveBoundaryCloses_im_eq_zero_of_causalChiralDefectGram
    (M : ℕ) (z : ℂ) (hzIm : 0 ≤ z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hclose : NativeCarryLogWaveBoundaryCloses z)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    z.im = 0 := by
  by_contra hne
  have hpos : 0 < z.im := lt_of_le_of_ne hzIm (Ne.symm hne)
  exact
    (not_nativeCarryLogWaveBoundaryCloses_of_causalChiralDefectGram
      M z hpos hzStrip hdefect) hclose

end

end CarrySelfAdjointOperator
