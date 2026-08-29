import CarrySelfAdjointOperator.CompletedC3WronskianResolventRealizationProbe
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import Mathlib.Tactic

open scoped ComplexConjugate InnerProductSpace lp ENNReal MeasureTheory
open Set MeasureTheory

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

def minimalSlopeCamera : CameraIndex :=
  completedC3RealCameraIndex 1

@[simp] theorem minimalSlopeCamera_label :
    cameraLabel minimalSlopeCamera = 3 := by
  rfl

@[simp] theorem minimalSlopeCamera_slope :
    cameraSlope (cameraLabel minimalSlopeCamera) = 3 := by
  norm_num [minimalSlopeCamera, completedC3RealCameraIndex, cameraLabel,
    cameraSlope]

theorem minimalSlopeCamera_slope_le (camera : CameraIndex) :
    cameraSlope (cameraLabel minimalSlopeCamera) <=
      cameraSlope (cameraLabel camera) := by
  rw [minimalSlopeCamera_slope]
  simp only [cameraLabel]
  by_cases htwo : (camera : Nat) = 2
  · simp [htwo]
  · rw [cameraSlope_of_ne_two htwo]
    omega

theorem cameraInterval_minimalSlopeCamera_inter (camera : CameraIndex) :
    cameraInterval minimalSlopeCamera ∩ cameraInterval camera =
      cameraInterval minimalSlopeCamera := by
  rw [inter_eq_left]
  intro x hx
  exact ⟨hx.1, le_trans hx.2
    (by exact_mod_cast minimalSlopeCamera_slope_le camera)⟩

theorem integral_indicator_minimalSlopeCamera_centeredCoordinate :
    ∫ x,
        (cameraInterval minimalSlopeCamera).indicator
          (fun x =>
            logarithmicCoordinate x -
              Real.log (cameraSlope (cameraLabel minimalSlopeCamera) : Real)) x
      ∂positiveLebesgueMeasure = 0 := by
  rw [MeasureTheory.integral_indicator
    (cameraInterval_measurable minimalSlopeCamera)]
  have hrestrict :
      positiveLebesgueMeasure.restrict (cameraInterval minimalSlopeCamera) =
        volume.restrict (cameraInterval minimalSlopeCamera) := by
    rw [positiveLebesgueMeasure,
      Measure.restrict_restrict_of_subset
        (cameraInterval_subset_positive minimalSlopeCamera)]
  rw [hrestrict, cameraInterval]
  rw [← intervalIntegral.integral_of_le
    (show (0 : Real) <=
      cameraSlope (cameraLabel minimalSlopeCamera) by positivity)]
  simp [logarithmicCoordinate]

theorem inner_centeredMinimalSlopeCamera_naimarkCameraVector
    (camera : CameraIndex) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (naimarkCameraVector camera) = 0 := by
  rw [L2.inner_def]
  calc
    ∫ x,
        inner Real ((centeredNaimarkCameraVector minimalSlopeCamera) x)
          ((naimarkCameraVector camera) x) ∂positiveLebesgueMeasure =
      ∫ x,
        inner Real (kolmogorovVector minimalSlopeCamera)
            (kolmogorovVector camera) *
          (cameraInterval minimalSlopeCamera).indicator
            (fun x => logarithmicCoordinate x -
              Real.log
                (cameraSlope (cameraLabel minimalSlopeCamera) : Real)) x
        ∂positiveLebesgueMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [centeredNaimarkCameraVector_coeFn minimalSlopeCamera,
          naimarkCameraVector_coeFn camera] with x hcentered hcamera
      rw [hcentered, hcamera]
      by_cases hmin : x ∈ cameraInterval minimalSlopeCamera
      · have hlarge : x ∈ cameraInterval camera :=
          (show cameraInterval minimalSlopeCamera ⊆ cameraInterval camera by
            rw [← inter_eq_left]
            exact cameraInterval_minimalSlopeCamera_inter camera) hmin
        simp only [Set.indicator_of_mem hmin, Set.indicator_of_mem hlarge,
          real_inner_smul_left]
        ring
      · simp [Set.indicator_of_notMem hmin]
    _ = inner Real (kolmogorovVector minimalSlopeCamera)
          (kolmogorovVector camera) * 0 := by
      rw [MeasureTheory.integral_const_mul,
        integral_indicator_minimalSlopeCamera_centeredCoordinate]
    _ = 0 := by ring

theorem integral_indicator_minimalSlopeCamera_centered_mul_coordinate :
    ∫ x,
        (cameraInterval minimalSlopeCamera).indicator
          (fun x =>
            (logarithmicCoordinate x -
                Real.log
                  (cameraSlope (cameraLabel minimalSlopeCamera) : Real)) *
              logarithmicCoordinate x) x
      ∂positiveLebesgueMeasure =
    (cameraSlope (cameraLabel minimalSlopeCamera) : Real) := by
  rw [MeasureTheory.integral_indicator
    (cameraInterval_measurable minimalSlopeCamera)]
  have hrestrict :
      positiveLebesgueMeasure.restrict (cameraInterval minimalSlopeCamera) =
        volume.restrict (cameraInterval minimalSlopeCamera) := by
    rw [positiveLebesgueMeasure,
      Measure.restrict_restrict_of_subset
        (cameraInterval_subset_positive minimalSlopeCamera)]
  rw [hrestrict, cameraInterval]
  rw [← intervalIntegral.integral_of_le
    (show (0 : Real) <=
      cameraSlope (cameraLabel minimalSlopeCamera) by positivity)]
  let b : Real := cameraSlope (cameraLabel minimalSlopeCamera)
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast cameraSlope_pos minimalSlopeCamera
  have hone : IntervalIntegrable logarithmicCoordinate volume 0 b := by
    change IntervalIntegrable (fun x : Real => 1 + Real.log x) volume 0 b
    exact NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLog_zero
  have htwo : IntervalIntegrable
      (fun x : Real => logarithmicCoordinate x ^ 2) volume 0 b := by
    change IntervalIntegrable (fun x : Real => (1 + Real.log x) ^ 2)
      volume 0 b
    exact
      NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLogSq_zero hb
  have hcentered : IntervalIntegrable
      (fun x : Real => logarithmicCoordinate x - Real.log b)
      volume 0 b := by
    exact hone.sub intervalIntegrable_const
  have hsquared : IntervalIntegrable
      (fun x : Real => (logarithmicCoordinate x - Real.log b) ^ 2)
      volume 0 b := by
    have hpoly : IntervalIntegrable
        (fun x : Real =>
          logarithmicCoordinate x ^ 2 -
            (2 * Real.log b) * logarithmicCoordinate x + Real.log b ^ 2)
        volume 0 b :=
      (htwo.sub (hone.const_mul _)).add intervalIntegrable_const
    exact hpoly.congr fun x hx => by ring
  calc
    ∫ x in 0..b,
        (logarithmicCoordinate x - Real.log b) * logarithmicCoordinate x =
      ∫ x in 0..b,
        (logarithmicCoordinate x - Real.log b) ^ 2 +
          Real.log b * (logarithmicCoordinate x - Real.log b) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (∫ x in 0..b,
          (logarithmicCoordinate x - Real.log b) ^ 2) +
        Real.log b *
          (∫ x in 0..b,
            logarithmicCoordinate x - Real.log b) := by
      rw [intervalIntegral.integral_add hsquared
        (hcentered.const_mul _), intervalIntegral.integral_const_mul]
    _ = b := by
      rw [integral_logarithmicCoordinate_sub_log_sq hb]
      have hzero :
          ∫ x in 0..b,
              logarithmicCoordinate x - Real.log b = 0 := by
        simp [logarithmicCoordinate]
      rw [hzero]
      ring

theorem inner_centeredMinimalSlopeCamera_logarithmicCameraVector
    (camera : CameraIndex) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (logarithmicMultiplication
          ⟨naimarkCameraVector camera,
            naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩) =
      inner Real (naimarkCameraVector minimalSlopeCamera)
        (naimarkCameraVector camera) := by
  rw [L2.inner_def]
  calc
    ∫ x,
        inner Real ((centeredNaimarkCameraVector minimalSlopeCamera) x)
          ((logarithmicMultiplication
            ⟨naimarkCameraVector camera,
              naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩) x)
        ∂positiveLebesgueMeasure =
      ∫ x,
        inner Real (kolmogorovVector minimalSlopeCamera)
            (kolmogorovVector camera) *
          (cameraInterval minimalSlopeCamera).indicator
            (fun x =>
              (logarithmicCoordinate x -
                  Real.log
                    (cameraSlope
                      (cameraLabel minimalSlopeCamera) : Real)) *
                logarithmicCoordinate x) x
        ∂positiveLebesgueMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards
        [centeredNaimarkCameraVector_coeFn minimalSlopeCamera,
          logarithmicMultiplication_coeFn
            ⟨naimarkCameraVector camera,
              naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩,
          naimarkCameraVector_coeFn camera] with x hcentered hlog hcamera
      rw [hcentered, hlog, logarithmicWeightedFunction, hcamera]
      by_cases hmin : x ∈ cameraInterval minimalSlopeCamera
      · have hlarge : x ∈ cameraInterval camera :=
          (show cameraInterval minimalSlopeCamera ⊆ cameraInterval camera by
            rw [← inter_eq_left]
            exact cameraInterval_minimalSlopeCamera_inter camera) hmin
        simp only [Set.indicator_of_mem hmin, Set.indicator_of_mem hlarge,
          real_inner_smul_left, real_inner_smul_right]
        ring
      · simp [Set.indicator_of_notMem hmin]
    _ = inner Real (kolmogorovVector minimalSlopeCamera)
          (kolmogorovVector camera) *
        (cameraSlope (cameraLabel minimalSlopeCamera) : Real) := by
      rw [MeasureTheory.integral_const_mul,
        integral_indicator_minimalSlopeCamera_centered_mul_coordinate]
    _ = inner Real (naimarkCameraVector minimalSlopeCamera)
        (naimarkCameraVector camera) := by
      rw [inner_naimarkCameraVector, inner_kolmogorovVector]
      simp only [gramKernel]
      rw [Nat.min_eq_left (minimalSlopeCamera_slope_le camera)]
      ring

def naimarkCoreDomainLinearMap :
    CameraFinsupp →ₗ[Real] logarithmicMultiplication.domain where
  toFun u := ⟨naimarkCoreMap u,
    naimarkCoreMap_mem_logarithmicMultiplicationDomain u⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add naimarkCoreMap u v
  map_smul' r u := by
    apply Subtype.ext
    exact map_smul naimarkCoreMap r u

def logarithmicNaimarkCoreLinearMap : CameraFinsupp →ₗ[Real] NaimarkSpace :=
  logarithmicMultiplication.toFun.comp naimarkCoreDomainLinearMap

@[simp] theorem logarithmicNaimarkCoreLinearMap_single
    (camera : CameraIndex) (coefficient : Real) :
    logarithmicNaimarkCoreLinearMap (Finsupp.single camera coefficient) =
      coefficient • logarithmicMultiplication
        ⟨naimarkCameraVector camera,
          naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩ := by
  change logarithmicMultiplication
      (naimarkCoreDomainLinearMap (Finsupp.single camera coefficient)) = _
  rw [show naimarkCoreDomainLinearMap (Finsupp.single camera coefficient) =
      coefficient •
        (⟨naimarkCameraVector camera,
          naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩ :
            logarithmicMultiplication.domain) by
    apply Subtype.ext
    exact naimarkCoreMap_single camera coefficient]
  exact LinearPMap.map_smul _ _ _

theorem inner_centeredMinimalSlopeCamera_naimarkCoreMap (u : CameraFinsupp) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
      (naimarkCoreMap u) = 0 := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | @single_add camera coefficient u hcoefficient hcamera ih =>
      rw [map_add, inner_add_right, ih]
      rw [naimarkCoreMap_single]
      rw [real_inner_smul_right,
        inner_centeredMinimalSlopeCamera_naimarkCameraVector]
      ring

theorem inner_centeredMinimalSlopeCamera_logarithmicNaimarkCoreMap
    (u : CameraFinsupp) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (logarithmicNaimarkCoreLinearMap u) =
      inner Real (naimarkCameraVector minimalSlopeCamera)
        (naimarkCoreMap u) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | @single_add camera coefficient u hcoefficient hcamera ih =>
      rw [map_add, map_add, inner_add_right, inner_add_right, ih]
      rw [logarithmicNaimarkCoreLinearMap_single, naimarkCoreMap_single]
      rw [real_inner_smul_right, real_inner_smul_right,
        inner_centeredMinimalSlopeCamera_logarithmicCameraVector]

theorem inner_centeredMinimalSlopeCamera_naimarkIsometry
    (x : CameraHilbert) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
      (naimarkIsometry x) = 0 := by
  refine cameraEmbedding_denseRange.induction_on
    (p := fun y =>
      inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (naimarkIsometry y) = 0) x ?_ ?_
  · exact isClosed_eq
      (continuous_const.inner
        (naimarkIsometry.continuous)) continuous_const
  · intro u
    rw [naimarkIsometry_cameraEmbedding]
    exact inner_centeredMinimalSlopeCamera_naimarkCoreMap u

theorem inner_centeredMinimalSlopeCamera_realifiedNaimarkPort_snd
    (x : RealifiedCameraComplexification) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
      (realifiedNaimarkPort x).snd = 0 := by
  rw [realifiedNaimarkPort_snd]
  exact inner_centeredMinimalSlopeCamera_naimarkIsometry x.snd

theorem finiteC3SymplecticNaimarkDomainVector_snd
    (M : Nat) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    ((finiteC3SymplecticNaimarkDomainVector M x).snd : NaimarkSpace) =
      naimarkCoreMap (finiteC3LegCameraCore M x.2) :=
  rfl

theorem realifiedLogarithmicMultiplication_finiteC3SymplecticNaimarkDomainVector_snd
    (M : Nat) (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier M) :
    (realifiedLogarithmicMultiplication
      (finiteC3SymplecticNaimarkDomainVector M x)).snd =
        logarithmicNaimarkCoreLinearMap
          (finiteC3LegCameraCore M x.2) := by
  rw [realifiedLogarithmicMultiplication_snd]
  rfl

theorem inner_centeredMinimalSlopeCamera_finiteNaimarkLeak_snd
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z).snd =
      -inner Real (naimarkCameraVector minimalSlopeCamera)
        (naimarkCoreMap
          (finiteC3LegCameraCore
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
            (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
              (operatorHeightParameter z)).2)) := by
  let M := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  let x := canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
    (operatorHeightParameter z)
  have hembed :
      realifiedLogarithmicDomainEmbedding
          (finiteC3SymplecticNaimarkDomainVector M x) =
        realifiedNaimarkPort (finiteC3SymplecticCameraPacking M x) := by
    exact finiteC3SymplecticNaimarkDomainVector_embedding M x
  unfold canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
    canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
    realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe, WithLp.sub_snd, inner_sub_right,
    realifiedNaimarkScalar_snd]
  rw [show canonicalCompletedC3CausalResponseBoundaryDomainVector
      hbase cutoff (operatorHeightParameter z) =
        finiteC3SymplecticNaimarkDomainVector M x by rfl]
  rw [hembed]
  rw [realifiedNaimarkPort_fst, realifiedNaimarkPort_snd]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_centeredMinimalSlopeCamera_naimarkIsometry,
    inner_centeredMinimalSlopeCamera_naimarkIsometry]
  simp only [mul_zero, zero_add, zero_sub]
  have hcompressed :
      inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
        (realifiedNaimarkPort
          (realifiedNaimarkAdjoint
            (canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
              hbase cutoff z))).snd = 0 :=
    inner_centeredMinimalSlopeCamera_realifiedNaimarkPort_snd _
  rw [hcompressed, sub_zero]
  rw [realifiedLogarithmicMultiplication_finiteC3SymplecticNaimarkDomainVector_snd]
  rw [inner_centeredMinimalSlopeCamera_logarithmicNaimarkCoreMap]

/-- The realified Naimark port and adjoint retain the ambient/intrinsic
pairing exactly, coordinate by coordinate. -/
theorem inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint
    (u : RealifiedCameraComplexification)
    (x : RealifiedNaimarkComplexification) :
    inner Real (realifiedNaimarkPort u) x =
      inner Real u (realifiedNaimarkAdjoint x) := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    inner Real (realifiedNaimarkPort u).fst x.fst +
        inner Real (realifiedNaimarkPort u).snd x.snd =
      inner Real u.fst (realifiedNaimarkAdjoint x).fst +
        inner Real u.snd (realifiedNaimarkAdjoint x).snd
  rw [realifiedNaimarkPort_fst, realifiedNaimarkPort_snd,
    realifiedNaimarkAdjoint_fst, realifiedNaimarkAdjoint_snd]
  rw [show naimarkAdjoint =
      naimarkIsometry.toContinuousLinearMap.adjoint by rfl]
  rw [naimarkIsometry.toContinuousLinearMap.adjoint_inner_right,
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The compressed source is orthogonal to the complementary Naimark channel.
This is the exact finite analogue of the active/residual split in the seeded
TFVD Bessel ledger. -/
theorem canonicalCompletedC3CausalResponseBoundaryFinite_port_orthogonal_leak
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    inner Real
      (realifiedNaimarkPort
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z))
      (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
        hbase cutoff z) = 0 := by
  rw [inner_realifiedNaimarkPort_eq_inner_realifiedNaimarkAdjoint,
    realifiedNaimarkAdjoint_canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak]
  simp

/-- Exact finite energy conservation for the induced source: active camera
energy and complementary Naimark energy are separate nonnegative channels. -/
theorem canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_norm_sq
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    ‖canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource
        hbase cutoff z‖ ^ 2 =
      ‖realifiedNaimarkPort
        (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)‖ ^ 2 +
      ‖canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
        hbase cutoff z‖ ^ 2 := by
  rw [canonicalCompletedC3CausalResponseBoundaryFiniteInducedSource_eq_port_add_leak,
    norm_add_sq_real,
    canonicalCompletedC3CausalResponseBoundaryFinite_port_orthogonal_leak]
  ring

theorem noLeak_imp_inner_minimalSlopeCamera_completedState_snd_eq_zero
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re)
    (hnoLeak : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z)
      Filter.atTop (nhds 0)) :
    inner Real (naimarkCameraVector minimalSlopeCamera)
      (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hs).snd = 0 := by
  have hleakSnd : Filter.Tendsto
      (fun cutoff : Nat =>
        (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff z).snd)
      Filter.atTop (nhds 0) := by
    have h :=
      (WithLp.continuous_snd (p := 2)
        (α := NaimarkSpace) (β := NaimarkSpace)).continuousAt.tendsto.comp
          hnoLeak
    exact h.congr'
      (Filter.Eventually.of_forall fun cutoff => rfl)
  have hleakRead : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
          (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
            hbase cutoff z).snd)
      Filter.atTop (nhds 0) := by
    have hcontinuous : Continuous
        (fun y : NaimarkSpace =>
          inner Real (centeredNaimarkCameraVector minimalSlopeCamera) y) :=
      continuous_const.inner continuous_id
    have h := (hcontinuous.tendsto (0 : NaimarkSpace)).comp hleakSnd
    have h' : Filter.Tendsto
        (fun cutoff : Nat =>
          inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
            (canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
              hbase cutoff z).snd)
        Filter.atTop
        (nhds (inner Real (centeredNaimarkCameraVector minimalSlopeCamera)
          (0 : NaimarkSpace))) :=
      h.congr' (Filter.Eventually.of_forall fun cutoff => rfl)
    simpa using h'
  have hnegativeRead : Filter.Tendsto
      (fun cutoff : Nat =>
        -inner Real (naimarkCameraVector minimalSlopeCamera)
          (naimarkCoreMap
            (finiteC3LegCameraCore
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
              (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
                (operatorHeightParameter z)).2)))
      Filter.atTop (nhds 0) :=
    hleakRead.congr'
      (Filter.Eventually.of_forall fun cutoff =>
        inner_centeredMinimalSlopeCamera_finiteNaimarkLeak_snd
          hbase cutoff z)
  have hembedding :=
    canonicalCompletedC3CausalResponseBoundaryDomainVector_embedding_tendsto
      hbase hs
  have hsnd : Filter.Tendsto
      (fun cutoff : Nat =>
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3CausalResponseBoundaryDomainVector hbase cutoff
            (operatorHeightParameter z))).snd)
      Filter.atTop
      (nhds (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hs).snd) :=
    (WithLp.continuous_snd (p := 2)
      (α := NaimarkSpace) (β := NaimarkSpace)).continuousAt.tendsto.comp
        hembedding
  have hcore : Filter.Tendsto
      (fun cutoff : Nat =>
        naimarkCoreMap
          (finiteC3LegCameraCore
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
            (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
              (operatorHeightParameter z)).2))
      Filter.atTop
      (nhds (completedC3SymplecticNaimarkState
        (operatorHeightParameter z) hs).snd) := by
    exact hsnd.congr'
      (Filter.Eventually.of_forall fun cutoff => rfl)
  have hcoreRead : Filter.Tendsto
      (fun cutoff : Nat =>
        inner Real (naimarkCameraVector minimalSlopeCamera)
          (naimarkCoreMap
            (finiteC3LegCameraCore
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
              (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
                (operatorHeightParameter z)).2)))
      Filter.atTop
      (nhds (inner Real (naimarkCameraVector minimalSlopeCamera)
        (completedC3SymplecticNaimarkState
          (operatorHeightParameter z) hs).snd)) := by
    have hcontinuous : Continuous
        (fun y : NaimarkSpace =>
          inner Real (naimarkCameraVector minimalSlopeCamera) y) :=
      continuous_const.inner continuous_id
    exact (hcontinuous.tendsto _).comp hcore
  have hnegativeTarget := hcoreRead.neg
  have hzero :
      -inner Real (naimarkCameraVector minimalSlopeCamera)
          (completedC3SymplecticNaimarkState
            (operatorHeightParameter z) hs).snd = 0 :=
    tendsto_nhds_unique hnegativeTarget hnegativeRead
  linarith

theorem completedC3RawCameraVector_zero_inner_one :
    inner Real (completedC3RawCameraVector 0)
      (completedC3RawCameraVector 1) = 0 := by
  rw [completedC3RawCameraVector, completedC3RawCameraVector,
    inner_cameraVector]
  norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
    periodicProductSum, pairPeriod, completedC3RealCameraIndex,
    cameraLabel, cameraSlope, profile, c2Profile, oddProfile, evenProfile,
    dvdIndicator, Finset.sum_range_succ]

theorem completedC3RawCameraVector_one_inner_one :
    inner Real (completedC3RawCameraVector 1)
      (completedC3RawCameraVector 1) = 6 := by
  simp only [completedC3RawCameraVector, inner_cameraVector]
  norm_num [gramKernel, periodicMeanKernel, periodicProductMean,
    periodicProductSum, pairPeriod, completedC3RealCameraIndex,
    cameraLabel, cameraSlope, profile, c2Profile, oddProfile, evenProfile,
    dvdIndicator, Finset.sum_range_succ]

theorem completedC3RawCameraVector_one_norm :
    ‖completedC3RawCameraVector 1‖ = Real.sqrt 6 := by
  rw [norm_eq_sqrt_real_inner,
    completedC3RawCameraVector_one_inner_one]

theorem completedC3RawCameraVector_gramSchmidt_one :
    InnerProductSpace.gramSchmidt Real completedC3RawCameraVector 1 =
      completedC3RawCameraVector 1 := by
  rw [InnerProductSpace.gramSchmidt_def]
  rw [show Finset.Iio (1 : Nat) = {0} by
    ext n
    simp only [Finset.mem_Iio, Finset.mem_singleton]
    omega]
  simp only [Finset.sum_singleton]
  have hzero :
      InnerProductSpace.gramSchmidt Real completedC3RawCameraVector 0 =
        completedC3RawCameraVector 0 := by
    exact InnerProductSpace.gramSchmidt_bot Real completedC3RawCameraVector
  rw [hzero]
  rw [Submodule.starProjection_apply]
  have horth : completedC3RawCameraVector 1 ∈
      (Real ∙ completedC3RawCameraVector 0)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact completedC3RawCameraVector_zero_inner_one
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal horth]
  simp

theorem completedC3OrthonormalCameraVector_one :
    completedC3OrthonormalCameraVector 1 =
      (Real.sqrt 6)⁻¹ • completedC3RawCameraVector 1 := by
  rw [completedC3OrthonormalCameraVector,
    InnerProductSpace.gramSchmidtNormed,
    completedC3RawCameraVector_gramSchmidt_one,
    completedC3RawCameraVector_one_norm]
  norm_cast

theorem inner_completedC3OrthonormalCameraVector_one_globalLeg
    (x : CarryVerticalL2) :
    inner Real (completedC3OrthonormalCameraVector 1)
        (completedC3GlobalLegCameraIsometry x) = (x 0).im := by
  have hbasis :
      completedC3GlobalCameraCoordinateSynthesis
          (lp.single 2 (0, (1 : Fin 2)) (1 : Real)) =
        completedC3OrthonormalCameraVector 1 := by
    change
      completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry
          (lp.single 2 (0, (1 : Fin 2)) (1 : Real)) = _
    rw [completedC3GlobalCameraCoordinateOrthogonalFamily.linearIsometry_apply_single]
    simp [completedC3GlobalRealCoordinateNat]
  rw [← hbasis]
  change inner Real
      (completedC3GlobalCameraCoordinateSynthesis
        (lp.single 2 (0, (1 : Fin 2)) (1 : Real)))
      (completedC3GlobalCameraCoordinateSynthesis
        (completedC3RealifiedL2CoordinateState x)) = _
  rw [completedC3GlobalCameraCoordinateSynthesis.inner_map_map]
  rw [lp.inner_single_left]
  simp [completedC3RealifiedL2CoordinateState]

theorem inner_minimalSlopeCamera_completedC3GlobalLegCameraIsometry
    (x : CarryVerticalL2) :
    inner Real (cameraVector minimalSlopeCamera)
        (completedC3GlobalLegCameraIsometry x) =
      Real.sqrt 6 * (x 0).im := by
  have hsqrt : Real.sqrt 6 ≠ 0 := by positivity
  have hraw :
      cameraVector minimalSlopeCamera =
        Real.sqrt 6 • completedC3OrthonormalCameraVector 1 := by
    rw [completedC3OrthonormalCameraVector_one]
    change completedC3RawCameraVector 1 = _
    rw [smul_smul]
    field_simp
    simp
  rw [hraw, real_inner_smul_left,
    inner_completedC3OrthonormalCameraVector_one_globalLeg]

theorem inner_minimalSlopeCamera_completedC3SymplecticNaimarkState_snd
    (s : Complex) (hs : 0 < s.re) :
    inner Real (naimarkCameraVector minimalSlopeCamera)
        (completedC3SymplecticNaimarkState s hs).snd =
      Real.sqrt 6 * (positiveDirichletGradient s 0).im := by
  rw [completedC3SymplecticNaimarkState, realifiedNaimarkPort_snd,
    ← naimarkIsometry_cameraVector, naimarkIsometry_inner]
  change inner Real (cameraVector minimalSlopeCamera)
      (completedC3GlobalLegCameraIsometry
        (canonicalCompletedC3DirichletGradientState s hs)) = _
  rw [inner_minimalSlopeCamera_completedC3GlobalLegCameraIsometry,
    canonicalCompletedC3DirichletGradientState_apply]

def noLeakWitnessHeight : Complex :=
  1 - Complex.I / 4

theorem noLeakWitnessHeight_im : noLeakWitnessHeight.im = -(1 / 4 : Real) := by
  simp [noLeakWitnessHeight]

theorem operatorHeightParameter_noLeakWitnessHeight_re :
    (operatorHeightParameter noLeakWitnessHeight).re = 3 / 4 := by
  simp [operatorHeightParameter, noLeakWitnessHeight]
  norm_num

theorem positiveDirichletGradient_noLeakWitnessHeight_im_ne_zero :
    (positiveDirichletGradient
      (operatorHeightParameter noLeakWitnessHeight) 0).im ≠ 0 := by
  rw [positiveDirichletGradient]
  rw [natDirichletTerm_operatorHeightParameter_eq_logOrbit
      (m := 2) (by norm_num) noLeakWitnessHeight,
    natDirichletTerm_operatorHeightParameter_eq_logOrbit
      (m := 1) (by norm_num) noLeakWitnessHeight]
  have hampTwo :
      nativeCriticalDirichletAmplitude 2 =
        ((Real.rpow 2 (-(1 / 2 : Real))) : Complex) := by
    unfold nativeCriticalDirichletAmplitude natDirichletTerm dirichletTerm
    change (2 : Complex) ^ (-(1 / 2 : Complex)) =
      ((Real.rpow 2 (-(1 / 2 : Real))) : Complex)
    convert (Complex.ofReal_cpow (by norm_num : (0 : Real) <= 2)
      (-(1 / 2 : Real))).symm using 1 <;> norm_num
  have hampOne : nativeCriticalDirichletAmplitude 1 = 1 := by
    norm_num [nativeCriticalDirichletAmplitude, natDirichletTerm,
      dirichletTerm]
  have hexponent :
      (-Complex.I * (Real.log (2 : Real) : Complex)) * noLeakWitnessHeight =
        ((-Real.log 2 / 4 : Real) : Complex) +
          ((-Real.log 2 : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp [noLeakWitnessHeight] <;> ring
  rw [hampTwo, hampOne]
  norm_num only [Nat.cast_ofNat]
  rw [hexponent, Complex.exp_add]
  simp only [Complex.exp_ofReal_mul_I]
  norm_num
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLtPi : Real.log 2 < Real.pi := by
    have hlogLtOne : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos
        (x := (2 : Real)) (by norm_num) (by norm_num)
      nlinarith
    nlinarith [Real.pi_gt_three]
  have hsinPos : 0 < Real.sin (Real.log 2) :=
    Real.sin_pos_of_pos_of_lt_pi hlogPos hlogLtPi
  have hrpowPos : 0 < (2 : Real) ^ (-(1 / 2 : Real)) := by positivity
  have hexpPos : 0 < Real.exp (-Real.log 2 / 4) := Real.exp_pos _
  have hlogC : Complex.log (2 : Complex) = (Real.log 2 : Complex) :=
    (Complex.ofReal_log (by norm_num : (0 : Real) <= 2)).symm
  rw [hlogC]
  have hExp :
      Complex.exp (-((Real.log 2 : Real) : Complex) / 4) =
        (Real.exp (-Real.log 2 / 4) : Complex) := by
    rw [show -((Real.log 2 : Real) : Complex) / 4 =
        ((-Real.log 2 / 4 : Real) : Complex) by push_cast; ring]
    exact (Complex.ofReal_exp _).symm
  rw [hExp]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, zero_mul, add_zero,
    zero_add]
  exact mul_ne_zero hexpPos.ne' (neg_ne_zero.mpr hsinPos.ne')

theorem canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak_not_tendsto_zero
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    ¬Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteNaimarkLeak
          hbase cutoff noLeakWitnessHeight)
      Filter.atTop (nhds 0) := by
  intro hnoLeak
  have hs : 0 < (operatorHeightParameter noLeakWitnessHeight).re := by
    rw [operatorHeightParameter_noLeakWitnessHeight_re]
    norm_num
  have hzero :=
    noLeak_imp_inner_minimalSlopeCamera_completedState_snd_eq_zero
      hbase noLeakWitnessHeight hs hnoLeak
  rw [inner_minimalSlopeCamera_completedC3SymplecticNaimarkState_snd]
    at hzero
  exact positiveDirichletGradient_noLeakWitnessHeight_im_ne_zero
    (mul_eq_zero.mp hzero |>.resolve_left (by positivity))

end

end CarrySelfAdjointOperator
