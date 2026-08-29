import CarrySelfAdjointOperator.CompletedC3CompressedSourceLimit

/-!
# Tail control for the intrinsic compressed C3 source

This module proves the graph-tail estimate needed to promote the intrinsic
compressed source form to its strong Hilbert-space limit.  The proof stays on
the native all-camera carrier.  A finite Gram--Schmidt coordinate of order
`n` uses only literal cameras of slope bounded by `n + 4`; logarithmic
multiplication on that finite step space therefore has logarithmic growth.
The already-proved Dirichlet-gradient estimate then makes the series of
compressed logarithmic images absolutely summable.
-/

open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace LinearPMap lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter MeasureTheory Set
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Pointwise Kolmogorov value of a finite all-camera coefficient vector on
the common initial interval of all native cameras. -/
def naimarkCameraCoreInitialValue (u : CameraFinsupp) : KolmogorovSpace :=
  u.sum fun camera coefficient => coefficient • kolmogorovVector camera

/-- Pointwise step-function representative of the finite Naimark core. -/
def naimarkCameraCoreFunction (u : CameraFinsupp) (x : Real) : KolmogorovSpace :=
  u.sum fun camera coefficient =>
    coefficient • (cameraInterval camera).indicator
      (fun _ => kolmogorovVector camera) x

theorem naimarkCoreMap_coeFn (u : CameraFinsupp) :
    ⇑(naimarkCoreMap u) =ᵐ[positiveLebesgueMeasure]
      naimarkCameraCoreFunction u := by
  classical
  induction u using Finsupp.induction with
  | zero =>
      filter_upwards [Lp.coeFn_zero KolmogorovSpace 2
        positiveLebesgueMeasure] with x hx
      simpa [naimarkCameraCoreFunction] using hx
  | @single_add camera coefficient u hcoefficient hcamera ih =>
      rw [map_add]
      filter_upwards [Lp.coeFn_add (naimarkCoreMap (Finsupp.single camera coefficient))
          (naimarkCoreMap u),
        Lp.coeFn_smul coefficient (naimarkCameraVector camera),
        naimarkCameraVector_coeFn camera, ih] with x hadd hsmul
        hcameraFn hu
      rw [hadd, Pi.add_apply, naimarkCoreMap_single, hsmul, Pi.smul_apply,
        hcameraFn, hu]
      unfold naimarkCameraCoreFunction
      rw [Finsupp.sum_add_index'] <;> simp [add_smul]

/-- Every supported native camera contains the common initial interval
`(0, 1]`. -/
theorem Ioc_zero_one_subset_cameraInterval (camera : CameraIndex) :
    Ioc (0 : Real) 1 ⊆ cameraInterval camera := by
  intro x hx
  rw [cameraInterval]
  exact ⟨hx.1, hx.2.trans (by
    exact_mod_cast (cameraSlope_pos camera))⟩

/-- On the common initial interval the finite Naimark core is one constant
Kolmogorov vector. -/
theorem naimarkCameraCoreFunction_eq_initialValue
    (u : CameraFinsupp) {x : Real} (hx : x ∈ Ioc (0 : Real) 1) :
    naimarkCameraCoreFunction u x = naimarkCameraCoreInitialValue u := by
  classical
  unfold naimarkCameraCoreFunction naimarkCameraCoreInitialValue
  apply Finsupp.sum_congr
  intro camera hcamera
  rw [Set.indicator_of_mem (Ioc_zero_one_subset_cameraInterval camera hx)]

/-- A finite core with slopes bounded by `B` vanishes beyond `B`. -/
theorem naimarkCameraCoreFunction_eq_zero_of_slopeBound
    {u : CameraFinsupp} {B : Nat}
    (hB : ∀ camera ∈ u.support,
      cameraSlope (cameraLabel camera) ≤ B)
    {x : Real} (hx : (B : Real) < x) :
    naimarkCameraCoreFunction u x = 0 := by
  classical
  unfold naimarkCameraCoreFunction
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro camera hcamera
  have hnot : x ∉ cameraInterval camera := by
    intro hinterval
    have hxle : x ≤ (cameraSlope (cameraLabel camera) : Real) := hinterval.2
    have hslope : (cameraSlope (cameraLabel camera) : Real) ≤ B := by
      exact_mod_cast hB camera hcamera
    linarith
  simp [hnot]

/-- The common initial interval has finite measure under the positive
half-line measure. -/
theorem positiveLebesgueMeasure_Ioc_zero_one_ne_top :
    positiveLebesgueMeasure (Ioc (0 : Real) 1) ≠ ⊤ := by
  apply ne_of_lt
  exact (measure_mono (Ioc_zero_one_subset_cameraInterval
    minimalSlopeCamera)).trans_lt
      (lt_top_iff_ne_top.mpr
        (positiveLebesgueMeasure_cameraInterval_ne_top minimalSlopeCamera))

/-- Restriction of a finite Naimark core to the interval common to every
native camera. -/
def naimarkCameraCoreLowPart (u : CameraFinsupp) : NaimarkSpace :=
  indicatorConstLp 2 measurableSet_Ioc
    positiveLebesgueMeasure_Ioc_zero_one_ne_top
    (naimarkCameraCoreInitialValue u)

theorem naimarkCameraCoreLowPart_coeFn (u : CameraFinsupp) :
    ⇑(naimarkCameraCoreLowPart u) =ᵐ[positiveLebesgueMeasure]
      (Ioc (0 : Real) 1).indicator (naimarkCameraCoreFunction u) := by
  filter_upwards [(indicatorConstLp_coeFn
      (p := (2 : ℝ≥0∞))
      (hs := measurableSet_Ioc)
      (hμs := positiveLebesgueMeasure_Ioc_zero_one_ne_top)
      (c := naimarkCameraCoreInitialValue u))] with x hlow
  unfold naimarkCameraCoreLowPart
  rw [hlow]
  by_cases hx : x ∈ Ioc (0 : Real) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      naimarkCameraCoreFunction_eq_initialValue u hx]
  · simp [hx]

/-- The complementary high part is literally restriction to the complement
of the common initial interval. -/
theorem naimarkCameraCore_sub_lowPart_coeFn (u : CameraFinsupp) :
    ⇑(naimarkCoreMap u - naimarkCameraCoreLowPart u) =ᵐ[
      positiveLebesgueMeasure]
      (Ioc (0 : Real) 1)ᶜ.indicator (naimarkCameraCoreFunction u) := by
  filter_upwards [Lp.coeFn_sub (naimarkCoreMap u)
      (naimarkCameraCoreLowPart u),
    naimarkCoreMap_coeFn u,
    naimarkCameraCoreLowPart_coeFn u] with x hsub hcore hlow
  rw [hsub, Pi.sub_apply, hcore, hlow]
  by_cases hx : x ∈ Ioc (0 : Real) 1 <;> simp [hx]

/-- Restriction to the common initial interval cannot increase the `L²`
norm. -/
theorem norm_naimarkCameraCoreLowPart_le (u : CameraFinsupp) :
    ‖naimarkCameraCoreLowPart u‖ ≤ ‖naimarkCoreMap u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono
  · exact (Lp.memLp (naimarkCoreMap u)).eLpNorm_ne_top
  · rw [eLpNorm_congr_ae (naimarkCameraCoreLowPart_coeFn u),
      eLpNorm_congr_ae (naimarkCoreMap_coeFn u)]
    exact eLpNorm_indicator_le _

/-- Restriction to the complementary interval cannot increase the `L²`
norm. -/
theorem norm_naimarkCameraCore_sub_lowPart_le (u : CameraFinsupp) :
    ‖naimarkCoreMap u - naimarkCameraCoreLowPart u‖ ≤
      ‖naimarkCoreMap u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono
  · exact (Lp.memLp (naimarkCoreMap u)).eLpNorm_ne_top
  · rw [eLpNorm_congr_ae (naimarkCameraCore_sub_lowPart_coeFn u),
      eLpNorm_congr_ae (naimarkCoreMap_coeFn u)]
    exact eLpNorm_indicator_le _

/-! ## A bounded high logarithmic multiplier -/

/-- Above the common initial interval, logarithmic multiplication on a core
of maximal slope `B` is the bounded multiplier obtained by cutting the
logarithmic coordinate to `(1, B]`. -/
def finiteCameraHighLogCoefficient (B : Nat) (x : Real) : Real :=
  (Ioc (1 : Real) B).indicator logarithmicCoordinate x

theorem measurable_finiteCameraHighLogCoefficient (B : Nat) :
    Measurable (finiteCameraHighLogCoefficient B) := by
  exact measurable_logarithmicCoordinate.indicator measurableSet_Ioc

/-- The high logarithmic coefficient is bounded by `1 + log B`. -/
def finiteCameraHighLogMultiplier (B : Nat) (hB : 1 ≤ B) :
    BoundedRealNaimarkMultiplier where
  coefficient := finiteCameraHighLogCoefficient B
  bound := 1 + Real.log B
  measurable_coefficient := measurable_finiteCameraHighLogCoefficient B
  bound_nonneg := by
    have hlog : 0 ≤ Real.log (B : Real) := by
      exact Real.log_nonneg (by exact_mod_cast hB)
    linarith
  abs_coefficient_le := by
    intro x
    by_cases hx : x ∈ Ioc (1 : Real) B
    · rw [finiteCameraHighLogCoefficient, Set.indicator_of_mem hx]
      have hxpos : 0 < x := zero_lt_one.trans hx.1
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.1.le
      have hlogle : Real.log x ≤ Real.log (B : Real) := by
        exact Real.log_le_log hxpos hx.2
      rw [abs_of_nonneg]
      · dsimp [logarithmicCoordinate]
        linarith
      · dsimp [logarithmicCoordinate]
        linarith
    · rw [finiteCameraHighLogCoefficient, Set.indicator_of_notMem hx,
        abs_zero]
      have hlog : 0 ≤ Real.log (B : Real) := by
        exact Real.log_nonneg (by exact_mod_cast hB)
      linarith

/-! ## Exact control on the common initial interval -/

/-- The scalar logarithmic coordinate restricted to `(0,1]` is square
integrable. -/
theorem memLp_Ioc_zero_one_logarithmicCoordinate :
    MemLp ((Ioc (0 : Real) 1).indicator logarithmicCoordinate) 2
      positiveLebesgueMeasure := by
  have hmeas : AEStronglyMeasurable
      ((Ioc (0 : Real) 1).indicator logarithmicCoordinate)
      positiveLebesgueMeasure :=
    (measurable_logarithmicCoordinate.indicator
      measurableSet_Ioc).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hint : IntegrableOn (fun x : Real => logarithmicCoordinate x ^ 2)
      (Ioc (0 : Real) 1) volume := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : Real) ≤ 1)).mp
        (by simpa [logarithmicCoordinate] using
          (NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLogSq_zero
            (by norm_num : (0 : Real) < 1)))
  have hvolume : Integrable
      ((Ioc (0 : Real) 1).indicator
        (fun x : Real => logarithmicCoordinate x ^ 2)) volume :=
    hint.integrable_indicator measurableSet_Ioc
  have hpositive : Integrable
      ((Ioc (0 : Real) 1).indicator
        (fun x : Real => logarithmicCoordinate x ^ 2))
      positiveLebesgueMeasure := by
    rw [positiveLebesgueMeasure]
    exact hvolume.mono_measure Measure.restrict_le_self
  apply hpositive.congr
  filter_upwards with x
  by_cases hx : x ∈ Ioc (0 : Real) 1
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Fixed scalar `L²` vector carrying the logarithmic coordinate on the
common initial interval. -/
def commonInitialLogarithmicLp : Lp Real 2 positiveLebesgueMeasure :=
  memLp_Ioc_zero_one_logarithmicCoordinate.toLp
    ((Ioc (0 : Real) 1).indicator logarithmicCoordinate)

theorem commonInitialLogarithmicLp_coeFn :
    ⇑commonInitialLogarithmicLp =ᵐ[positiveLebesgueMeasure]
      (Ioc (0 : Real) 1).indicator logarithmicCoordinate :=
  memLp_Ioc_zero_one_logarithmicCoordinate.coeFn_toLp

/-- The low restriction of every finite core belongs to the maximal
logarithmic domain. -/
theorem naimarkCameraCoreLowPart_mem_logarithmicMultiplicationDomain
    (u : CameraFinsupp) :
    naimarkCameraCoreLowPart u ∈ logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain,
    mem_logarithmicMultiplicationDomain_iff]
  have hcomposed : MemLp
      ((ContinuousLinearMap.toSpanSingleton Real
        (naimarkCameraCoreInitialValue u)) ∘
        (Ioc (0 : Real) 1).indicator logarithmicCoordinate)
      2 positiveLebesgueMeasure :=
    (ContinuousLinearMap.toSpanSingleton Real
      (naimarkCameraCoreInitialValue u)).comp_memLp'
        memLp_Ioc_zero_one_logarithmicCoordinate
  apply hcomposed.ae_eq
  filter_upwards [naimarkCameraCoreLowPart_coeFn u] with x hlow
  rw [Function.comp_apply, logarithmicWeightedFunction, hlow]
  by_cases hx : x ∈ Ioc (0 : Real) 1
  · simp [Set.indicator_of_mem hx,
      ContinuousLinearMap.toSpanSingleton_apply,
      naimarkCameraCoreFunction_eq_initialValue u hx]
  · simp [Set.indicator_of_notMem hx,
      ContinuousLinearMap.toSpanSingleton_apply]

/-- Low restriction bundled with its exact maximal-domain witness. -/
def naimarkCameraCoreLowDomainVector (u : CameraFinsupp) :
    logarithmicMultiplication.domain :=
  ⟨naimarkCameraCoreLowPart u,
    naimarkCameraCoreLowPart_mem_logarithmicMultiplicationDomain u⟩

/-- The logarithmic image of the low restriction is a rank-one `L²`
vector built from the fixed scalar initial logarithm. -/
theorem logarithmicMultiplication_lowDomainVector_eq_compLp
    (u : CameraFinsupp) :
    logarithmicMultiplication (naimarkCameraCoreLowDomainVector u) =
      (ContinuousLinearMap.toSpanSingleton Real
        (naimarkCameraCoreInitialValue u)).compLp
          commonInitialLogarithmicLp := by
  apply Lp.ext
  filter_upwards [logarithmicMultiplication_coeFn
      (naimarkCameraCoreLowDomainVector u),
    naimarkCameraCoreLowPart_coeFn u,
    (ContinuousLinearMap.toSpanSingleton Real
      (naimarkCameraCoreInitialValue u)).coeFn_compLp
        commonInitialLogarithmicLp,
    commonInitialLogarithmicLp_coeFn] with x hmul hlow hcomp hscalar
  rw [hmul, logarithmicWeightedFunction, hcomp, hscalar]
  change logarithmicCoordinate x • (naimarkCameraCoreLowPart u) x = _
  rw [hlow]
  by_cases hx : x ∈ Ioc (0 : Real) 1
  · simp [Set.indicator_of_mem hx,
      ContinuousLinearMap.toSpanSingleton_apply,
      naimarkCameraCoreFunction_eq_initialValue u hx]
  · simp [Set.indicator_of_notMem hx,
      ContinuousLinearMap.toSpanSingleton_apply]

theorem positiveLebesgueMeasure_real_Ioc_zero_one :
    positiveLebesgueMeasure.real (Ioc (0 : Real) 1) = 1 := by
  rw [positiveLebesgueMeasure, measureReal_restrict_apply measurableSet_Ioc]
  rw [inter_eq_left.mpr]
  · simp
  · intro x hx
    exact hx.1

/-- On the common interval of measure one, the low-part norm is exactly the
norm of its constant Kolmogorov value. -/
theorem norm_naimarkCameraCoreLowPart (u : CameraFinsupp) :
    ‖naimarkCameraCoreLowPart u‖ =
      ‖naimarkCameraCoreInitialValue u‖ := by
  rw [naimarkCameraCoreLowPart,
    norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    positiveLebesgueMeasure_real_Ioc_zero_one]
  norm_num

/-- The singular endpoint contributes one fixed finite constant and no
cutoff-dependent growth. -/
theorem norm_logarithmicMultiplication_lowDomainVector_le
    (u : CameraFinsupp) :
    ‖logarithmicMultiplication (naimarkCameraCoreLowDomainVector u)‖ ≤
      ‖commonInitialLogarithmicLp‖ * ‖naimarkCoreMap u‖ := by
  rw [logarithmicMultiplication_lowDomainVector_eq_compLp]
  calc
    _ ≤ ‖ContinuousLinearMap.toSpanSingleton Real
          (naimarkCameraCoreInitialValue u)‖ *
        ‖commonInitialLogarithmicLp‖ :=
      (ContinuousLinearMap.toSpanSingleton Real
        (naimarkCameraCoreInitialValue u)).norm_compLp_le _
    _ = ‖commonInitialLogarithmicLp‖ *
        ‖naimarkCameraCoreLowPart u‖ := by
      rw [ContinuousLinearMap.norm_toSpanSingleton,
        norm_naimarkCameraCoreLowPart]
      ring
    _ ≤ ‖commonInitialLogarithmicLp‖ * ‖naimarkCoreMap u‖ :=
      mul_le_mul_of_nonneg_left (norm_naimarkCameraCoreLowPart_le u)
        (norm_nonneg _)

/-! ## Finite-slope graph estimate -/

/-- Exact low/high decomposition of logarithmic multiplication on a finite
camera core.  No endpoint estimate is hidden in this identity. -/
theorem logarithmicNaimarkCoreLinearMap_eq_low_add_high
    {u : CameraFinsupp} {B : Nat} (hB : 1 ≤ B)
    (hsupport : ∀ camera ∈ u.support,
      cameraSlope (cameraLabel camera) ≤ B) :
    logarithmicNaimarkCoreLinearMap u =
      logarithmicMultiplication (naimarkCameraCoreLowDomainVector u) +
        boundedRealNaimarkMultiplier (finiteCameraHighLogMultiplier B hB)
          (naimarkCoreMap u - naimarkCameraCoreLowPart u) := by
  change logarithmicMultiplication (naimarkCoreDomainLinearMap u) = _
  apply Lp.ext
  have hpositive : ∀ᵐ x : Real ∂positiveLebesgueMeasure, x ∈ Ioi 0 := by
    rw [positiveLebesgueMeasure]
    exact ae_restrict_mem measurableSet_Ioi
  filter_upwards [hpositive,
    logarithmicMultiplication_coeFn (naimarkCoreDomainLinearMap u),
    naimarkCoreMap_coeFn u,
    logarithmicMultiplication_coeFn (naimarkCameraCoreLowDomainVector u),
    naimarkCameraCoreLowPart_coeFn u,
    boundedRealNaimarkMultiplier_coeFn
      (finiteCameraHighLogMultiplier B hB)
      (naimarkCoreMap u - naimarkCameraCoreLowPart u),
    naimarkCameraCore_sub_lowPart_coeFn u,
    Lp.coeFn_add
      (logarithmicMultiplication (naimarkCameraCoreLowDomainVector u))
      (boundedRealNaimarkMultiplier (finiteCameraHighLogMultiplier B hB)
        (naimarkCoreMap u - naimarkCameraCoreLowPart u))] with
      x hxpos hlhs hcore hlowMul hlow hhighMul hhigh hadd
  rw [hlhs]
  change logarithmicCoordinate x • (naimarkCoreMap u) x = _
  rw [hcore, hadd, Pi.add_apply, hlowMul]
  change logarithmicCoordinate x • naimarkCameraCoreFunction u x =
    logarithmicCoordinate x • (naimarkCameraCoreLowPart u) x + _
  rw [hlow, hhighMul, boundedRealNaimarkMultiplierFunction, hhigh]
  by_cases hxone : x ≤ 1
  · have hxlow : x ∈ Ioc (0 : Real) 1 := ⟨hxpos, hxone⟩
    have hxnotComplement : x ∉ (Ioc (0 : Real) 1)ᶜ := by
      simp [hxlow]
    rw [Set.indicator_of_mem hxlow,
      naimarkCameraCoreFunction_eq_initialValue u hxlow,
      Set.indicator_of_notMem hxnotComplement, smul_zero, add_zero]
  · have hxgt : 1 < x := lt_of_not_ge hxone
    have hxnotLow : x ∉ Ioc (0 : Real) 1 := by
      intro hx
      linarith [hx.2]
    have hxComplement : x ∈ (Ioc (0 : Real) 1)ᶜ := by
      simp [hxnotLow]
    by_cases hxB : x ≤ B
    · have hxhigh : x ∈ Ioc (1 : Real) B := ⟨hxgt, hxB⟩
      rw [Set.indicator_of_notMem hxnotLow, smul_zero, zero_add,
        Set.indicator_of_mem hxComplement]
      change logarithmicCoordinate x • naimarkCameraCoreFunction u x =
        finiteCameraHighLogCoefficient B x • naimarkCameraCoreFunction u x
      rw [finiteCameraHighLogCoefficient, Set.indicator_of_mem hxhigh]
    · have hxBeyond : (B : Real) < x := lt_of_not_ge hxB
      have hxhigh : x ∉ Ioc (1 : Real) B := by
        intro hx
        linarith [hx.2]
      have hzero :=
        naimarkCameraCoreFunction_eq_zero_of_slopeBound hsupport hxBeyond
      rw [Set.indicator_of_notMem hxnotLow, smul_zero, zero_add,
        Set.indicator_of_mem hxComplement, hzero, smul_zero]
      simp

/-- Quantitative graph norm on a finite camera core.  Its only
cutoff-dependent term is logarithmic in the maximal camera slope. -/
theorem norm_logarithmicNaimarkCoreLinearMap_le
    {u : CameraFinsupp} {B : Nat} (hB : 1 ≤ B)
    (hsupport : ∀ camera ∈ u.support,
      cameraSlope (cameraLabel camera) ≤ B) :
    ‖logarithmicNaimarkCoreLinearMap u‖ ≤
      (‖commonInitialLogarithmicLp‖ + (1 + Real.log B)) *
        ‖naimarkCoreMap u‖ := by
  rw [logarithmicNaimarkCoreLinearMap_eq_low_add_high hB hsupport]
  calc
    _ ≤ ‖logarithmicMultiplication
          (naimarkCameraCoreLowDomainVector u)‖ +
        ‖boundedRealNaimarkMultiplier (finiteCameraHighLogMultiplier B hB)
          (naimarkCoreMap u - naimarkCameraCoreLowPart u)‖ := norm_add_le _ _
    _ ≤ ‖commonInitialLogarithmicLp‖ * ‖naimarkCoreMap u‖ +
        (1 + Real.log B) *
          ‖naimarkCoreMap u - naimarkCameraCoreLowPart u‖ := by
      exact add_le_add
        (norm_logarithmicMultiplication_lowDomainVector_le u)
        (by
          change
            ‖boundedRealNaimarkMultiplierLinearMap
              (finiteCameraHighLogMultiplier B hB)
              (naimarkCoreMap u - naimarkCameraCoreLowPart u)‖ ≤ _
          exact boundedRealNaimarkMultiplierLinearMap_norm_le
            (finiteCameraHighLogMultiplier B hB)
            (naimarkCoreMap u - naimarkCameraCoreLowPart u))
    _ ≤ ‖commonInitialLogarithmicLp‖ * ‖naimarkCoreMap u‖ +
        (1 + Real.log B) * ‖naimarkCoreMap u‖ := by
      have hlog : 0 ≤ Real.log (B : Real) :=
        Real.log_nonneg (by exact_mod_cast hB)
      have hcoefficient : 0 ≤ 1 + Real.log (B : Real) := by
        linarith
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (norm_naimarkCameraCore_sub_lowPart_le u) hcoefficient)
    _ = (‖commonInitialLogarithmicLp‖ + (1 + Real.log B)) *
        ‖naimarkCoreMap u‖ := by ring

/-! ## Finite support inherited by the permanent Gram--Schmidt family -/

/-- The literal camera reserved for coordinate `n` has slope at most
`n + 4`; the extra two units cover the exceptional aligned camera `2`. -/
theorem cameraSlope_completedC3RealCameraIndex_le (n : Nat) :
    cameraSlope (cameraLabel (completedC3RealCameraIndex n)) ≤ n + 4 := by
  simp only [completedC3RealCameraIndex, cameraLabel]
  unfold cameraSlope
  split <;> omega

/-- Every vector in the span of the first `n+1` raw cameras admits a finite
camera representative supported at slopes at most `n+4`. -/
theorem exists_cameraCore_with_slopeBound_of_mem_rawSpan
    {n : Nat} {x : CameraHilbert}
    (hx : x ∈ Submodule.span Real
      (completedC3RawCameraVector '' Set.Iic n)) :
    ∃ u : CameraFinsupp,
      cameraEmbedding u = x ∧
        ∀ camera ∈ u.support,
          cameraSlope (cameraLabel camera) ≤ n + 4 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩
      refine ⟨Finsupp.single (completedC3RealCameraIndex i) 1, ?_, ?_⟩
      · simp [completedC3RawCameraVector, cameraVector]
      · intro camera hcamera
        have heq : camera = completedC3RealCameraIndex i := by
          simpa using hcamera
        subst camera
        have hin : i ≤ n := hi
        exact (cameraSlope_completedC3RealCameraIndex_le i).trans
          (Nat.add_le_add_right hin 4)
  | zero =>
      refine ⟨0, by simp, ?_⟩
      simp
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨u, hu, huBound⟩
      rcases ihy with ⟨v, hv, hvBound⟩
      refine ⟨u + v, ?_, ?_⟩
      · rw [map_add, hu, hv]
      · intro camera hcamera
        have hne : u camera + v camera ≠ 0 := by
          simpa [Finsupp.mem_support_iff] using hcamera
        by_cases hucamera : u camera = 0
        · apply hvBound camera
          simpa [Finsupp.mem_support_iff, hucamera] using hne
        · apply huBound camera
          simpa [Finsupp.mem_support_iff] using hucamera
  | smul r x hx ih =>
      rcases ih with ⟨u, hu, huBound⟩
      refine ⟨r • u, ?_, ?_⟩
      · rw [map_smul, hu]
      · intro camera hcamera
        exact huBound camera (Finsupp.support_smul hcamera)

/-- A slope-bounded finite representative of the permanent orthonormal
coordinate exists before any choice of core is made. -/
theorem exists_completedC3OrthonormalCameraCore_with_slopeBound (n : Nat) :
    ∃ u : CameraFinsupp,
      cameraEmbedding u = completedC3OrthonormalCameraVector n ∧
        ∀ camera ∈ u.support,
          cameraSlope (cameraLabel camera) ≤ n + 4 := by
  apply exists_cameraCore_with_slopeBound_of_mem_rawSpan
  unfold completedC3OrthonormalCameraVector
  apply Submodule.smul_mem
  exact InnerProductSpace.gramSchmidt_mem_span
    Real completedC3RawCameraVector (le_refl n)

/-- The already chosen canonical core inherits the same slope bound by
injectivity of the camera embedding. -/
theorem completedC3OrthonormalCameraCore_slopeBound (n : Nat) :
    ∀ camera ∈ (completedC3OrthonormalCameraCore n).support,
      cameraSlope (cameraLabel camera) ≤ n + 4 := by
  rcases exists_completedC3OrthonormalCameraCore_with_slopeBound n with
    ⟨u, hu, huBound⟩
  have hcore : completedC3OrthonormalCameraCore n = u := by
    apply cameraEmbedding.injective
    rw [cameraEmbedding_completedC3OrthonormalCameraCore, hu]
  simpa [hcore] using huBound

theorem norm_naimarkCoreMap_completedC3OrthonormalCameraCore (n : Nat) :
    ‖naimarkCoreMap (completedC3OrthonormalCameraCore n)‖ = 1 := by
  change ‖naimarkCoreIsometry (completedC3OrthonormalCameraCore n)‖ = 1
  rw [← naimarkIsometry_cameraEmbedding,
    cameraEmbedding_completedC3OrthonormalCameraCore,
    naimarkIsometry.norm_map]
  exact completedC3OrthonormalCameraVector_orthonormal.norm_eq_one n

/-- The ambient logarithmic image of the `n`-th permanent coordinate grows
at most logarithmically. -/
theorem norm_logarithmicNaimarkCore_completedC3OrthonormalCameraCore_le
    (n : Nat) :
    ‖logarithmicNaimarkCoreLinearMap
        (completedC3OrthonormalCameraCore n)‖ ≤
      ‖commonInitialLogarithmicLp‖ + (1 + Real.log (n + 4)) := by
  have hbound := norm_logarithmicNaimarkCoreLinearMap_le
    (u := completedC3OrthonormalCameraCore n)
    (B := n + 4) (by omega)
    (completedC3OrthonormalCameraCore_slopeBound n)
  rw [norm_naimarkCoreMap_completedC3OrthonormalCameraCore, mul_one] at hbound
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hbound

/-! ## Compressed coordinate images -/

/-- Image of one permanent camera coordinate under the intrinsic compressed
logarithmic operator. -/
def completedC3CompressedLogarithmicCoordinateImage (n : Nat) : CameraHilbert :=
  naimarkAdjoint
    (logarithmicNaimarkCoreLinearMap
      (completedC3OrthonormalCameraCore n))

/-- Compression cannot enlarge the logarithmic graph bound of a permanent
coordinate. -/
theorem norm_completedC3CompressedLogarithmicCoordinateImage_le (n : Nat) :
    ‖completedC3CompressedLogarithmicCoordinateImage n‖ ≤
      ‖commonInitialLogarithmicLp‖ + (1 + Real.log (n + 4)) := by
  calc
    _ ≤ ‖naimarkAdjoint‖ *
        ‖logarithmicNaimarkCoreLinearMap
          (completedC3OrthonormalCameraCore n)‖ :=
      naimarkAdjoint.le_opNorm _
    _ ≤ 1 * ‖logarithmicNaimarkCoreLinearMap
          (completedC3OrthonormalCameraCore n)‖ := by
      exact mul_le_mul_of_nonneg_right naimarkAdjoint_norm_le_one
        (norm_nonneg _)
    _ ≤ ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (n + 4)) := by
      simpa using
        norm_logarithmicNaimarkCore_completedC3OrthonormalCameraCore_le n

/-- Logarithmic compression of a finite C3 leg is the exact finite synthesis
of the permanent compressed coordinate images. -/
theorem naimarkAdjoint_logarithmicNaimarkCore_finiteC3LegCameraCore
    (M : Nat)
    (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    naimarkAdjoint
        (logarithmicNaimarkCoreLinearMap (finiteC3LegCameraCore M x)) =
      ∑ j : FiniteC3RealCoordinate M,
        ![(x j.1).re, (x j.1).im] j.2 •
          completedC3CompressedLogarithmicCoordinateImage
            (finiteC3RealCoordinateNat j) := by
  unfold finiteC3LegCameraCore finiteC3CameraCoreCoordinateState
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul]
  rfl

/-- One complex Dirichlet-gradient coordinate, with both real quadratures
kept as separate compressed camera vectors. -/
def completedC3CompressedLogarithmicLegTerm (s : Complex) (n : Nat) :
    CameraHilbert :=
  (positiveDirichletGradient s n).re •
      completedC3CompressedLogarithmicCoordinateImage (2 * n) +
    (positiveDirichletGradient s n).im •
      completedC3CompressedLogarithmicCoordinateImage (2 * n + 1)

/-- Exact finite prefix of the intrinsic compressed logarithmic leg. -/
def completedC3CompressedLogarithmicLegPrefix (s : Complex) (N : Nat) :
    CameraHilbert :=
  ∑ n ∈ Finset.range N, completedC3CompressedLogarithmicLegTerm s n

theorem naimarkAdjoint_logarithmicNaimarkCore_genuineSecondLeg_eq_prefix
    (N : Nat) (s : Complex) :
    naimarkAdjoint
        (logarithmicNaimarkCoreLinearMap
          (finiteC3LegCameraCore N
            (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
              N s).2)) =
      completedC3CompressedLogarithmicLegPrefix s N := by
  rw [naimarkAdjoint_logarithmicNaimarkCore_finiteC3LegCameraCore]
  rw [Fintype.sum_prod_type]
  unfold completedC3CompressedLogarithmicLegPrefix
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < N := Finset.mem_range.mp hn
  simp only [hnlt, dif_pos]
  rw [Fin.sum_univ_two]
  simp only [finiteC3RealCoordinateNat]
  simp [completedC3CompressedLogarithmicLegTerm,
    NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_snd_apply]

/-- At coefficient level, the first genuine leg is exactly the real radial
multiple of the second leg. -/
theorem finiteC3LegCameraCore_genuineFirst_eq_radial_smul_second
    (N : Nat) (s : Complex) :
    finiteC3LegCameraCore N
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
          N s).1 =
      completedC3RadialRealCoefficient s •
        finiteC3LegCameraCore N
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
            N s).2 := by
  apply cameraEmbedding.injective
  rw [cameraEmbedding_finiteC3LegCameraCore, map_smul,
    cameraEmbedding_finiteC3LegCameraCore,
    finiteC3GenuineFirstLegCamera_eq_radial_completedPrefix,
    finiteC3GenuineSecondLegCamera_eq_completedPrefix]

/-- The second component of the actual finite compressed logarithmic image
is exactly the intrinsic leg prefix. -/
theorem canonicalCompletedC3FiniteCompressedLogarithmicImage_snd_eq_prefix
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    (realifiedCompressedLogarithmicMultiplication
      (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
        hbase cutoff z)).snd =
      completedC3CompressedLogarithmicLegPrefix
        (operatorHeightParameter z)
        (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1) := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  rw [realifiedCompressedLogarithmicMultiplication_apply,
    realifiedNaimarkAdjoint_snd, realifiedLogarithmicMultiplication_snd,
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_lift]
  change
    naimarkAdjoint
      (logarithmicNaimarkCoreLinearMap
        (finiteC3LegCameraCore N
          (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
            (operatorHeightParameter z)).2)) = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine]
  exact
    naimarkAdjoint_logarithmicNaimarkCore_genuineSecondLeg_eq_prefix
      N (operatorHeightParameter z)

/-- The first component carries the same intrinsic logarithmic prefix with
the exact symplectic minus sign and radial coefficient. -/
theorem canonicalCompletedC3FiniteCompressedLogarithmicImage_fst_eq_prefix
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff : Nat) (z : Complex) :
    (realifiedCompressedLogarithmicMultiplication
      (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
        hbase cutoff z)).fst =
      -(completedC3RadialRealCoefficient (operatorHeightParameter z) •
        completedC3CompressedLogarithmicLegPrefix
          (operatorHeightParameter z)
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) := by
  let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
  rw [realifiedCompressedLogarithmicMultiplication_apply,
    realifiedNaimarkAdjoint_fst, realifiedLogarithmicMultiplication_fst,
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector_lift]
  change
    naimarkAdjoint
      (logarithmicNaimarkCoreLinearMap
        (-finiteC3LegCameraCore N
          (canonicalCompletedC3CausalResponseBoundaryTfvdPort hbase cutoff
            (operatorHeightParameter z)).1)) = _
  rw [canonicalCompletedC3CausalResponseBoundaryTfvdPort_eq_genuine,
    finiteC3LegCameraCore_genuineFirst_eq_radial_smul_second,
    map_neg, map_smul, map_neg, map_smul,
    naimarkAdjoint_logarithmicNaimarkCore_genuineSecondLeg_eq_prefix]

/-! ## Absolute summability of the intrinsic logarithmic leg -/

/-- Common scalar majorant for the two quadratures of coordinate `n`. -/
def completedC3CompressedLogarithmicCoordinateWeight (n : Nat) : Real :=
  ‖commonInitialLogarithmicLp‖ +
    (1 + Real.log (2 * n + 5))

theorem completedC3CompressedLogarithmicCoordinateWeight_nonneg (n : Nat) :
    0 ≤ completedC3CompressedLogarithmicCoordinateWeight n := by
  have hlog : 0 ≤ Real.log ((2 * n + 5 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * n + 5 by omega)
  have hlog' : 0 ≤ Real.log (2 * (n : Real) + 5) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hlog
  unfold completedC3CompressedLogarithmicCoordinateWeight
  exact add_nonneg (norm_nonneg _) (add_nonneg zero_le_one hlog')

theorem norm_completedC3CompressedLogarithmicCoordinateImage_even_le
    (n : Nat) :
    ‖completedC3CompressedLogarithmicCoordinateImage (2 * n)‖ ≤
      completedC3CompressedLogarithmicCoordinateWeight n := by
  calc
    _ ≤ ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (2 * n + 4)) :=
      (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        norm_completedC3CompressedLogarithmicCoordinateImage_le (2 * n))
    _ ≤ ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (2 * n + 5)) := by
      have hlog : Real.log (2 * (n : Real) + 4) ≤
          Real.log (2 * (n : Real) + 5) := by
        apply Real.log_le_log
        · positivity
        · norm_num
      exact add_le_add (le_refl _) (add_le_add (le_refl _) hlog)
    _ = completedC3CompressedLogarithmicCoordinateWeight n := rfl

theorem norm_completedC3CompressedLogarithmicCoordinateImage_odd_le
    (n : Nat) :
    ‖completedC3CompressedLogarithmicCoordinateImage (2 * n + 1)‖ ≤
      completedC3CompressedLogarithmicCoordinateWeight n := by
  have h :=
    norm_completedC3CompressedLogarithmicCoordinateImage_le (2 * n + 1)
  unfold completedC3CompressedLogarithmicCoordinateWeight
  convert h using 1
  all_goals push_cast
  all_goals ring_nf

/-- Each two-quadrature term is controlled by the gradient norm times one
logarithmic scalar weight. -/
theorem norm_completedC3CompressedLogarithmicLegTerm_le
    (s : Complex) (n : Nat) :
    ‖completedC3CompressedLogarithmicLegTerm s n‖ ≤
      2 * completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ := by
  unfold completedC3CompressedLogarithmicLegTerm
  calc
    _ ≤
        ‖(positiveDirichletGradient s n).re •
          completedC3CompressedLogarithmicCoordinateImage (2 * n)‖ +
        ‖(positiveDirichletGradient s n).im •
          completedC3CompressedLogarithmicCoordinateImage (2 * n + 1)‖ :=
      norm_add_le _ _
    _ = |(positiveDirichletGradient s n).re| *
          ‖completedC3CompressedLogarithmicCoordinateImage (2 * n)‖ +
        |(positiveDirichletGradient s n).im| *
          ‖completedC3CompressedLogarithmicCoordinateImage (2 * n + 1)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖positiveDirichletGradient s n‖ *
          completedC3CompressedLogarithmicCoordinateWeight n +
        ‖positiveDirichletGradient s n‖ *
          completedC3CompressedLogarithmicCoordinateWeight n := by
      exact add_le_add
        (mul_le_mul (Complex.abs_re_le_norm _)
          (norm_completedC3CompressedLogarithmicCoordinateImage_even_le n)
          (norm_nonneg _)
          (norm_nonneg _))
        (mul_le_mul (Complex.abs_im_le_norm _)
          (norm_completedC3CompressedLogarithmicCoordinateImage_odd_le n)
          (norm_nonneg _)
          (norm_nonneg _))
    _ = 2 * completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ := by ring

/-- A polynomial majorant for the logarithmic coordinate weight. -/
theorem completedC3CompressedLogarithmicCoordinateWeight_le_rpow
    {s : Complex} (hs : 0 < s.re) (n : Nat) :
    completedC3CompressedLogarithmicCoordinateWeight n ≤
      (‖commonInitialLogarithmicLp‖ + 1 +
          (5 : Real) ^ (s.re / 2) / (s.re / 2)) *
        (((n + 1 : Nat) : Real) ^ (s.re / 2)) := by
  let epsilon : Real := s.re / 2
  let x : Real := ((n + 1 : Nat) : Real)
  let y : Real := ((2 * n + 5 : Nat) : Real)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hyfive : y ≤ 5 * x := by
    dsimp [x, y]
    push_cast
    have hnnonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
    nlinarith
  have hlog : Real.log y ≤ y ^ epsilon / epsilon :=
    Real.log_le_rpow_div hypos.le hepsilon
  have hyrpow : y ^ epsilon ≤ (5 * x) ^ epsilon :=
    Real.rpow_le_rpow hypos.le hyfive hepsilon.le
  have hmulrpow : (5 * x) ^ epsilon =
      (5 : Real) ^ epsilon * x ^ epsilon := by
    rw [Real.mul_rpow (by norm_num) hxpos.le]
  have hlog' : Real.log y ≤
      ((5 : Real) ^ epsilon / epsilon) * x ^ epsilon := by
    calc
      Real.log y ≤ y ^ epsilon / epsilon := hlog
      _ ≤ (5 * x) ^ epsilon / epsilon := by
        exact div_le_div_of_nonneg_right hyrpow hepsilon.le
      _ = ((5 : Real) ^ epsilon / epsilon) * x ^ epsilon := by
        rw [hmulrpow]
        field_simp
  have hxpow : 1 ≤ x ^ epsilon :=
    Real.one_le_rpow hxone hepsilon.le
  have hconstantNonneg : 0 ≤ ‖commonInitialLogarithmicLp‖ + 1 := by
    positivity
  have hconstant : ‖commonInitialLogarithmicLp‖ + 1 ≤
      (‖commonInitialLogarithmicLp‖ + 1) * x ^ epsilon := by
    nlinarith
  have hlog'' : Real.log (2 * (n : Real) + 5) ≤
      ((5 : Real) ^ epsilon / epsilon) * x ^ epsilon := by
    simpa only [y, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hlog'
  change ‖commonInitialLogarithmicLp‖ +
      (1 + Real.log (2 * (n : Real) + 5)) ≤ _
  calc
    ‖commonInitialLogarithmicLp‖ +
        (1 + Real.log (2 * (n : Real) + 5)) =
        ‖commonInitialLogarithmicLp‖ + 1 +
          Real.log (2 * (n : Real) + 5) := by ring
    _ ≤
        (‖commonInitialLogarithmicLp‖ + 1) * x ^ epsilon +
          ((5 : Real) ^ epsilon / epsilon) * x ^ epsilon :=
      add_le_add hconstant hlog''
    _ = (‖commonInitialLogarithmicLp‖ + 1 +
          (5 : Real) ^ epsilon / epsilon) * x ^ epsilon := by ring
    _ = (‖commonInitialLogarithmicLp‖ + 1 +
          (5 : Real) ^ (s.re / 2) / (s.re / 2)) *
        (((n + 1 : Nat) : Real) ^ (s.re / 2)) := by
      rfl

/-- The logarithmic coordinate weight times the native gradient has a
summable power majorant throughout the open right half-plane. -/
theorem completedC3CompressedLogarithmicCoordinateWeight_mul_gradient_le
    {s : Complex} (hs : 0 < s.re) (n : Nat) :
    completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ ≤
      ((‖commonInitialLogarithmicLp‖ + 1 +
          (5 : Real) ^ (s.re / 2) / (s.re / 2)) * ‖s‖) *
        (((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1)) := by
  let x : Real := ((n + 1 : Nat) : Real)
  let K : Real := ‖commonInitialLogarithmicLp‖ + 1 +
    (5 : Real) ^ (s.re / 2) / (s.re / 2)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hepsilon : 0 < s.re / 2 := by linarith
    positivity
  have hweight : completedC3CompressedLogarithmicCoordinateWeight n ≤
      K * x ^ (s.re / 2) := by
    simpa only [K, x] using
      completedC3CompressedLogarithmicCoordinateWeight_le_rpow hs n
  have hgradient : ‖positiveDirichletGradient s n‖ ≤
      ‖s‖ * x ^ (-s.re - 1) := by
    simpa only [x] using norm_positiveDirichletGradient_le hs n
  calc
    completedC3CompressedLogarithmicCoordinateWeight n *
        ‖positiveDirichletGradient s n‖ ≤
      (K * x ^ (s.re / 2)) * (‖s‖ * x ^ (-s.re - 1)) := by
        exact mul_le_mul hweight hgradient (norm_nonneg _)
          (mul_nonneg hK (Real.rpow_nonneg hxpos.le _))
    _ = (K * ‖s‖) * x ^ (-s.re / 2 - 1) := by
      rw [show -s.re / 2 - 1 = s.re / 2 + (-s.re - 1) by ring,
        Real.rpow_add hxpos]
      ring
    _ = ((‖commonInitialLogarithmicLp‖ + 1 +
          (5 : Real) ^ (s.re / 2) / (s.re / 2)) * ‖s‖) *
        (((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1)) := by
      rfl

/-- The full two-quadrature compressed logarithmic leg is absolutely
summable. -/
theorem summable_completedC3CompressedLogarithmicLegTerm
    {s : Complex} (hs : 0 < s.re) :
    Summable (completedC3CompressedLogarithmicLegTerm s) := by
  have hbase : Summable
      (fun n : Nat => (n : Real) ^ (-s.re / 2 - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable
      (fun n : Nat => ((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1)) := by
    have h := hbase.comp_injective
      (show Function.Injective (fun n : Nat => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    change Summable
      (fun n : Nat => ((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1)) at h
    exact h
  let C : Real := 2 *
    ((‖commonInitialLogarithmicLp‖ + 1 +
      (5 : Real) ^ (s.re / 2) / (s.re / 2)) * ‖s‖)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hepsilon : 0 < s.re / 2 := by linarith
    positivity
  have hmajorant := hshift.mul_left C
  exact hmajorant.of_norm_bounded fun n => by
    calc
      ‖completedC3CompressedLogarithmicLegTerm s n‖ ≤
          2 * completedC3CompressedLogarithmicCoordinateWeight n *
            ‖positiveDirichletGradient s n‖ :=
        norm_completedC3CompressedLogarithmicLegTerm_le s n
      _ = 2 *
          (completedC3CompressedLogarithmicCoordinateWeight n *
            ‖positiveDirichletGradient s n‖) := by ring
      _ ≤ 2 *
          (((‖commonInitialLogarithmicLp‖ + 1 +
              (5 : Real) ^ (s.re / 2) / (s.re / 2)) * ‖s‖) *
            (((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1))) := by
        exact mul_le_mul_of_nonneg_left
          (completedC3CompressedLogarithmicCoordinateWeight_mul_gradient_le
            hs n) (by norm_num)
      _ = C * (((n + 1 : Nat) : Real) ^ (-s.re / 2 - 1)) := by
        dsimp [C]
        ring

/-- The intrinsic compressed logarithmic prefixes converge strongly to their
own absolutely convergent Hilbert-space series. -/
theorem completedC3CompressedLogarithmicLegPrefix_tendsto
    {s : Complex} (hs : 0 < s.re) :
    Tendsto (completedC3CompressedLogarithmicLegPrefix s) atTop
      (nhds (∑' n : Nat, completedC3CompressedLogarithmicLegTerm s n)) := by
  exact (summable_completedC3CompressedLogarithmicLegTerm hs).tendsto_sum_tsum_nat

/-! ## Strong graph-tail and source limits -/

/-- Intrinsic Hilbert limit of one compressed logarithmic TFVD leg. -/
def completedC3CompressedLogarithmicLegLimit (s : Complex) : CameraHilbert :=
  ∑' n : Nat, completedC3CompressedLogarithmicLegTerm s n

/-- Intrinsic two-leg compressed logarithmic image, retaining the symplectic
sign and radial coefficient exactly. -/
def completedC3CompressedLogarithmicImageLimit
    (s : Complex) : RealifiedCameraComplexification :=
  WithLp.toLp 2
    (-(completedC3RadialRealCoefficient s •
        completedC3CompressedLogarithmicLegLimit s),
      completedC3CompressedLogarithmicLegLimit s)

/-- The compressed logarithmic images of the actual finite TFVD states
converge strongly to their intrinsic all-camera series. -/
theorem canonicalCompletedC3FiniteCompressedLogarithmicImage_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : Nat =>
        realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z))
      atTop
      (nhds (completedC3CompressedLogarithmicImageLimit
        (operatorHeightParameter z))) := by
  let s := operatorHeightParameter z
  let L := completedC3CompressedLogarithmicLegLimit s
  have hleg : Tendsto
      (fun cutoff : Nat =>
        completedC3CompressedLogarithmicLegPrefix s
          (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1))
      atTop (nhds L) := by
    exact (completedC3CompressedLogarithmicLegPrefix_tendsto hs).comp
      (finiteCameraWindow_add_one_tendsto_atTop hbase)
  have hfirst : Tendsto
      (fun cutoff : Nat =>
        -(completedC3RadialRealCoefficient s •
          completedC3CompressedLogarithmicLegPrefix s
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)))
      atTop
      (nhds (-(completedC3RadialRealCoefficient s • L))) :=
    (hleg.const_smul (completedC3RadialRealCoefficient s)).neg
  have hpair := hfirst.prodMk_nhds hleg
  have hlp : Tendsto
      (fun cutoff : Nat => WithLp.toLp 2
        (-(completedC3RadialRealCoefficient s •
            completedC3CompressedLogarithmicLegPrefix s
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)),
          completedC3CompressedLogarithmicLegPrefix s
            (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)))
      atTop
      (nhds (WithLp.toLp 2
        (-(completedC3RadialRealCoefficient s • L), L))) :=
    (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp hpair
  have heq (cutoff : Nat) :
      realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z) =
        WithLp.toLp 2
          (-(completedC3RadialRealCoefficient s •
              completedC3CompressedLogarithmicLegPrefix s
                (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)),
            completedC3CompressedLogarithmicLegPrefix s
              (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)) := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        (realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z)).fst = _
      simpa only [s, WithLp.toLp_fst] using
        canonicalCompletedC3FiniteCompressedLogarithmicImage_fst_eq_prefix
          hbase cutoff z
    · change
        (realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z)).snd = _
      simpa only [s, WithLp.toLp_snd] using
        canonicalCompletedC3FiniteCompressedLogarithmicImage_snd_eq_prefix
          hbase cutoff z
  unfold completedC3CompressedLogarithmicImageLimit
  change Tendsto _ atTop
    (nhds (WithLp.toLp 2
      (-(completedC3RadialRealCoefficient s • L), L)))
  exact hlp.congr' (Eventually.of_forall fun cutoff => (heq cutoff).symm)

/-- The graph tail of the compressed logarithmic images is Cauchy without
any Green-positivity or spectral hypothesis. -/
theorem canonicalCompletedC3FiniteCompressedLogarithmicImage_cauchy
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    CauchySeq
      (fun cutoff : Nat =>
        realifiedCompressedLogarithmicMultiplication
          (canonicalCompletedC3CausalResponseBoundaryFiniteCompressedDomainVector
            hbase cutoff z)) :=
  (canonicalCompletedC3FiniteCompressedLogarithmicImage_tendsto
    hbase z hs).cauchySeq

/-- Consequently the intrinsic finite compressed sources themselves form a
Cauchy sequence. -/
theorem canonicalCompletedC3FiniteCompressedSource_cauchy
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    CauchySeq
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z) := by
  exact
    (canonicalCompletedC3FiniteCompressedSource_cauchy_iff_logarithmicImage_cauchy
      hbase z hs).mpr
      (canonicalCompletedC3FiniteCompressedLogarithmicImage_cauchy
        hbase z hs)

/-- The tail estimate constructs the canonical Riesz source and proves
strong convergence of the finite compressed sources to it. -/
theorem exists_canonicalCompletedC3CompressedHilbertSource_tendsto
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : Complex) (hs : 0 < (operatorHeightParameter z).re) :
    ∃ hbound : CanonicalCompletedC3CompressedSourceFormBounded z hs,
      Tendsto
        (fun cutoff : Nat =>
          canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
            hbase cutoff z)
        atTop
        (nhds (canonicalCompletedC3CompressedHilbertSource z hs hbound)) :=
  exists_canonicalCompletedC3CompressedHilbertSource_tendsto_of_cauchy
    hbase z hs
    (canonicalCompletedC3FiniteCompressedSource_cauchy hbase z hs)

end

end CarrySelfAdjointOperator
