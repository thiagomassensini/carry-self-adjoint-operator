import CarrySelfAdjointOperator.CompletedC3SymplecticGammaCentralCommonFiberOutcome
import CarrySelfAdjointOperator.CompletedGreenDiagonalClosure
import NativeCarrySpectralWeyl.Infinite.Cauchy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open MeasureTheory
open Set
open NativeCarrySpectralWeyl.Infinite

open scoped ENNReal MeasureTheory RealInnerProductSpace ComplexConjugate

noncomputable section

def canonicalCompletedC3SymplecticCommonFiberFst
    (z : ℂ) : KolmogorovSpace :=
  canonicalC3CommonFiberMap
    ⟨(canonicalCompletedC3SymplecticGammaCameraSource z).fst,
      canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan z⟩

def canonicalCompletedC3SymplecticCommonFiberSnd
    (z : ℂ) : KolmogorovSpace :=
  canonicalC3CommonFiberMap
    ⟨(canonicalCompletedC3SymplecticGammaCameraSource z).snd,
      canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan z⟩

@[simp] theorem canonicalCompletedC3SymplecticCommonFiberFst_zero :
    canonicalCompletedC3SymplecticCommonFiberFst 0 =
      canonicalCompletedC3SymplecticCentralCommonFiberFst := by
  simp [canonicalCompletedC3SymplecticCommonFiberFst,
    canonicalCompletedC3SymplecticCentralCommonFiberFst,
    canonicalCompletedC3SymplecticCentralRawFst]

@[simp] theorem canonicalCompletedC3SymplecticCommonFiberSnd_zero :
    canonicalCompletedC3SymplecticCommonFiberSnd 0 =
      canonicalCompletedC3SymplecticCentralCommonFiberSnd := by
  simp [canonicalCompletedC3SymplecticCommonFiberSnd,
    canonicalCompletedC3SymplecticCentralCommonFiberSnd,
    canonicalCompletedC3SymplecticCentralRawSnd]

noncomputable def canonicalC3CommonFiberContinuousMap :
    canonicalC3RawCameraSpan →L[ℝ] KolmogorovSpace :=
  letI : FiniteDimensional ℝ canonicalC3RawCameraSpan := by
    unfold canonicalC3RawCameraSpan
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  LinearMap.toContinuousLinearMap canonicalC3CommonFiberMap

@[simp] theorem canonicalC3CommonFiberContinuousMap_apply
    (x : canonicalC3RawCameraSpan) :
    canonicalC3CommonFiberContinuousMap x = canonicalC3CommonFiberMap x := by
  simp [canonicalC3CommonFiberContinuousMap,
    LinearMap.coe_toContinuousLinearMap]

private theorem canonicalCompletedC3SymplecticGammaCameraSource_continuousAt_zero :
    ContinuousAt canonicalCompletedC3SymplecticGammaCameraSource 0 := by
  have hstate : ContinuousAt canonicalCompletedOperatorC3State 0 := by
    change ContinuousAt
      (fun z : ℂ =>
        WithLp.ofLp (canonicalCompletedOperatorC3HilbertState z)) 0
    exact (WithLp.prod_continuous_ofLp 2 _ _).continuousAt.comp
      canonicalCompletedOperatorC3HilbertState_continuousAt_zero
  have hpack : Continuous (fun x :
      NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 =>
        (canonicalC3SymplecticCameraPackingLinearMap x :
          CarryGammaComplexCamera)) := by
    exact LinearMap.continuous_of_finiteDimensional _
  change ContinuousAt
    (fun z : ℂ =>
      (canonicalC3SymplecticCameraPackingLinearMap
        (canonicalCompletedOperatorC3State z) : CarryGammaComplexCamera)) 0
  exact hpack.continuousAt.comp hstate

theorem canonicalCompletedC3SymplecticCommonFiberFst_continuousAt_zero :
    ContinuousAt canonicalCompletedC3SymplecticCommonFiberFst 0 := by
  have hsource :=
    canonicalCompletedC3SymplecticGammaCameraSource_continuousAt_zero
  have hsource' : ContinuousAt
      (fun z : ℂ => WithLp.ofLp
        (canonicalCompletedC3SymplecticGammaCameraSource z)) 0 :=
    (WithLp.prod_continuous_ofLp 2 _ _).continuousAt.comp hsource
  have hleg : ContinuousAt
      (fun z : ℂ => (canonicalCompletedC3SymplecticGammaCameraSource z).fst) 0 :=
    hsource'.fst
  have hspan : ContinuousAt
      (fun z : ℂ =>
        (⟨(canonicalCompletedC3SymplecticGammaCameraSource z).fst,
          canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan z⟩ :
            canonicalC3RawCameraSpan)) 0 := by
    exact tendsto_subtype_rng.mpr hleg
  have hcomp :=
    canonicalC3CommonFiberContinuousMap.continuous.continuousAt.comp hspan
  have heq :
      (fun z : ℂ => canonicalCompletedC3SymplecticCommonFiberFst z) =
        (fun z : ℂ => canonicalC3CommonFiberContinuousMap
          ⟨(canonicalCompletedC3SymplecticGammaCameraSource z).fst,
            canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan z⟩) := by
    funext z
    simp [canonicalCompletedC3SymplecticCommonFiberFst]
  change ContinuousAt (fun z : ℂ =>
    canonicalCompletedC3SymplecticCommonFiberFst z) 0
  rw [heq]
  simpa only [Function.comp_def] using hcomp

theorem canonicalCompletedC3SymplecticCommonFiberSnd_continuousAt_zero :
    ContinuousAt canonicalCompletedC3SymplecticCommonFiberSnd 0 := by
  have hsource :=
    canonicalCompletedC3SymplecticGammaCameraSource_continuousAt_zero
  have hsource' : ContinuousAt
      (fun z : ℂ => WithLp.ofLp
        (canonicalCompletedC3SymplecticGammaCameraSource z)) 0 :=
    (WithLp.prod_continuous_ofLp 2 _ _).continuousAt.comp hsource
  have hleg : ContinuousAt
      (fun z : ℂ => (canonicalCompletedC3SymplecticGammaCameraSource z).snd) 0 :=
    hsource'.snd
  have hspan : ContinuousAt
      (fun z : ℂ =>
        (⟨(canonicalCompletedC3SymplecticGammaCameraSource z).snd,
          canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan z⟩ :
            canonicalC3RawCameraSpan)) 0 := by
    exact tendsto_subtype_rng.mpr hleg
  have hcomp :=
    canonicalC3CommonFiberContinuousMap.continuous.continuousAt.comp hspan
  have heq :
      (fun z : ℂ => canonicalCompletedC3SymplecticCommonFiberSnd z) =
        (fun z : ℂ => canonicalC3CommonFiberContinuousMap
          ⟨(canonicalCompletedC3SymplecticGammaCameraSource z).snd,
            canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan z⟩) := by
    funext z
    simp [canonicalCompletedC3SymplecticCommonFiberSnd]
  change ContinuousAt (fun z : ℂ =>
    canonicalCompletedC3SymplecticCommonFiberSnd z) 0
  rw [heq]
  simpa only [Function.comp_def] using hcomp

def canonicalCompletedC3SymplecticCommonFiberEnergy (z : ℂ) : ℝ :=
  ‖canonicalCompletedC3SymplecticCommonFiberFst z‖ ^ 2 +
    ‖canonicalCompletedC3SymplecticCommonFiberSnd z‖ ^ 2

theorem canonicalCompletedC3SymplecticCommonFiberEnergy_continuousAt_zero :
    ContinuousAt canonicalCompletedC3SymplecticCommonFiberEnergy 0 := by
  change ContinuousAt
    (fun z : ℂ =>
      ‖canonicalCompletedC3SymplecticCommonFiberFst z‖ ^ 2 +
        ‖canonicalCompletedC3SymplecticCommonFiberSnd z‖ ^ 2) 0
  exact
    (canonicalCompletedC3SymplecticCommonFiberFst_continuousAt_zero.norm.pow 2).add
      (canonicalCompletedC3SymplecticCommonFiberSnd_continuousAt_zero.norm.pow 2)

theorem canonicalCompletedC3SymplecticCommonFiberEnergy_zero_pos :
    0 < canonicalCompletedC3SymplecticCommonFiberEnergy 0 := by
  change 0 <
    ‖canonicalCompletedC3SymplecticCommonFiberFst 0‖ ^ 2 +
      ‖canonicalCompletedC3SymplecticCommonFiberSnd 0‖ ^ 2
  rw [canonicalCompletedC3SymplecticCommonFiberFst_zero,
    canonicalCompletedC3SymplecticCommonFiberSnd_zero]
  rcases canonicalCompletedC3SymplecticCentralCommonFiber_nontrivial with hfst | hsnd
  · have hpos : 0 <
        ‖canonicalCompletedC3SymplecticCentralCommonFiberFst‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hfst)
    nlinarith [sq_nonneg
      ‖canonicalCompletedC3SymplecticCentralCommonFiberSnd‖]
  · have hpos : 0 <
        ‖canonicalCompletedC3SymplecticCentralCommonFiberSnd‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hsnd)
    nlinarith [sq_nonneg
      ‖canonicalCompletedC3SymplecticCentralCommonFiberFst‖]

theorem canonicalCompletedC3SymplecticCommonFiberEnergy_eventually_ge_half :
    ∀ᶠ z : ℂ in nhds 0,
      canonicalCompletedC3SymplecticCommonFiberEnergy z ≥
        canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2 := by
  have hpos := canonicalCompletedC3SymplecticCommonFiberEnergy_zero_pos
  have hnhds : Set.Ioi
      (canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2) ∈
        nhds (canonicalCompletedC3SymplecticCommonFiberEnergy 0) := by
    apply isOpen_Ioi.mem_nhds
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)
  have hev : ∀ᶠ z : ℂ in nhds 0,
      canonicalCompletedC3SymplecticCommonFiberEnergy z ∈
        Set.Ioi (canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2) :=
    canonicalCompletedC3SymplecticCommonFiberEnergy_continuousAt_zero hnhds
  exact hev.mono (fun z hz => le_of_lt hz)

def canonicalCentralResolventWindow (η : ℝ) : Set ℝ :=
  Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))

theorem canonicalCentralResolventWindow_subset_Ioc_zero_one
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    canonicalCentralResolventWindow η ⊆ Set.Ioc 0 1 := by
  intro x hx
  change x ∈ Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)) at hx
  change x ∈ Set.Ioc 0 1
  constructor
  · exact lt_trans (Real.exp_pos _) hx.1
  · have harg : -1 + η ≤ (0 : ℝ) := by linarith
    have hexp : Real.exp (-1 + η) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr harg
    simpa using hx.2.trans hexp

theorem logarithmicCoordinate_mem_canonicalCentralResolventWindow
    {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : x ∈ canonicalCentralResolventWindow η) :
    0 ≤ logarithmicCoordinate x ∧ logarithmicCoordinate x ≤ η := by
  have hx' := (canonicalCentralResolventWindow_subset_Ioc_zero_one hη hη1) hx
  have hxpos : 0 < x := hx'.1
  change x ∈ Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)) at hx
  have hloglow : -1 < Real.log x := by
    by_contra h
    have hle : Real.log x ≤ -1 := le_of_not_gt h
    have hexp : Real.exp (Real.log x) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr hle
    rw [Real.exp_log hxpos] at hexp
    linarith [hx.1]
  have hloghigh : Real.log x ≤ -1 + η := by
    by_contra h
    have hlt : -1 + η < Real.log x := lt_of_not_ge h
    have hexp : Real.exp (-1 + η) < Real.exp (Real.log x) :=
      Real.exp_lt_exp.mpr hlt
    rw [Real.exp_log hxpos] at hexp
    linarith [hx.2]
  constructor <;> simp [logarithmicCoordinate] <;> linarith

theorem logarithmicResolventDenominator_I_mul_le
    {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : x ∈ canonicalCentralResolventWindow η) :
    logarithmicResolventDenominator
        (Complex.I * (η : ℂ)) x ≤ 2 * η ^ 2 := by
  have hcoord := logarithmicCoordinate_mem_canonicalCentralResolventWindow
    hη hη1 hx
  simp [logarithmicResolventDenominator, logarithmicCoordinate] at *
  nlinarith [sq_nonneg (1 + Real.log x)]

theorem positiveLebesgueMeasure_real_canonicalCentralResolventWindow
    {η : ℝ} (hη : 0 < η) :
    positiveLebesgueMeasure.real (canonicalCentralResolventWindow η) =
      Real.exp (-1 + η) - Real.exp (-1) := by
  unfold canonicalCentralResolventWindow
  rw [positiveLebesgueMeasure,
    measureReal_restrict_apply measurableSet_Ioc]
  rw [inter_eq_left.mpr (by
    intro x hx
    exact lt_trans (Real.exp_pos _) hx.1)]
  have hle : Real.exp (-1) ≤ Real.exp (-1 + η) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.volume_real_Ioc_of_le hle]

theorem positiveLebesgueMeasure_real_canonicalCentralResolventWindow_ge
    {η : ℝ} (hη : 0 < η) :
    Real.exp (-1) * η ≤
      positiveLebesgueMeasure.real (canonicalCentralResolventWindow η) := by
  rw [positiveLebesgueMeasure_real_canonicalCentralResolventWindow hη]
  rw [Real.exp_add]
  have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp η)
    (le_of_lt (Real.exp_pos (-1)))
  nlinarith

theorem canonicalCentralResolventWindow_integral_inv_denominator_ge
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    Real.exp (-1) / (2 * η) ≤
      ∫ x in canonicalCentralResolventWindow η,
        (logarithmicResolventDenominator
          (Complex.I * (η : ℂ)) x)⁻¹ ∂volume := by
  let lam : ℂ := Complex.I * (η : ℂ)
  have hlam : lam.im ≠ 0 := by
    dsimp [lam]
    simpa using hη.ne'
  have hdenpos (x : ℝ) :
      0 < logarithmicResolventDenominator lam x :=
    logarithmicResolventDenominator_pos hlam x
  have hdenlower (x : ℝ) :
      η ^ 2 ≤ logarithmicResolventDenominator lam x := by
    dsimp [lam]
    simp [logarithmicResolventDenominator]
    nlinarith [sq_nonneg (logarithmicCoordinate x)]
  have hdenupper {x : ℝ}
      (hx : x ∈ canonicalCentralResolventWindow η) :
      logarithmicResolventDenominator lam x ≤ 2 * η ^ 2 := by
    dsimp [lam]
    exact logarithmicResolventDenominator_I_mul_le hη hη1 hx
  have hfmeas : Measurable (fun x : ℝ =>
      (logarithmicResolventDenominator lam x)⁻¹) := by
    exact (measurable_logarithmicResolventDenominator lam).inv
  have hfint : IntegrableOn (fun x : ℝ =>
      (logarithmicResolventDenominator lam x)⁻¹)
      (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))) volume := by
    refine Measure.integrableOn_of_bounded
      (μ := (volume : Measure ℝ))
      (s := Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)))
      (f := fun x : ℝ =>
        (logarithmicResolventDenominator lam x)⁻¹)
      (M := (η ^ 2)⁻¹) ?_ ?_ ?_
    · exact (measure_Ioc_lt_top (μ := (volume : Measure ℝ))).ne
    · exact hfmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hupper :
          (logarithmicResolventDenominator lam x)⁻¹ ≤ (η ^ 2)⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le (sq_pos_of_ne_zero hη.ne')
            (hdenlower x)
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hdenpos x))]
      exact hupper
  have hpoint : ∀ x ∈ Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)),
      (2 * η ^ 2)⁻¹ ≤
        (logarithmicResolventDenominator lam x)⁻¹ := by
    intro x hx
    simpa [one_div] using
      one_div_le_one_div_of_le (hdenpos x) (hdenupper hx)
  have hsetint :
      (2 * η ^ 2)⁻¹ *
          volume.real (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))) ≤
        ∫ x in Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)),
          (logarithmicResolventDenominator lam x)⁻¹ ∂volume := by
    exact setIntegral_ge_of_const_le_real measurableSet_Ioc
      measure_Ioc_lt_top.ne hpoint hfint
  have hvolge : Real.exp (-1) * η ≤
      volume.real (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))) := by
    calc
      Real.exp (-1) * η ≤
          positiveLebesgueMeasure.real (canonicalCentralResolventWindow η) :=
        positiveLebesgueMeasure_real_canonicalCentralResolventWindow_ge hη
      _ = volume.real (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))) := by
        unfold canonicalCentralResolventWindow positiveLebesgueMeasure
        rw [measureReal_restrict_apply measurableSet_Ioc]
        rw [inter_eq_left.mpr (by
          intro x hx
          exact lt_trans (Real.exp_pos _) hx.1)]
  have hmul := mul_le_mul_of_nonneg_left hvolge
    (by positivity : 0 ≤ (2 * η ^ 2)⁻¹)
  have hscale : Real.exp (-1) / (2 * η) =
      (2 * η ^ 2)⁻¹ * (Real.exp (-1) * η) := by
    field_simp [hη.ne']
  change Real.exp (-1) / (2 * η) ≤
    ∫ x in Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η)),
      (logarithmicResolventDenominator lam x)⁻¹ ∂volume
  calc
    Real.exp (-1) / (2 * η) =
        (2 * η ^ 2)⁻¹ * (Real.exp (-1) * η) := hscale
    _ ≤ (2 * η ^ 2)⁻¹ *
        volume.real (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))) := hmul
    _ ≤ _ := by simpa [lam] using hsetint

end

end CarrySelfAdjointOperator
