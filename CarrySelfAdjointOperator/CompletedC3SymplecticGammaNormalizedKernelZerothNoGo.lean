import CarrySelfAdjointOperator.CompletedC3SymplecticGammaCentralResolventLowerBound
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaNormalizedKernelZerothAudit
import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import NativeCarrySpectralWeyl.Boundary.GammaField
import NativeCarrySpectralWeyl.Infinite.Cauchy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Zeroth-order no-go audit for the normalized symplectic Gamma carrier

OUTCOME NO-GO

The corrected symplectic Gamma field remains a valid positive
off-axis Green/Naimark dilation, but its raw normalized resolvent Gram
does not have the finite zeroth radial germ required by the canonical
completed moment kernel.

The obstruction is the nonzero common spectral fiber at `Y = 0`,
which forces a `1/Im(z)`-type diagonal growth.

This theorem rejects this Gamma-Gram sewing route only.
It does not reject:
* the symplectic Gamma Green identity;
* the explicit completed ledger;
* the corrected clock/moment-kernel identity;
* other positive carriers;
* boundary/Poisson-renormalized Gamma constructions.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace
  RealInnerProductSpace lp Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open MeasureTheory
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite
open Set

noncomputable section

theorem realifiedResolventRotation_norm_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (r s : ℝ) (a b : E) :
    ‖r • a - s • b‖ ^ 2 +
        ‖s • a + r • b‖ ^ 2
      =
    (r ^ 2 + s ^ 2) *
      (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right]
  simp only [mul_pow, sq_abs]
  ring

theorem
    canonicalCompletedC3SymplecticGammaState_pointwiseEnergy_ae_eq_commonWindow
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᵐ x ∂positiveLebesgueMeasure,
      x ∈ canonicalCentralResolventWindow η →
        ‖(canonicalCompletedC3SymplecticGammaState
            (Complex.I * (η : ℂ)) (by simp [hη.ne'])).fst x‖ ^ 2 +
            ‖(canonicalCompletedC3SymplecticGammaState
              (Complex.I * (η : ℂ)) (by simp [hη.ne'])).snd x‖ ^ 2 =
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ *
            canonicalCompletedC3SymplecticCommonFiberEnergy
              (Complex.I * (η : ℂ)) := by
  let z : ℂ := Complex.I * (η : ℂ)
  have hz : z.im ≠ 0 := by
    simpa [z] using hη.ne'
  have hcommonFst :
      ∀ᵐ x ∂positiveLebesgueMeasure,
        x ∈ canonicalC3CommonNaimarkInterval →
          (naimarkIsometry
            (canonicalCompletedC3SymplecticGammaCameraSource z).fst) x =
            canonicalCompletedC3SymplecticCommonFiberFst z := by
    simpa [canonicalCompletedC3SymplecticCommonFiberFst] using
      (naimarkIsometry_rawSpan_ae_eq_commonFiber
        (⟨(canonicalCompletedC3SymplecticGammaCameraSource z).fst,
          canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan z⟩ :
          canonicalC3RawCameraSpan))
  have hcommonSnd :
      ∀ᵐ x ∂positiveLebesgueMeasure,
        x ∈ canonicalC3CommonNaimarkInterval →
          (naimarkIsometry
            (canonicalCompletedC3SymplecticGammaCameraSource z).snd) x =
            canonicalCompletedC3SymplecticCommonFiberSnd z := by
    simpa [canonicalCompletedC3SymplecticCommonFiberSnd] using
      (naimarkIsometry_rawSpan_ae_eq_commonFiber
        (⟨(canonicalCompletedC3SymplecticGammaCameraSource z).snd,
          canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan z⟩ :
          canonicalC3RawCameraSpan))
  have hreal := logarithmicResolventRealOperator_coeFn z hz
    (naimarkIsometry
      ((canonicalCompletedC3SymplecticGammaCameraSource z :
        WithLp 2 (CameraHilbert × CameraHilbert)).fst))
  have himag := logarithmicResolventImaginaryOperator_coeFn z hz
    (naimarkIsometry
      ((canonicalCompletedC3SymplecticGammaCameraSource z :
        WithLp 2 (CameraHilbert × CameraHilbert)).snd))
  have hrealSnd := logarithmicResolventRealOperator_coeFn z hz
    (naimarkIsometry
      ((canonicalCompletedC3SymplecticGammaCameraSource z :
        WithLp 2 (CameraHilbert × CameraHilbert)).snd))
  have himagFst := logarithmicResolventImaginaryOperator_coeFn z hz
    (naimarkIsometry
      ((canonicalCompletedC3SymplecticGammaCameraSource z :
        WithLp 2 (CameraHilbert × CameraHilbert)).fst))
  have hsub := Lp.coeFn_sub
    (logarithmicResolventRealOperator z hz
      (naimarkIsometry
        ((canonicalCompletedC3SymplecticGammaCameraSource z :
          WithLp 2 (CameraHilbert × CameraHilbert)).fst)))
    (logarithmicResolventImaginaryOperator z hz
      (naimarkIsometry
        ((canonicalCompletedC3SymplecticGammaCameraSource z :
          WithLp 2 (CameraHilbert × CameraHilbert)).snd)))
  have hadd := Lp.coeFn_add
    (logarithmicResolventImaginaryOperator z hz
      (naimarkIsometry
        ((canonicalCompletedC3SymplecticGammaCameraSource z :
          WithLp 2 (CameraHilbert × CameraHilbert)).fst)))
    (logarithmicResolventRealOperator z hz
      (naimarkIsometry
        ((canonicalCompletedC3SymplecticGammaCameraSource z :
          WithLp 2 (CameraHilbert × CameraHilbert)).snd)))
  unfold CarrySelfAdjointOperator.RealHilbertComplexification at hreal himag hrealSnd himagFst
  filter_upwards [hreal, himag, hrealSnd, himagFst, hsub, hadd,
    hcommonFst, hcommonSnd] with x hreal himag hrealSnd himagFst hsub hadd
    hcommonFst hcommonSnd
  intro hx
  have hx01 :=
    (canonicalCentralResolventWindow_subset_Ioc_zero_one hη hη1) hx
  have hxcommon : x ∈ canonicalC3CommonNaimarkInterval := by
    simpa [canonicalC3CommonNaimarkInterval] using
      (show x ∈ Set.Ioc (0 : ℝ) 3 from
        ⟨hx01.1, le_trans hx01.2 (by norm_num)⟩)
  have hfst :
      (canonicalCompletedC3SymplecticGammaState z hz).fst x =
        logarithmicResolventRealCoefficient z x •
            canonicalCompletedC3SymplecticCommonFiberFst z -
          logarithmicResolventImaginaryCoefficient z x •
            canonicalCompletedC3SymplecticCommonFiberSnd z := by
    have hsub' := hsub
    simp only [Pi.sub_apply] at hsub'
    change (carryGammaSource z hz
      (canonicalCompletedC3SymplecticGammaCameraSource z)).fst x = _
    rw [carryGammaSource_fst]
    rw [hsub', hreal, himag,
      hcommonFst hxcommon, hcommonSnd hxcommon]
  have hsnd :
      (canonicalCompletedC3SymplecticGammaState z hz).snd x =
        logarithmicResolventImaginaryCoefficient z x •
            canonicalCompletedC3SymplecticCommonFiberFst z +
          logarithmicResolventRealCoefficient z x •
            canonicalCompletedC3SymplecticCommonFiberSnd z := by
    have hadd' := hadd
    simp only [Pi.add_apply] at hadd'
    change (carryGammaSource z hz
      (canonicalCompletedC3SymplecticGammaCameraSource z)).snd x = _
    rw [carryGammaSource_snd]
    rw [hadd', himagFst, hrealSnd,
      hcommonFst hxcommon, hcommonSnd hxcommon]
  rw [hfst, hsnd, realifiedResolventRotation_norm_sq,
    logarithmicResolventCoefficient_norm_sq hz x]
  rfl

theorem
    canonicalCompletedC3SymplecticGammaState_norm_sq_ge_commonWindow
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    canonicalCompletedC3SymplecticCommonFiberEnergy
        (Complex.I * (η : ℂ)) *
      (∫ x in canonicalCentralResolventWindow η,
        (logarithmicResolventDenominator
          (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) ≤
      ‖canonicalCompletedC3SymplecticGammaState
          (Complex.I * (η : ℂ))
          (by simp [hη.ne'])‖ ^ 2 := by
  let γ : CarryGammaComplexNaimark :=
    canonicalCompletedC3SymplecticGammaState
      (Complex.I * (η : ℂ)) (by simp [hη.ne'])
  let μ : Measure ℝ := positiveLebesgueMeasure
  have hwindow_pos : canonicalCentralResolventWindow η ⊆ Set.Ioi 0 := by
    intro x hx
    exact (canonicalCentralResolventWindow_subset_Ioc_zero_one hη hη1 hx).1
  have hfstint : Integrable (fun x : ℝ => ‖γ.fst x‖ ^ 2) μ := by
    simpa [μ, real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) γ.fst γ.fst)
  have hsndint : Integrable (fun x : ℝ => ‖γ.snd x‖ ^ 2) μ := by
    simpa [μ, real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) γ.snd γ.snd)
  have hfstnorm :
      ‖γ.fst‖ ^ 2 = ∫ x : ℝ, ‖γ.fst x‖ ^ 2 ∂μ := by
    dsimp [μ]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  have hsndnorm :
      ‖γ.snd‖ ^ 2 = ∫ x : ℝ, ‖γ.snd x‖ ^ 2 ∂μ := by
    dsimp [μ]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
  have hfull :
      (∫ x : ℝ, (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ) =
        ‖γ‖ ^ 2 := by
    calc
      (∫ x : ℝ, (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ) =
          (∫ x : ℝ, ‖γ.fst x‖ ^ 2 ∂μ) +
            ∫ x : ℝ, ‖γ.snd x‖ ^ 2 ∂μ :=
        integral_add hfstint hsndint
      _ = ‖γ.fst‖ ^ 2 + ‖γ.snd‖ ^ 2 := by
        rw [hfstnorm, hsndnorm]
      _ = ‖γ‖ ^ 2 :=
        (WithLp.prod_norm_sq_eq_of_L2 γ).symm
  have hsetle :
      (∫ x in canonicalCentralResolventWindow η,
        (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ) ≤
        ∫ x : ℝ, (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ := by
    apply setIntegral_le_integral (hfstint.add hsndint)
    filter_upwards with x
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint :=
    canonicalCompletedC3SymplecticGammaState_pointwiseEnergy_ae_eq_commonWindow
      hη hη1
  have hseteq :
      (∫ x in canonicalCentralResolventWindow η,
        (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ) =
      ∫ x in canonicalCentralResolventWindow η,
        (logarithmicResolventDenominator
          (Complex.I * (η : ℂ)) x)⁻¹ *
          canonicalCompletedC3SymplecticCommonFiberEnergy
            (Complex.I * (η : ℂ)) ∂μ := by
    apply integral_congr_ae
    exact (ae_restrict_iff' measurableSet_Ioc).2 hpoint
  have hmeasure :
      (∫ x in canonicalCentralResolventWindow η,
        (logarithmicResolventDenominator
          (Complex.I * (η : ℂ)) x)⁻¹ ∂μ) =
        ∫ x in canonicalCentralResolventWindow η,
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ ∂volume := by
    unfold canonicalCentralResolventWindow
    change MeasureTheory.integral
        ((volume.restrict (Set.Ioi 0)).restrict
          (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))))
        (fun x : ℝ =>
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹) =
      MeasureTheory.integral
        (volume.restrict (Set.Ioc (Real.exp (-1)) (Real.exp (-1 + η))))
        (fun x : ℝ =>
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹)
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (by
        simpa [canonicalCentralResolventWindow] using hwindow_pos)]
  have hconst :
      (∫ x in canonicalCentralResolventWindow η,
        (logarithmicResolventDenominator
          (Complex.I * (η : ℂ)) x)⁻¹ *
          canonicalCompletedC3SymplecticCommonFiberEnergy
            (Complex.I * (η : ℂ)) ∂μ) =
        canonicalCompletedC3SymplecticCommonFiberEnergy
            (Complex.I * (η : ℂ)) *
          (∫ x in canonicalCentralResolventWindow η,
            (logarithmicResolventDenominator
              (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) := by
    calc
      (∫ x in canonicalCentralResolventWindow η,
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ *
            canonicalCompletedC3SymplecticCommonFiberEnergy
              (Complex.I * (η : ℂ)) ∂μ) =
          ∫ x in canonicalCentralResolventWindow η,
            canonicalCompletedC3SymplecticCommonFiberEnergy
                (Complex.I * (η : ℂ)) *
              (logarithmicResolventDenominator
                (Complex.I * (η : ℂ)) x)⁻¹ ∂μ := by
        congr 1
        funext x
        ring
      _ = canonicalCompletedC3SymplecticCommonFiberEnergy
              (Complex.I * (η : ℂ)) *
            (∫ x in canonicalCentralResolventWindow η,
              (logarithmicResolventDenominator
                (Complex.I * (η : ℂ)) x)⁻¹ ∂μ) := by
        rw [integral_const_mul]
      _ = _ := by rw [hmeasure]
  change canonicalCompletedC3SymplecticCommonFiberEnergy
      (Complex.I * (η : ℂ)) *
        (∫ x in canonicalCentralResolventWindow η,
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) ≤ ‖γ‖ ^ 2
  calc
    canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) *
        (∫ x in canonicalCentralResolventWindow η,
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) =
        (∫ x in canonicalCentralResolventWindow η,
          (logarithmicResolventDenominator
            (Complex.I * (η : ℂ)) x)⁻¹ *
            canonicalCompletedC3SymplecticCommonFiberEnergy
              (Complex.I * (η : ℂ)) ∂μ) := hconst.symm
    _ = ∫ x in canonicalCentralResolventWindow η,
          (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ := hseteq.symm
    _ ≤ ∫ x : ℝ, (‖γ.fst x‖ ^ 2 + ‖γ.snd x‖ ^ 2) ∂μ := hsetle
    _ = ‖γ‖ ^ 2 := hfull

theorem
    canonicalCompletedC3SymplecticGammaState_norm_sq_ge_source_over_eta
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (henergy :
      canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) ≥
        canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2) :
    canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
        Real.exp (-1) / (4 * η) ≤
      ‖canonicalCompletedC3SymplecticGammaState
          (Complex.I * (η : ℂ)) (by simp [hη.ne'])‖ ^ 2 := by
  have henergy0 :
      0 < canonicalCompletedC3SymplecticCommonFiberEnergy 0 :=
    canonicalCompletedC3SymplecticCommonFiberEnergy_zero_pos
  have henergy_nonneg :
      0 ≤ canonicalCompletedC3SymplecticCommonFiberEnergy
        (Complex.I * (η : ℂ)) := by
    linarith
  have hinv_nonneg : 0 ≤ Real.exp (-1) / (2 * η) := by
    positivity
  have hwindow :=
    canonicalCentralResolventWindow_integral_inv_denominator_ge hη hη1
  have hwindow_lower :=
    mul_le_mul_of_nonneg_left hwindow
      (le_of_lt henergy0)
  have henergy_lower :=
    mul_le_mul_of_nonneg_right henergy
      hinv_nonneg
  have hproduct_lower :
      canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2 *
          (Real.exp (-1) / (2 * η)) ≤
        canonicalCompletedC3SymplecticCommonFiberEnergy
            (Complex.I * (η : ℂ)) *
          (Real.exp (-1) / (2 * η)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using henergy_lower
  have henergy_product_nonneg :
      0 ≤ canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) := henergy_nonneg
  have hproduct_window :
      canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) *
          (Real.exp (-1) / (2 * η)) ≤
        canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) *
          (∫ x in canonicalCentralResolventWindow η,
            (logarithmicResolventDenominator
              (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) := by
    exact mul_le_mul_of_nonneg_left hwindow
      henergy_product_nonneg
  have hmain :=
    canonicalCompletedC3SymplecticGammaState_norm_sq_ge_commonWindow
      hη hη1
  calc
    canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
          Real.exp (-1) / (4 * η) =
    canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2 *
          (Real.exp (-1) / (2 * η)) := by
      field_simp [hη.ne']
      ring
    _ ≤ canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) *
          (Real.exp (-1) / (2 * η)) := hproduct_lower
    _ ≤ canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * (η : ℂ)) *
          (∫ x in canonicalCentralResolventWindow η,
            (logarithmicResolventDenominator
              (Complex.I * (η : ℂ)) x)⁻¹ ∂volume) := hproduct_window
    _ ≤ ‖canonicalCompletedC3SymplecticGammaState
          (Complex.I * (η : ℂ)) (by simp [hη.ne'])‖ ^ 2 := hmain

theorem
    canonicalCompletedC3SymplecticGammaState_norm_sq_radial_eventually_ge_source_over_eta :
    ∀ᶠ k : ℕ in atTop,
      canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
          Real.exp (-1) /
            (4 * (((k : ℝ) + 1)⁻¹)) ≤
        ‖canonicalCompletedC3SymplecticGammaState
            (canonicalCompletedC3RadialSecondStep k)
            (by
              simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 := by
  have henergy :=
    canonicalCompletedC3RadialSecondStep_tendsto_zero.eventually
      canonicalCompletedC3SymplecticCommonFiberEnergy_eventually_ge_half
  filter_upwards [henergy] with k hk
  have hη : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  have hkplus : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hη1 : ((k : ℝ) + 1)⁻¹ ≤ (1 : ℝ) := by
    exact (inv_le_one₀ (by positivity)).2 hkplus
  have hstep : canonicalGreenJetStep k =
      ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    rw [← canonicalGreenJetRealStep_coe]
    rfl
  have hradial : canonicalCompletedC3RadialSecondStep k =
      Complex.I * ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    simp [canonicalCompletedC3RadialSecondStep, hstep]
  have henergy' :
      canonicalCompletedC3SymplecticCommonFiberEnergy
          (Complex.I * ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)) ≥
        canonicalCompletedC3SymplecticCommonFiberEnergy 0 / 2 := by
    simpa [hradial] using hk
  have hbound :=
    canonicalCompletedC3SymplecticGammaState_norm_sq_ge_source_over_eta
      hη hη1 henergy'
  simpa [hradial] using hbound

theorem
    canonicalCompletedC3RawHeightValue_scaled_norm_sq_eventually_bounded :
    ∃ M : ℝ, 0 < M ∧
      ∀ᶠ k : ℕ in atTop,
        ‖((Real.sqrt 2 : ℝ) : ℂ) *
            canonicalCompletedC3RawHeightValue
              (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 ≤ M := by
  have hdomain :
      {z : ℂ | operatorHeightParameter z ∈ genuineCriticalStrip} ∈
        nhds 0 :=
    (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds
        zero_mem_completedNativeHeightDomain)
  have hrawEq :
      (fun z : ℂ => canonicalCompletedC3RawHeightValue z) =ᶠ[nhds 0]
        (fun z : ℂ => canonicalC3ChartFactorHeight z * nativeHeightScalar z) := by
    filter_upwards [hdomain] with z hz
    exact canonicalCompletedC3RawHeightValue_eq_chart_mul_nativeHeightScalar hz
  have hraw : ContinuousAt canonicalCompletedC3RawHeightValue 0 := by
    have hprod : ContinuousAt
        (fun z : ℂ => canonicalC3ChartFactorHeight z * nativeHeightScalar z) 0 :=
      canonicalC3ChartFactorHeight_analyticAt_zero.continuousAt.mul
        nativeHeightScalar_analyticAt_zero.continuousAt
    exact hprod.congr hrawEq.symm
  let c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  let M : ℝ := ‖c * canonicalCompletedC3RawHeightValue 0‖ ^ 2 + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hscaled : ContinuousAt
      (fun z : ℂ => ‖c * canonicalCompletedC3RawHeightValue z‖ ^ 2) 0 := by
    exact (hraw.const_mul c).norm.pow 2
  have hMnhds :
      Set.Iio M ∈ nhds
        (‖c * canonicalCompletedC3RawHeightValue 0‖ ^ 2) := by
    apply Iio_mem_nhds
    dsimp [M]
    linarith
  have hMevent : ∀ᶠ z : ℂ in nhds 0,
      ‖c * canonicalCompletedC3RawHeightValue z‖ ^ 2 ∈ Set.Iio M :=
    hscaled hMnhds
  have hradial :=
    canonicalCompletedC3RadialSecondStep_tendsto_zero.eventually hMevent
  refine ⟨M, hM, ?_⟩
  filter_upwards [hradial] with k hk
  have hk' :
      ‖c * canonicalCompletedC3RawHeightValue
          (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 < M := hk
  simpa [c, norm_mul] using (le_of_lt hk')

theorem
    canonicalCompletedC3NormalizedSymplecticGammaState_radial_lower_bound :
    ∃ C : ℝ, ∃ K : ℕ, 0 < C ∧
      ∀ k : ℕ, K ≤ k →
        C * ((k : ℝ) + 1) ≤
          ‖canonicalCompletedC3NormalizedSymplecticGammaState
              (canonicalCompletedC3RadialSecondStep k)
              (by
                simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                  using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 := by
  rcases canonicalCompletedC3RawHeightValue_scaled_norm_sq_eventually_bounded with
    ⟨M, hM, hMbound⟩
  let Csource : ℝ :=
    canonicalCompletedC3SymplecticCommonFiberEnergy 0 * Real.exp (-1) / 4
  have hCsource : 0 < Csource := by
    have henergy0 := canonicalCompletedC3SymplecticCommonFiberEnergy_zero_pos
    dsimp [Csource]
    positivity
  let C : ℝ := Csource / M
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos hCsource hM
  have hrawEvent :
      ∀ᶠ k : ℕ in atTop,
        canonicalCompletedC3RawHeightValue
            (canonicalCompletedC3RadialSecondStep k) ≠ 0 := by
    filter_upwards [canonicalCompletedC3RadialTiltPoint_eventually_admissible 0]
      with k hk
    have hkstrip :
        operatorHeightParameter
            (canonicalCompletedC3RadialSecondStep k) ∈ genuineCriticalStrip := by
      simpa [completedNativeHeightDomain,
        ← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep] using hk.1
    have hkF :
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialSecondStep k) ≠ 0 := by
      simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep] using hk.2
    exact canonicalCompletedC3RawHeightValue_ne_zero hkstrip hkF
  have hgammaEvent :=
    canonicalCompletedC3SymplecticGammaState_norm_sq_radial_eventually_ge_source_over_eta
  have hboth : ∀ᶠ k : ℕ in atTop,
      ‖((Real.sqrt 2 : ℝ) : ℂ) *
          canonicalCompletedC3RawHeightValue
            (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 ≤ M ∧
        canonicalCompletedC3RawHeightValue
            (canonicalCompletedC3RadialSecondStep k) ≠ 0 ∧
        canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
            Real.exp (-1) /
              (4 * (((k : ℝ) + 1)⁻¹)) ≤
          ‖canonicalCompletedC3SymplecticGammaState
              (canonicalCompletedC3RadialSecondStep k)
              (by
                simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                  using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 := by
    exact hMbound.and (hrawEvent.and hgammaEvent)
  rcases eventually_atTop.1 hboth with ⟨K, hK⟩
  refine ⟨C, K, hC, ?_⟩
  intro k hk
  have hkdata := hK k hk
  rcases hkdata with ⟨hMboundk, hrawk, hGammak⟩
  have hkplus : 0 < (k : ℝ) + 1 := by positivity
  have hsource_eq :
      Csource * ((k : ℝ) + 1) =
        canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
          Real.exp (-1) / (4 * (((k : ℝ) + 1)⁻¹)) := by
    dsimp [Csource]
    field_simp [ne_of_gt hkplus]
  have hGammak' :
      Csource * ((k : ℝ) + 1) ≤
        ‖canonicalCompletedC3SymplecticGammaState
            (canonicalCompletedC3RadialSecondStep k)
            (by
              simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 := by
    calc
      Csource * ((k : ℝ) + 1) =
          canonicalCompletedC3SymplecticCommonFiberEnergy 0 *
            Real.exp (-1) / (4 * (((k : ℝ) + 1)⁻¹)) := hsource_eq
      _ ≤ _ := hGammak
  have hrawscaled :
      ((Real.sqrt 2 : ℝ) : ℂ) *
          canonicalCompletedC3RawHeightValue
            (canonicalCompletedC3RadialSecondStep k) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hrawk
  have hdenpos : 0 <
      ‖((Real.sqrt 2 : ℝ) : ℂ) *
          canonicalCompletedC3RawHeightValue
            (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hrawscaled)
  have hnormeq :
      ‖canonicalCompletedC3NormalizedSymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 =
        ‖canonicalCompletedC3SymplecticGammaState
            (canonicalCompletedC3RadialSecondStep k)
            (by
              simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 /
          ‖((Real.sqrt 2 : ℝ) : ℂ) *
              canonicalCompletedC3RawHeightValue
                (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 := by
    unfold canonicalCompletedC3NormalizedSymplecticGammaState
    rw [norm_smul, norm_inv]
    field_simp [norm_ne_zero_iff.mpr hrawscaled]
  have hGnonneg : 0 ≤
      ‖canonicalCompletedC3SymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 :=
    sq_nonneg _
  have hGdivM :
      (Csource * ((k : ℝ) + 1)) / M ≤
        ‖canonicalCompletedC3SymplecticGammaState
            (canonicalCompletedC3RadialSecondStep k)
            (by
              simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 / M :=
    div_le_div_of_nonneg_right hGammak' hM.le
  have hMdivden :
      ‖canonicalCompletedC3SymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 / M ≤
        ‖canonicalCompletedC3SymplecticGammaState
            (canonicalCompletedC3RadialSecondStep k)
            (by
              simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
                using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 /
          ‖((Real.sqrt 2 : ℝ) : ℂ) *
              canonicalCompletedC3RawHeightValue
                (canonicalCompletedC3RadialSecondStep k)‖ ^ 2 := by
    apply (div_le_div_iff₀ hM hdenpos).2
    exact mul_le_mul_of_nonneg_left hMboundk hGnonneg
  rw [hnormeq]
  calc
    C * ((k : ℝ) + 1) =
        (Csource * ((k : ℝ) + 1)) / M := by
          dsimp [C]
          ring
    _ ≤ ‖canonicalCompletedC3SymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 / M := hGdivM
    _ ≤ _ := hMdivden

theorem
    canonicalCompletedC3NormalizedSymplecticGammaKernel_diagonal_not_tendsto_finite
    (a : ℂ) :
    ¬ Tendsto
      (fun k : ℕ =>
        canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
          (canonicalCompletedC3RadialSecondStep k)
          (canonicalCompletedC3RadialSecondStep k))
      Filter.atTop
      (nhds a) := by
  intro hconv
  have hreal :
      Tendsto
        (fun k : ℕ =>
          (canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
            (canonicalCompletedC3RadialSecondStep k)
            (canonicalCompletedC3RadialSecondStep k)).re)
        Filter.atTop (nhds a.re) := by
    have hre : Tendsto Complex.re (nhds a) (nhds a.re) :=
      Complex.continuous_re.continuousAt.tendsto
    simpa only [Function.comp_def] using hre.comp hconv
  have hrealBound : ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
        (canonicalCompletedC3RadialSecondStep k)
        (canonicalCompletedC3RadialSecondStep k)).re < a.re + 1 := by
    exact hreal (Iio_mem_nhds (by linarith))
  rcases eventually_atTop.1 hrealBound with ⟨Kbound, hbound⟩
  rcases canonicalCompletedC3NormalizedSymplecticGammaState_radial_lower_bound with
    ⟨C, Klower, hC, hlower⟩
  have hdiag (k : ℕ) :
      (canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
        (canonicalCompletedC3RadialSecondStep k)
        (canonicalCompletedC3RadialSecondStep k)).re =
        ‖canonicalCompletedC3NormalizedSymplecticGammaState
          (canonicalCompletedC3RadialSecondStep k)
          (by
            simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
              using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)‖ ^ 2 := by
    have hk :
        (canonicalCompletedC3RadialSecondStep k).im ≠ 0 := by
      simpa [← canonicalCompletedC3RadialTiltPoint_zero_eq_secondStep]
        using canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0
    rw [canonicalCompletedC3TotalNormalizedSymplecticGammaKernel_of_offAxis
        _ _ hk hk,
      canonicalCompletedC3NormalizedSymplecticGammaKernel_eq_inner _ _ hk hk]
    rw [RealHilbertComplexification.inner_apply,
      RealHilbertComplexification.complexInner_re]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    exact (WithLp.prod_norm_sq_eq_of_L2 _).symm
  have hlowerRe : ∀ k : ℕ, Klower ≤ k →
      C * ((k : ℝ) + 1) ≤
        (canonicalCompletedC3TotalNormalizedSymplecticGammaKernel
          (canonicalCompletedC3RadialSecondStep k)
          (canonicalCompletedC3RadialSecondStep k)).re := by
    intro k hk
    rw [hdiag]
    exact hlower k hk
  obtain ⟨N, hN⟩ := exists_nat_gt ((a.re + 1) / C)
  let k : ℕ := max Kbound Klower + N + 1
  have hkbound : Kbound ≤ k := by
    dsimp [k]
    omega
  have hklower : Klower ≤ k := by
    dsimp [k]
    omega
  have hNnat : N ≤ k + 1 := by
    dsimp [k]
    omega
  have hNreal : (N : ℝ) ≤ (k : ℝ) + 1 := by
    exact_mod_cast hNnat
  have hratio : (a.re + 1) / C < (k : ℝ) + 1 :=
    lt_of_lt_of_le hN hNreal
  have hlarge : a.re + 1 < C * ((k : ℝ) + 1) := by
    have hlarge' := (div_lt_iff₀ hC).mp hratio
    nlinarith
  have hup := hbound k hkbound
  have hlow := hlowerRe k hklower
  linarith

theorem
    not_CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness :
    ¬ CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness := by
  intro hflat
  have hgamma :=
    (canonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness_iff_gammaKernel_tendsto).1
      hflat
  have hdiag :=
    canonicalCompletedC3NormalizedSymplecticGammaKernel_diagonal_tendsto_h0_of_zeroth
      hgamma
  exact
    canonicalCompletedC3NormalizedSymplecticGammaKernel_diagonal_not_tendsto_finite
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) hdiag

theorem
    not_CanonicalCompletedC3SymplecticNormalizedLedgerJetFlatness :
    ¬ CanonicalCompletedC3SymplecticNormalizedLedgerJetFlatness := by
  intro hflat
  have hzero : CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness := by
    unfold CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness
    simpa only [completedGreenKernelTwoStepShiftedForwardDifference_zero_zero] using
      hflat 0 0
  exact not_CanonicalCompletedC3SymplecticNormalizedLedgerZerothFlatness hzero

end

end CarrySelfAdjointOperator
