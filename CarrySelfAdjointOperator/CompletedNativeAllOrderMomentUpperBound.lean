import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Uniform coefficient estimates from the existing canonical theta cosine
representation. No corrected metric, moment positivity, fitted carrier or
external numerical certificate is an input. -/
open Real Set Filter MeasureTheory
open scoped BigOperators
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 800000

private theorem integrableOn_mul_cos_of_integrableOn
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) (t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ f u * Real.cos (t * u)) (Ioi (0 : ℝ)) := by
  apply hf.mul_bdd
  · exact (by fun_prop : Continuous
      (fun u : ℝ ↦ Real.cos (t * u))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * u))

private theorem integrableOn_mul_sin_of_integrableOn
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) (t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ f u * Real.sin (t * u)) (Ioi (0 : ℝ)) := by
  apply hf.mul_bdd
  · exact (by fun_prop : Continuous
      (fun u : ℝ ↦ Real.sin (t * u))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t * u))

private theorem hasDerivAt_integral_mul_cos
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (huf : IntegrableOn (fun u : ℝ ↦ u * f u) (Ioi (0 : ℝ)))
    (t : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ ∫ u in Ioi (0 : ℝ), f u * Real.cos (x * u))
      (∫ u in Ioi (0 : ℝ), -(u * f u) * Real.sin (t * u)) t := by
  let F : ℝ → ℝ → ℝ := fun x u ↦ f u * Real.cos (x * u)
  let F' : ℝ → ℝ → ℝ := fun x u ↦ -(u * f u) * Real.sin (x * u)
  let bound : ℝ → ℝ := fun u ↦ ‖u * f u‖
  have hFmeas : ∀ᶠ x in nhds t,
      AEStronglyMeasurable (F x) (volume.restrict (Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall (fun x ↦
      (integrableOn_mul_cos_of_integrableOn hf x).aestronglyMeasurable)
  have hFint : Integrable (F t) (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn (F t) (Ioi (0 : ℝ))
    simpa [F] using integrableOn_mul_cos_of_integrableOn hf t
  have hF'meas :
      AEStronglyMeasurable (F' t) (volume.restrict (Ioi (0 : ℝ))) := by
    have hneg : IntegrableOn (fun u : ℝ ↦ -(u * f u)) (Ioi (0 : ℝ)) :=
      huf.neg
    simpa [F'] using
      (integrableOn_mul_sin_of_integrableOn hneg t).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x u‖ ≤ bound u := by
    filter_upwards [] with u
    intro x _hx
    dsimp [F', bound]
    rw [abs_mul]
    calc
      |-(u * f u)| * |Real.sin (x * u)| ≤
          |-(u * f u)| * 1 := by
        gcongr
        exact Real.abs_sin_le_one (x * u)
      _ = |u * f u| := by simp
  have hboundInt : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [bound] using huf.norm
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (F · u) (F' x u) x := by
    filter_upwards [] with u
    intro x _hx
    have hlinear : HasDerivAt (fun y : ℝ ↦ y * u) u x :=
      by simpa only [id_eq, one_mul] using (hasDerivAt_id x).mul_const u
    have hcos := (Real.hasDerivAt_cos (x * u)).comp x hlinear
    dsimp [F, F']
    refine ((hcos.const_mul (f u)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ ↦ rfl))).congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (s := Set.univ)
    (x₀ := t) (μ := volume.restrict (Ioi (0 : ℝ)))
    univ_mem hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa [F, F'] using hmain.2

private theorem hasDerivAt_integral_mul_sin
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (huf : IntegrableOn (fun u : ℝ ↦ u * f u) (Ioi (0 : ℝ)))
    (t : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ ∫ u in Ioi (0 : ℝ), f u * Real.sin (x * u))
      (∫ u in Ioi (0 : ℝ), (u * f u) * Real.cos (t * u)) t := by
  let F : ℝ → ℝ → ℝ := fun x u ↦ f u * Real.sin (x * u)
  let F' : ℝ → ℝ → ℝ := fun x u ↦ (u * f u) * Real.cos (x * u)
  let bound : ℝ → ℝ := fun u ↦ ‖u * f u‖
  have hFmeas : ∀ᶠ x in nhds t,
      AEStronglyMeasurable (F x) (volume.restrict (Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall (fun x ↦
      (integrableOn_mul_sin_of_integrableOn hf x).aestronglyMeasurable)
  have hFint : Integrable (F t) (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn (F t) (Ioi (0 : ℝ))
    simpa [F] using integrableOn_mul_sin_of_integrableOn hf t
  have hF'meas :
      AEStronglyMeasurable (F' t) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [F'] using
      (integrableOn_mul_cos_of_integrableOn huf t).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x u‖ ≤ bound u := by
    filter_upwards [] with u
    intro x _hx
    dsimp [F', bound]
    rw [abs_mul]
    calc
      |u * f u| * |Real.cos (x * u)| ≤
          |u * f u| * 1 := by
        gcongr
        exact Real.abs_cos_le_one (x * u)
      _ = |u * f u| := by ring
  have hboundInt : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [bound] using huf.norm
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (F · u) (F' x u) x := by
    filter_upwards [] with u
    intro x _hx
    have hlinear : HasDerivAt (fun y : ℝ ↦ y * u) u x :=
      by simpa only [id_eq, one_mul] using (hasDerivAt_id x).mul_const u
    have hsin := (Real.hasDerivAt_sin (x * u)).comp x hlinear
    dsimp [F, F']
    refine ((hsin.const_mul (f u)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ ↦ rfl))).congr_deriv ?_
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (s := Set.univ)
    (x₀ := t) (μ := volume.restrict (Ioi (0 : ℝ)))
    univ_mem hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa [F, F'] using hmain.2

private def cosineChannel (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), (u^(2*n) * completedNativeXiCosineKernel u) * Real.cos (t*u)
private def sineChannel (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), (u^(2*n+1) * completedNativeXiCosineKernel u) * Real.sin (t*u)

private theorem cosineChannel_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (cosineChannel n) (-sineChannel n t) t := by
  have hu : IntegrableOn (fun u : ℝ => u * (u^(2*n) * completedNativeXiCosineKernel u)) (Ioi 0) := by
    convert integrableOn_pow_mul_completedNativeXiCosineKernel (2*n+1) using 1
    funext u; ring
  have h := hasDerivAt_integral_mul_cos
    (integrableOn_pow_mul_completedNativeXiCosineKernel (2*n)) hu t
  apply h.congr_deriv
  dsimp [sineChannel]
  rw [← integral_neg]
  congr 1; funext u; ring

private theorem sineChannel_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (sineChannel n) (cosineChannel (n+1) t) t := by
  have hu : IntegrableOn (fun u : ℝ => u * (u^(2*n+1) * completedNativeXiCosineKernel u)) (Ioi 0) := by
    convert integrableOn_pow_mul_completedNativeXiCosineKernel (2*(n+1)) using 1
    funext u; ring
  apply (hasDerivAt_integral_mul_sin
    (integrableOn_pow_mul_completedNativeXiCosineKernel (2*n+1)) hu t).congr_deriv
  dsimp [cosineChannel]
  congr 1; funext u; ring

private theorem iteratedDeriv_cosineChannel (n : ℕ) :
    iteratedDeriv (2*n) (fun t : ℝ => (cosineChannel 0 t : ℂ)) =
      fun t => (((-1 : ℝ)^n * cosineChannel n t : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, iteratedDeriv_succ,
      iteratedDeriv_succ, ih]
    funext t
    have hd : deriv (fun t => (((-1 : ℝ)^n * cosineChannel n t : ℝ) : ℂ)) =
        fun t => (((-1 : ℝ)^n * (-sineChannel n t) : ℝ) : ℂ) := by
      funext t
      exact (((cosineChannel_deriv n t).const_mul _).ofReal_comp).deriv
    rw [hd]
    have hs := ((((sineChannel_deriv n t).neg).const_mul ((-1 : ℝ)^n)).ofReal_comp).deriv
    change deriv (fun t => (((-1 : ℝ)^n * (-sineChannel n t) : ℝ) : ℂ)) t =
      (((-1 : ℝ)^n * (-cosineChannel (n+1) t) : ℝ) : ℂ) at hs
    rw [hs, pow_succ]
    push_cast
    ring

/-- All even canonical characteristic coefficients are the actual cosine
moments divided by their factorial, with the alternating sign preserved. -/
theorem completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient n =
      (-1 : ℝ)^n * completedNativeXiCosineMoment n / (2*n).factorial := by
  have haxis : (fun t : ℝ => completedNativeOperatorCharacteristic (t : ℂ)) =
      fun t : ℝ => (cosineChannel 0 t : ℂ) := by
    funext t
    simpa [cosineChannel] using XiThetaCosine.completedNative_eq_xiCosineKernel t
  have hd : iteratedDeriv (2*n) completedNativeOperatorCharacteristic (0 : ℂ) =
      (((-1 : ℝ)^n * completedNativeXiCosineMoment n : ℝ) : ℂ) := by
    change iteratedDeriv (2*n) completedNativeOperatorCharacteristic ((0 : ℝ) : ℂ) = _
    rw [← iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal (2*n) 0, haxis]
    rw [iteratedDeriv_cosineChannel]
    simp [cosineChannel, completedNativeXiCosineMoment]
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [hd]
  change (((((2*n).factorial : ℝ) : ℂ)⁻¹ *
    (((-1 : ℝ)^n * completedNativeXiCosineMoment n : ℝ) : ℂ)).re) = _
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- An explicit all-order theta-tail bound from the already local exponential
majorant. The factorial is essential and cancels in Taylor coefficients. -/
theorem completedNativeThetaTailMoment_factorial_upper (p : ℕ) :
    completedNativeThetaTailMoment p ≤ (p.factorial : ℝ) / (7 * 5^(p+1)) := by
  have hp : -(1 : ℝ) < (p : ℝ) := by
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (p : ℝ)) (b := (5 : ℝ)) hp (by norm_num) (by norm_num)
  have hint : IntegrableOn (fun u : ℝ => u^p * Real.exp (-5*u)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using hi
  have hm := integral_mono_ae (integrableOn_pow_mul_thetaTail p)
    (hint.const_mul (1/7 : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hb := calibration_thetaTail_le_exp hu.le
      nlinarith [mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le p)])
  have he := integral_rpow_mul_exp_neg_mul_Ioi
    (a := (p : ℝ)+1) (r := (5 : ℝ)) (by positivity) (by norm_num)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at he
  rw [← Nat.cast_add_one, Real.rpow_natCast] at he
  simp only [neg_mul] at hm
  rw [integral_const_mul, he] at hm
  simpa [completedNativeThetaTailMoment, one_div_pow, div_eq_mul_inv, mul_assoc,
    mul_comm, mul_left_comm] using hm

/-- The actual constant coefficient has an unconditional positive ruler. -/
theorem completedNativeRealEvenCharacteristicCoefficient_zero_ge_third :
    (1/3 : ℝ) ≤ completedNativeRealEvenCharacteristicCoefficient 0 := by
  rw [completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment,
    completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  linarith [completedNativeThetaTailMoment_zero_le_calibration]

/-- Explicit upper bound at every positive coefficient order, independent of
any Gram or correction certificate. -/
theorem completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper (n : ℕ) :
    |completedNativeRealEvenCharacteristicCoefficient (n+1)| ≤
      1 / (35 * 25^n : ℝ) := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder,
    abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (completedNativeXiCosineMoment_pos (n+1)),
    abs_of_pos (by positivity : (0 : ℝ) < (2*(n+1)).factorial)]
  have hb := completedNativeThetaTailMoment_factorial_upper (2*n)
  have hnonneg := completedNativeThetaTailMoment_nonneg (2*n+2)
  have hmu := completedNativeXiCosineMoment_succ_eq_thetaTailMoments n
  have hfac : (((2*(n+1)).factorial : ℕ) : ℝ) =
      ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * ( (2*n).factorial : ℝ) := by
    rw [show 2*(n+1) = (2*n+1)+1 by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2*(n+1)).factorial)).mpr
  rw [hfac]
  have hb' := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ))
  have heq : (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ)) *
      ((2*n).factorial / (7 * 5^(2*n+1) : ℝ)) =
      1/(35*25^n : ℝ) *
        (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * ((2*n).factorial : ℝ)) := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [heq] at hb'
  nlinarith

/-- Positive-order coefficients relative to the actual constant coefficient
have a uniform geometric bound with certified ratio 1/4. -/
theorem completedNativeRealEvenCharacteristicCoefficient_succ_relative_bound (n : ℕ) :
    |completedNativeRealEvenCharacteristicCoefficient (n+1)| ≤
      completedNativeRealEvenCharacteristicCoefficient 0 * (1/4 : ℝ)^(n+1) := by
  have hb := completedNativeRealEvenCharacteristicCoefficient_succ_abs_upper n
  have h0 := completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hp : (1/25 : ℝ)^n ≤ (1/4 : ℝ)^n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have heq : 1/(35*25^n : ℝ) = (1/35 : ℝ)*(1/25 : ℝ)^n := by
    rw [one_div_pow, ← one_div_mul_one_div]
  rw [heq] at hb
  have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) n
  have hc := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1/35)
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right h0 hn]


private theorem prefix_geometric_convolution_bound (n : ℕ) :
    (∑ k ∈ Finset.range n, (3/4 : ℝ)^k * (1/4 : ℝ)^(n-k)) ≤
      (1/2 : ℝ) * (3/4 : ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : (∑ k ∈ Finset.range (n+1), (3/4 : ℝ)^k * (1/4 : ℝ)^(n+1-k)) =
        (1/4 : ℝ) * (∑ k ∈ Finset.range n, (3/4 : ℝ)^k * (1/4 : ℝ)^(n-k)) +
          (1/4 : ℝ)*(3/4 : ℝ)^n := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [show n+1-k = (n-k)+1 by omega, pow_succ]
        ring
      · simp; ring
    rw [heq, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1/4)]

private theorem coefficient_derivative_geometric_bound (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * (1/4 : ℝ)^(n+1) ≤ (1/4 : ℝ) * (3/4 : ℝ)^n := by
  have hn : ((n+1 : ℕ) : ℝ) ≤ (3 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := mul_le_mul_of_nonneg_right hn (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/4) n)
  rw [← mul_pow] at hb
  norm_num at hb
  rw [pow_succ]
  push_cast
  nlinarith

/-- Uniform, explicit decay of the actual canonical logarithmic moments.
This follows from their existing recurrence and the theta coefficient bound,
without correction, loss realization, or any moment-positivity hypothesis. -/
theorem canonicalCompletedNativeLogDerivativeMoment_explicit_decay (n : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment n| ≤ (1/2 : ℝ) * (3/4 : ℝ)^n := by
  have h0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [canonicalCompletedNativeLogDerivativeMoment_eq, abs_div, abs_of_pos h0]
    apply (div_le_iff₀ h0).mpr
    have hs : |∑ k ∈ Finset.range n,
        canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| ≤
        completedNativeRealEvenCharacteristicCoefficient 0 * (1/4 : ℝ) * (3/4 : ℝ)^n := by
      calc
        _ ≤ ∑ k ∈ Finset.range n,
            |canonicalCompletedNativeLogDerivativeMoment k| *
              |completedNativeRealEvenCharacteristicCoefficient (n-k)| := by
          simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
            (fun k => canonicalCompletedNativeLogDerivativeMoment k *
              completedNativeRealEvenCharacteristicCoefficient (n-k)) (Finset.range n)
        _ ≤ ∑ k ∈ Finset.range n,
            ((1/2 : ℝ)*(3/4 : ℝ)^k) *
              (completedNativeRealEvenCharacteristicCoefficient 0 * (1/4 : ℝ)^(n-k)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkn := Finset.mem_range.mp hk
          have hc := completedNativeRealEvenCharacteristicCoefficient_succ_relative_bound (n-k-1)
          rw [show n-k-1+1 = n-k by omega] at hc
          exact mul_le_mul (ih k hkn) hc (abs_nonneg _) (by positivity)
        _ = (completedNativeRealEvenCharacteristicCoefficient 0 * (1/2 : ℝ)) *
            ∑ k ∈ Finset.range n, (3/4 : ℝ)^k * (1/4 : ℝ)^(n-k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_left (prefix_geometric_convolution_bound n)
            (by positivity : 0 ≤ completedNativeRealEvenCharacteristicCoefficient 0 * (1/2 : ℝ))]
    have hn := completedNativeRealEvenCharacteristicCoefficient_succ_relative_bound n
    have hd := coefficient_derivative_geometric_bound n
    have ha : |-(((n+1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n+1)) -
        ∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| ≤
        ((n+1 : ℕ) : ℝ) * |completedNativeRealEvenCharacteristicCoefficient (n+1)| +
        |∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n-k)| := by
      simpa only [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n+1))] using
        abs_sub (-(((n+1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n+1)))
          (∑ k ∈ Finset.range n, canonicalCompletedNativeLogDerivativeMoment k *
            completedNativeRealEvenCharacteristicCoefficient (n-k))
    have hn' := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (n+1))
    have hd' := mul_le_mul_of_nonneg_left hd h0.le
    simp only [neg_mul]
    nlinarith


end
end CarrySelfAdjointOperator
