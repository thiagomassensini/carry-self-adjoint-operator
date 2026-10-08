import CarrySelfAdjointOperator.CompletedNativeXiCosineTransform
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Moments of the positive Xi cosine kernel

The theta-series construction gives exponential decay of the concrete Xi
kernel.  This file turns that pointwise estimate into integrability of every
polynomially weighted kernel and proves strict positivity of all its even
moments.  These facts are the analytic input needed both for differentiating
the cosine transform and for the low-order Herglotz certificate.
-/

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section

/-- Every polynomial weight of the concrete Xi kernel is integrable on the
positive half-line. -/
theorem integrableOn_pow_mul_completedNativeXiCosineKernel (power : ℕ) :
    IntegrableOn
      (fun u : ℝ ↦ u ^ power * completedNativeXiCosineKernel u)
      (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC, hdecay⟩ :=
    XiThetaCosine.exists_completedNativeXiCosineKernel_exp_decay
  have hbaseRpow : IntegrableOn
      (fun u : ℝ ↦
        u ^ (power : ℝ) *
          Real.exp (-(3 / 2 : ℝ) * u ^ (1 : ℝ)))
      (Ioi (0 : ℝ)) := by
    exact integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (power : ℝ)) (b := (3 / 2 : ℝ))
        (by
          have hpower : 0 ≤ (power : ℝ) := Nat.cast_nonneg power
          linarith)
        (by norm_num) (by norm_num)
  have hbase : IntegrableOn
      (fun u : ℝ ↦ u ^ power * Real.exp (-(3 / 2 : ℝ) * u))
      (Ioi (0 : ℝ)) := by
    apply hbaseRpow.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.rpow_natCast, Real.rpow_one]
  have hmajorant : IntegrableOn
      (fun u : ℝ ↦
        C * (u ^ power * Real.exp (-(3 / 2 : ℝ) * u)))
      (Ioi (0 : ℝ)) :=
    hbase.const_mul C
  apply hmajorant.mono'
  · exact
      ((continuous_id.pow power).aestronglyMeasurable.mul
        XiThetaCosine.integrableOn_completedNativeXiCosineKernel.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hpow : 0 ≤ u ^ power := pow_nonneg hu.le power
    calc
      ‖u ^ power * completedNativeXiCosineKernel u‖ =
          u ^ power * ‖completedNativeXiCosineKernel u‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpow]
      _ ≤ u ^ power *
          (C * Real.exp (-(3 / 2 : ℝ) * u)) :=
        mul_le_mul_of_nonneg_left (hdecay hu.le) hpow
      _ = C * (u ^ power * Real.exp (-(3 / 2 : ℝ) * u)) := by
        ring

/-- In particular, every even moment appearing in the cosine expansion is
absolutely integrable. -/
theorem integrableOn_completedNativeXiCosineMoment (order : ℕ) :
    IntegrableOn
      (fun u : ℝ ↦
        u ^ (2 * order) * completedNativeXiCosineKernel u)
      (Ioi (0 : ℝ)) :=
  integrableOn_pow_mul_completedNativeXiCosineKernel (2 * order)

/-- Every even moment of the strictly positive Xi kernel is strictly
positive. -/
theorem completedNativeXiCosineMoment_pos (order : ℕ) :
    0 < completedNativeXiCosineMoment order := by
  let f : ℝ → ℝ := fun u ↦
    u ^ (2 * order) * completedNativeXiCosineKernel u
  have hfint : Integrable f (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn f (Ioi (0 : ℝ))
    simpa [f] using integrableOn_completedNativeXiCosineMoment order
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (pow_nonneg hu.le _) (completedNativeXiCosineKernel_pos hu.le).le
  have hintervalSupport : Ioo (1 : ℝ) 2 ⊆ Function.support f := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    exact mul_ne_zero (pow_ne_zero _ hu0.ne')
      (completedNativeXiCosineKernel_pos hu0.le).ne'
  have hintervalMeasure :
      0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo (1 : ℝ) 2) := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    have hinter : Ioo (1 : ℝ) 2 ∩ Ioi 0 = Ioo (1 : ℝ) 2 := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · exact fun h ↦ h.1
      · intro h
        exact ⟨h, lt_trans zero_lt_one h.1⟩
    rw [hinter, Real.volume_Ioo]
    norm_num
  rw [completedNativeXiCosineMoment]
  change 0 < ∫ u, f u ∂volume.restrict (Ioi (0 : ℝ))
  exact (integral_pos_iff_support_of_nonneg_ae hfnonneg hfint).2
    (hintervalMeasure.trans_le (measure_mono hintervalSupport))

/-- The real half-line cosine transform of the concrete Xi kernel. -/
def completedNativeXiCosineTransformReal (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    completedNativeXiCosineKernel u * Real.cos (t * u)

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

private def completedNativeXiCosineTransformFirst (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u * completedNativeXiCosineKernel u) * Real.sin (t * u)

private def completedNativeXiCosineTransformSecond (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u ^ 2 * completedNativeXiCosineKernel u) * Real.cos (t * u)

private def completedNativeXiCosineTransformThird (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (u ^ 3 * completedNativeXiCosineKernel u) * Real.sin (t * u)

private def completedNativeXiCosineTransformFourth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (u ^ 4 * completedNativeXiCosineKernel u) * Real.cos (t * u)

private theorem hasDerivAt_completedNativeXiCosineTransformReal (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformReal
      (completedNativeXiCosineTransformFirst t) t := by
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * completedNativeXiCosineKernel u)
      (Ioi (0 : ℝ)) := by
    simpa [pow_one] using
      integrableOn_pow_mul_completedNativeXiCosineKernel 1
  have h := hasDerivAt_integral_mul_cos
    XiThetaCosine.integrableOn_completedNativeXiCosineKernel huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x ↦ by
      unfold completedNativeXiCosineTransformReal
      rfl)
  · unfold completedNativeXiCosineTransformFirst
    rfl

private theorem hasDerivAt_completedNativeXiCosineTransformFirst (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformFirst
      (completedNativeXiCosineTransformSecond t) t := by
  have hf : IntegrableOn
      (fun u : ℝ ↦ -(u * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    simpa [pow_one] using
      (integrableOn_pow_mul_completedNativeXiCosineKernel 1).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 2).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x ↦ by
      unfold completedNativeXiCosineTransformFirst
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u ↦ by ring))
  · unfold completedNativeXiCosineTransformSecond
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem hasDerivAt_completedNativeXiCosineTransformSecond (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformSecond
      (completedNativeXiCosineTransformThird t) t := by
  have hf : IntegrableOn
      (fun u : ℝ ↦ -(u ^ 2 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_completedNativeXiCosineKernel 2).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u ^ 2 * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 3).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)
  have h := hasDerivAt_integral_mul_cos hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x ↦ by
      unfold completedNativeXiCosineTransformSecond
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u ↦ by ring))
  · unfold completedNativeXiCosineTransformThird
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem hasDerivAt_completedNativeXiCosineTransformThird (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformThird
      (completedNativeXiCosineTransformFourth t) t := by
  have hf := integrableOn_pow_mul_completedNativeXiCosineKernel 3
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (u ^ 3 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 4).congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun x ↦ by
      unfold completedNativeXiCosineTransformThird
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u ↦ by ring))
  · unfold completedNativeXiCosineTransformFourth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

/-- The second derivative at the center is minus the second kernel moment. -/
theorem iteratedDeriv_two_completedNativeXiCosineTransformReal_zero :
    iteratedDeriv 2 completedNativeXiCosineTransformReal 0 =
      -completedNativeXiCosineMoment 1 := by
  have hfirst : deriv completedNativeXiCosineTransformReal =
      completedNativeXiCosineTransformFirst := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).deriv
  rw [show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  rw [(hasDerivAt_completedNativeXiCosineTransformFirst 0).deriv]
  unfold completedNativeXiCosineTransformSecond completedNativeXiCosineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The fourth derivative at the center is the fourth kernel moment. -/
theorem iteratedDeriv_four_completedNativeXiCosineTransformReal_zero :
    iteratedDeriv 4 completedNativeXiCosineTransformReal 0 =
      completedNativeXiCosineMoment 2 := by
  have hfirst : deriv completedNativeXiCosineTransformReal =
      completedNativeXiCosineTransformFirst := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).deriv
  have hsecond : deriv completedNativeXiCosineTransformFirst =
      completedNativeXiCosineTransformSecond := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).deriv
  have hthird : deriv completedNativeXiCosineTransformSecond =
      completedNativeXiCosineTransformThird := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).deriv
  rw [show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird]
  rw [(hasDerivAt_completedNativeXiCosineTransformThird 0).deriv]
  unfold completedNativeXiCosineTransformFourth completedNativeXiCosineMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- Evaluation at the center is the total mass of the Xi kernel. -/
theorem completedNativeXiCosineTransformReal_zero :
    completedNativeXiCosineTransformReal 0 =
      completedNativeXiCosineMoment 0 := by
  unfold completedNativeXiCosineTransformReal completedNativeXiCosineMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

private theorem iteratedDeriv_two_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 2
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      ((-completedNativeXiCosineMoment 1 : ℝ) : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  rw [show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  rw [(hasDerivAt_completedNativeXiCosineTransformFirst 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformSecond completedNativeXiCosineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

private theorem iteratedDeriv_four_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 4
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      (completedNativeXiCosineMoment 2 : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  have hsecond : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).ofReal_comp.deriv
  have hthird : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).ofReal_comp.deriv
  rw [show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird]
  rw [(hasDerivAt_completedNativeXiCosineTransformThird 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformFourth completedNativeXiCosineMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The complex second derivative of the completed native characteristic is
the negative second moment of its positive cosine kernel. -/
theorem iteratedDeriv_two_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 2 completedNativeOperatorCharacteristic 0 =
      ((-completedNativeXiCosineMoment 1 : ℝ) : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 2 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 2
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 := by
      exact (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 2 0).symm
    _ = iteratedDeriv 2
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by
      rw [haxis]
    _ = ((-completedNativeXiCosineMoment 1 : ℝ) : ℂ) :=
      iteratedDeriv_two_completedNativeXiCosineTransform_ofReal_zero

/-- The complex fourth derivative of the completed native characteristic is
the fourth moment of its positive cosine kernel. -/
theorem iteratedDeriv_four_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 4 completedNativeOperatorCharacteristic 0 =
      (completedNativeXiCosineMoment 2 : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 4 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 4
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 := by
      exact (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 4 0).symm
    _ = iteratedDeriv 4
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by
      rw [haxis]
    _ = (completedNativeXiCosineMoment 2 : ℂ) :=
      iteratedDeriv_four_completedNativeXiCosineTransform_ofReal_zero

/-- The constant reduced Taylor coefficient is the kernel mass. -/
theorem completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 0 =
      completedNativeXiCosineMoment 0 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  simp only [mul_zero, iteratedDeriv_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul]
  calc
    (completedNativeOperatorCharacteristic 0).re =
        completedNativeXiCosineTransformReal 0 := by
      have h := congrArg Complex.re
        (XiThetaCosine.completedNative_eq_xiCosineKernel 0)
      simpa [completedNativeXiCosineTransformReal] using h
    _ = completedNativeXiCosineMoment 0 :=
      completedNativeXiCosineTransformReal_zero

/-- The quadratic reduced Taylor coefficient has the standard cosine-moment
normalization `-μ₂ / 2`. -/
theorem completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 1 =
      -completedNativeXiCosineMoment 1 / 2 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [show 2 * 1 = 2 by norm_num,
    iteratedDeriv_two_completedNativeOperatorCharacteristic_zero]
  norm_num [smul_eq_mul]
  ring

/-- The quartic reduced Taylor coefficient has the standard cosine-moment
normalization `μ₄ / 24`. -/
theorem completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 2 =
      completedNativeXiCosineMoment 2 / 24 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [show 2 * 2 = 4 by norm_num,
    iteratedDeriv_four_completedNativeOperatorCharacteristic_zero]
  norm_num [smul_eq_mul]
  ring

/-! ## Sixth-order coefficient in the same cosine representation -/

private def completedNativeXiCosineTransformFifth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u ^ 5 * completedNativeXiCosineKernel u) * Real.sin (t * u)

private def completedNativeXiCosineTransformSixth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u ^ 6 * completedNativeXiCosineKernel u) * Real.cos (t * u)

private theorem hasDerivAt_completedNativeXiCosineTransformFourth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformFourth
      (completedNativeXiCosineTransformFifth t) t := by
  have hf := integrableOn_pow_mul_completedNativeXiCosineKernel 4
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (u ^ 4 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 5).congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have h := hasDerivAt_integral_mul_cos hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformFifth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem hasDerivAt_completedNativeXiCosineTransformFifth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformFifth
      (completedNativeXiCosineTransformSixth t) t := by
  have hf := (integrableOn_pow_mul_completedNativeXiCosineKernel 5).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u ^ 5 * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 6).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformSixth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)

private theorem iteratedDeriv_six_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 6
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      ((-completedNativeXiCosineMoment 3 : ℝ) : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  have hsecond : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).ofReal_comp.deriv
  have hthird : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).ofReal_comp.deriv
  have hfourth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformThird t).ofReal_comp.deriv
  have hfifth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFourth t).ofReal_comp.deriv
  rw [show 6 = Nat.succ 5 by norm_num, iteratedDeriv_succ,
    show 5 = Nat.succ 4 by norm_num, iteratedDeriv_succ,
    show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird, hfourth, hfifth]
  rw [(hasDerivAt_completedNativeXiCosineTransformFifth 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformSixth completedNativeXiCosineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The same cosine kernel determines the sixth native derivative, with
the alternating cosine sign and the original moment normalization. -/
theorem iteratedDeriv_six_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 6 completedNativeOperatorCharacteristic 0 =
      ((-completedNativeXiCosineMoment 3 : ℝ) : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 6 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 6
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 :=
      (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 6 0).symm
    _ = iteratedDeriv 6
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by rw [haxis]
    _ = ((-completedNativeXiCosineMoment 3 : ℝ) : ℂ) :=
      iteratedDeriv_six_completedNativeXiCosineTransform_ofReal_zero

/-- The sextic coefficient is exactly `-μ₆/720`; no moment is redefined. -/
theorem completedNativeRealEvenCharacteristicCoefficient_three_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 3 =
      -completedNativeXiCosineMoment 3 / 720 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [show 2 * 3 = 6 by norm_num,
    iteratedDeriv_six_completedNativeOperatorCharacteristic_zero]
  norm_num [smul_eq_mul]
  ring

/-! ## Eighth-order coefficient in the same cosine representation -/

private def completedNativeXiCosineTransformSeventh (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    u ^ 7 * completedNativeXiCosineKernel u * Real.sin (t * u)

private def completedNativeXiCosineTransformEighth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    u ^ 8 * completedNativeXiCosineKernel u * Real.cos (t * u)

private theorem hasDerivAt_completedNativeXiCosineTransformSixth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformSixth
      (completedNativeXiCosineTransformSeventh t) t := by
  have hf := (integrableOn_pow_mul_completedNativeXiCosineKernel 6).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u ^ 6 * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 7).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)
  have h := hasDerivAt_integral_mul_cos hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformSeventh
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)

private theorem hasDerivAt_completedNativeXiCosineTransformSeventh (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformSeventh
      (completedNativeXiCosineTransformEighth t) t := by
  have hf := integrableOn_pow_mul_completedNativeXiCosineKernel 7
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (u ^ 7 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    apply integrableOn_pow_mul_completedNativeXiCosineKernel 8 |>.congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformEighth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem iteratedDeriv_eight_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 8
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      (completedNativeXiCosineMoment 4 : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  have hsecond : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).ofReal_comp.deriv
  have hthird : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).ofReal_comp.deriv
  have hfourth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformThird t).ofReal_comp.deriv
  have hfifth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFourth t).ofReal_comp.deriv
  have hsixth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFifth t).ofReal_comp.deriv
  have hseventh : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSeventh t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSixth t).ofReal_comp.deriv
  rw [show 8 = Nat.succ 7 by norm_num, iteratedDeriv_succ,
    show 7 = Nat.succ 6 by norm_num, iteratedDeriv_succ,
    show 6 = Nat.succ 5 by norm_num, iteratedDeriv_succ,
    show 5 = Nat.succ 4 by norm_num, iteratedDeriv_succ,
    show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird, hfourth, hfifth, hsixth, hseventh]
  rw [(hasDerivAt_completedNativeXiCosineTransformSeventh 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformEighth completedNativeXiCosineMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The same concrete cosine kernel determines the eighth native derivative. -/
theorem iteratedDeriv_eight_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 8 completedNativeOperatorCharacteristic 0 =
      (completedNativeXiCosineMoment 4 : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 8 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 8
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 :=
      (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 8 0).symm
    _ = iteratedDeriv 8
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by rw [haxis]
    _ = (completedNativeXiCosineMoment 4 : ℂ) :=
      iteratedDeriv_eight_completedNativeXiCosineTransform_ofReal_zero

/-- The octic reduced Taylor coefficient is exactly `μ₈ / 40320`. -/
theorem completedNativeRealEvenCharacteristicCoefficient_four_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 4 =
      completedNativeXiCosineMoment 4 / 40320 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [show 2 * 4 = 8 by norm_num,
    iteratedDeriv_eight_completedNativeOperatorCharacteristic_zero]
  norm_num [smul_eq_mul]
  ring

/-! ## Tenth-order coefficient in the same cosine representation -/

private def completedNativeXiCosineTransformNinth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u ^ 9 * completedNativeXiCosineKernel u) * Real.sin (t * u)

private def completedNativeXiCosineTransformTenth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    -(u ^ 10 * completedNativeXiCosineKernel u) * Real.cos (t * u)

private theorem hasDerivAt_completedNativeXiCosineTransformEighth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformEighth
      (completedNativeXiCosineTransformNinth t) t := by
  have hf := integrableOn_pow_mul_completedNativeXiCosineKernel 8
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (u ^ 8 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 9).congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have h := hasDerivAt_integral_mul_cos hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformNinth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem hasDerivAt_completedNativeXiCosineTransformNinth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformNinth
      (completedNativeXiCosineTransformTenth t) t := by
  have hf := (integrableOn_pow_mul_completedNativeXiCosineKernel 9).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u ^ 9 * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 10).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformTenth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by
      simp only [Pi.neg_apply]
      ring)

private theorem iteratedDeriv_ten_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 10
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      ((-completedNativeXiCosineMoment 5 : ℝ) : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  have hsecond : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).ofReal_comp.deriv
  have hthird : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).ofReal_comp.deriv
  have hfourth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformThird t).ofReal_comp.deriv
  have hfifth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFourth t).ofReal_comp.deriv
  have hsixth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFifth t).ofReal_comp.deriv
  have hseventh : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSeventh t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSixth t).ofReal_comp.deriv
  have heighth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSeventh t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformEighth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSeventh t).ofReal_comp.deriv
  have hninth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformEighth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformNinth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformEighth t).ofReal_comp.deriv
  rw [show 10 = Nat.succ 9 by norm_num, iteratedDeriv_succ,
    show 9 = Nat.succ 8 by norm_num, iteratedDeriv_succ,
    show 8 = Nat.succ 7 by norm_num, iteratedDeriv_succ,
    show 7 = Nat.succ 6 by norm_num, iteratedDeriv_succ,
    show 6 = Nat.succ 5 by norm_num, iteratedDeriv_succ,
    show 5 = Nat.succ 4 by norm_num, iteratedDeriv_succ,
    show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird, hfourth, hfifth, hsixth,
    hseventh, heighth, hninth]
  rw [(hasDerivAt_completedNativeXiCosineTransformNinth 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformTenth completedNativeXiCosineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The same concrete cosine kernel determines the tenth native derivative. -/
theorem iteratedDeriv_ten_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 10 completedNativeOperatorCharacteristic 0 =
      ((-completedNativeXiCosineMoment 5 : ℝ) : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 10 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 10
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 :=
      (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 10 0).symm
    _ = iteratedDeriv 10
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by rw [haxis]
    _ = ((-completedNativeXiCosineMoment 5 : ℝ) : ℂ) :=
      iteratedDeriv_ten_completedNativeXiCosineTransform_ofReal_zero

/-- The tenth reduced Taylor coefficient is exactly `-μ₁₀ / 10!`. -/
theorem completedNativeRealEvenCharacteristicCoefficient_five_eq_xiCosineMoment :
    completedNativeRealEvenCharacteristicCoefficient 5 =
      -completedNativeXiCosineMoment 5 / 3628800 := by
  unfold completedNativeRealEvenCharacteristicCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  rw [show 2 * 5 = 10 by norm_num,
    iteratedDeriv_ten_completedNativeOperatorCharacteristic_zero]
  norm_num [smul_eq_mul]
  ring

/-! ## Twelfth derivative of the SAME raw cosine source -/

private def completedNativeXiCosineTransformEleventh (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (u ^ 11 * completedNativeXiCosineKernel u) * Real.sin (t * u)

private def completedNativeXiCosineTransformTwelfth (t : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (u ^ 12 * completedNativeXiCosineKernel u) * Real.cos (t * u)

private theorem hasDerivAt_completedNativeXiCosineTransformTenth (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformTenth
      (completedNativeXiCosineTransformEleventh t) t := by
  have hf := (integrableOn_pow_mul_completedNativeXiCosineKernel 10).neg
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (-(u ^ 10 * completedNativeXiCosineKernel u)))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 11).neg.congr
    exact Filter.Eventually.of_forall (fun u ↦ by simp only [Pi.neg_apply]; ring)
  have h := hasDerivAt_integral_mul_cos hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformEleventh
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by simp only [Pi.neg_apply]; ring)

private theorem hasDerivAt_completedNativeXiCosineTransformEleventh (t : ℝ) :
    HasDerivAt completedNativeXiCosineTransformEleventh
      (completedNativeXiCosineTransformTwelfth t) t := by
  have hf := integrableOn_pow_mul_completedNativeXiCosineKernel 11
  have huf : IntegrableOn
      (fun u : ℝ ↦ u * (u ^ 11 * completedNativeXiCosineKernel u))
      (Ioi (0 : ℝ)) := by
    apply (integrableOn_pow_mul_completedNativeXiCosineKernel 12).congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have h := hasDerivAt_integral_mul_sin hf huf t
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · unfold completedNativeXiCosineTransformTwelfth
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)

private theorem iteratedDeriv_twelve_completedNativeXiCosineTransform_ofReal_zero :
    iteratedDeriv 12
        (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 =
      (completedNativeXiCosineMoment 6 : ℂ) := by
  have hfirst : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformReal t).ofReal_comp.deriv
  have hsecond : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFirst t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFirst t).ofReal_comp.deriv
  have hthird : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSecond t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSecond t).ofReal_comp.deriv
  have hfourth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformThird t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformThird t).ofReal_comp.deriv
  have hfifth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFourth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFourth t).ofReal_comp.deriv
  have hsixth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformFifth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformFifth t).ofReal_comp.deriv
  have hseventh : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSixth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformSeventh t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSixth t).ofReal_comp.deriv
  have heighth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformSeventh t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformEighth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformSeventh t).ofReal_comp.deriv
  have hninth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformEighth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformNinth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformEighth t).ofReal_comp.deriv
  have htenth : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformNinth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformTenth t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformNinth t).ofReal_comp.deriv
  have heleventh : deriv
      (fun t : ℝ ↦ (completedNativeXiCosineTransformTenth t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformEleventh t : ℂ) := by
    funext t
    exact (hasDerivAt_completedNativeXiCosineTransformTenth t).ofReal_comp.deriv
  rw [show 12 = Nat.succ 11 by norm_num, iteratedDeriv_succ,
    show 11 = Nat.succ 10 by norm_num, iteratedDeriv_succ,
    show 10 = Nat.succ 9 by norm_num, iteratedDeriv_succ,
    show 9 = Nat.succ 8 by norm_num, iteratedDeriv_succ,
    show 8 = Nat.succ 7 by norm_num, iteratedDeriv_succ,
    show 7 = Nat.succ 6 by norm_num, iteratedDeriv_succ,
    show 6 = Nat.succ 5 by norm_num, iteratedDeriv_succ,
    show 5 = Nat.succ 4 by norm_num, iteratedDeriv_succ,
    show 4 = Nat.succ 3 by norm_num, iteratedDeriv_succ,
    show 3 = Nat.succ 2 by norm_num, iteratedDeriv_succ,
    show 2 = Nat.succ 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst, hsecond, hthird, hfourth, hfifth, hsixth,
    hseventh, heighth, hninth, htenth, heleventh]
  rw [(hasDerivAt_completedNativeXiCosineTransformEleventh 0).ofReal_comp.deriv]
  congr 1
  unfold completedNativeXiCosineTransformTwelfth completedNativeXiCosineMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by simp)

/-- The same concrete cosine kernel determines the twelfth native derivative. -/
theorem iteratedDeriv_twelve_completedNativeOperatorCharacteristic_zero :
    iteratedDeriv 12 completedNativeOperatorCharacteristic 0 =
      (completedNativeXiCosineMoment 6 : ℂ) := by
  have haxis :
      (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) =
        fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ) := by
    funext t
    simpa [completedNativeXiCosineTransformReal] using
      XiThetaCosine.completedNative_eq_xiCosineKernel t
  calc
    iteratedDeriv 12 completedNativeOperatorCharacteristic (0 : ℂ) =
        iteratedDeriv 12
          (fun t : ℝ ↦ completedNativeOperatorCharacteristic (t : ℂ)) 0 :=
      (iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 12 0).symm
    _ = iteratedDeriv 12
          (fun t : ℝ ↦ (completedNativeXiCosineTransformReal t : ℂ)) 0 := by rw [haxis]
    _ = (completedNativeXiCosineMoment 6 : ℂ) :=
      iteratedDeriv_twelve_completedNativeXiCosineTransform_ofReal_zero


end

end CarrySelfAdjointOperator
