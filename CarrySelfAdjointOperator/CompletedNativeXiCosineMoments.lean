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

end

end CarrySelfAdjointOperator
