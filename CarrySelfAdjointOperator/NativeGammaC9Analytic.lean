import CarrySelfAdjointOperator.NativeGammaC9Exterior
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ENNReal MeasureTheory
open Set MeasureTheory NativeCarrySpectralWeyl.Infinite
noncomputable section
set_option autoImplicit false

theorem nativeCauchyReal_integrableOn (z : ℂ) (hz : z.im ≠ 0) (a b : ℝ) :
    IntegrableOn (logarithmicResolventRealCoefficient z) (Ioc a b) volume := by
  simpa only [IntegrableOn, RCLike.re_to_complex, nativeCauchyKernel_real] using
    (nativeCauchyKernel_integrableOn z hz a b).re

theorem nativeCauchyReal_strictMono (z : ℂ)
    (h : 1 + Real.log 6 + |z.im| < z.re) :
    StrictMonoOn (logarithmicResolventRealCoefficient z) (Ioc 0 6) := by
  intro x hx y hy hxy
  have hlog : Real.log x < Real.log y := Real.log_lt_log hx.1 hxy
  have hylog : Real.log y ≤ Real.log 6 := Real.log_le_log hy.1 hy.2
  have hAy : |z.im| < z.re - (1 + Real.log y) := by linarith
  have habs : 0 ≤ |z.im| := abs_nonneg _
  have hAy0 : 0 < z.re - (1 + Real.log y) := by linarith
  have hAx0 : 0 < z.re - (1 + Real.log x) := by linarith
  have hsq : z.im^2 < (z.re - (1 + Real.log y))^2 := by
    nlinarith [sq_abs z.im]
  have hprod : z.im^2 <
      (z.re - (1 + Real.log x)) * (z.re - (1 + Real.log y)) := by
    nlinarith
  unfold logarithmicResolventRealCoefficient logarithmicResolventDenominator logarithmicCoordinate
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have hp : 0 < ((z.re - (1 + Real.log x)) - (z.re - (1 + Real.log y))) *
      ((z.re - (1 + Real.log x)) * (z.re - (1 + Real.log y)) - z.im^2) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem nativeCauchyIntervalIntegral_real (z : ℂ) (hz : z.im ≠ 0) (l : ℝ) :
    (nativeCauchyIntervalIntegral l z).re =
      ∫ x in Ioc 0 l, logarithmicResolventRealCoefficient z x := by
  unfold nativeCauchyIntervalIntegral
  symm
  simpa only [RCLike.re_to_complex, nativeCauchyKernel_real] using
    (integral_re (𝕜 := ℂ) (nativeCauchyKernel_integrableOn z hz 0 l))

theorem nativeCauchyReal_integral_split (z : ℂ) (hz : z.im ≠ 0)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ x in Ioc a c, logarithmicResolventRealCoefficient z x) =
      (∫ x in Ioc a b, logarithmicResolventRealCoefficient z x) +
      (∫ x in Ioc b c, logarithmicResolventRealCoefficient z x) := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (nativeCauchyReal_integrableOn z hz a b) (nativeCauchyReal_integrableOn z hz b c)

theorem nativeC9Beta_real_centered (z : ℂ) (hz : z.im ≠ 0) :
    (nativeC9Beta z).re =
      (96/139 : ℝ) * (∫ x in Ioc 0 3,
        logarithmicResolventRealCoefficient z 3 - logarithmicResolventRealCoefficient z x) +
      (128/139 : ℝ) * (∫ x in Ioc 3 4,
        logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3) +
      (80/139 : ℝ) * (∫ x in Ioc 4 6,
        logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3) := by
  have h03 := nativeCauchyReal_integrableOn z hz 0 3
  have h34 := nativeCauchyReal_integrableOn z hz 3 4
  have h46 := nativeCauchyReal_integrableOn z hz 4 6
  have hc03 : IntegrableOn (fun _ : ℝ => logarithmicResolventRealCoefficient z 3) (Ioc 0 3) volume :=
    integrableOn_const (by simp)
  have hc34 : IntegrableOn (fun _ : ℝ => logarithmicResolventRealCoefficient z 3) (Ioc 3 4) volume :=
    integrableOn_const (by simp)
  have hc46 : IntegrableOn (fun _ : ℝ => logarithmicResolventRealCoefficient z 3) (Ioc 4 6) volume :=
    integrableOn_const (by simp)
  simp only [integral_sub hc03 h03, integral_sub h34 hc34, integral_sub h46 hc46,
    setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]
  norm_num
  unfold nativeC9Beta
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re,
    Complex.neg_re, Complex.neg_im]
  norm_num
  rw [nativeCauchyIntervalIntegral_real z hz, nativeCauchyIntervalIntegral_real z hz,
    nativeCauchyIntervalIntegral_real z hz,
    nativeCauchyReal_integral_split z hz 0 4 6 (by norm_num) (by norm_num),
    nativeCauchyReal_integral_split z hz 0 3 4 (by norm_num) (by norm_num)]
  ring

theorem nativeC9Beta_real_pos (z : ℂ) (hz : z.im ≠ 0)
    (h : 1 + Real.log 6 + |z.im| < z.re) : 0 < (nativeC9Beta z).re := by
  have hm := nativeCauchyReal_strictMono z h
  have h3 : (3 : ℝ) ∈ Ioc 0 6 := by norm_num
  have hc (a b : ℝ) : IntegrableOn (fun _ : ℝ => logarithmicResolventRealCoefficient z 3)
      (Ioc a b) volume := integrableOn_const (by simp)
  have hn03 : 0 ≤ ∫ x in Ioc 0 3,
      logarithmicResolventRealCoefficient z 3 - logarithmicResolventRealCoefficient z x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact sub_nonneg.mpr (hm.monotoneOn ⟨hx.1, by linarith [hx.2]⟩ h3 hx.2)
  have hn46 : 0 ≤ ∫ x in Ioc 4 6,
      logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact sub_nonneg.mpr (hm.monotoneOn h3 ⟨by linarith [hx.1], hx.2⟩ (by linarith [hx.1]))
  have hp34 : 0 < ∫ x in Ioc 3 4,
      logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3 := by
    have hi := (nativeCauchyReal_integrableOn z hz 3 4).sub (hc 3 4)
    have hp : ∀ x ∈ Ioc (3 : ℝ) 4,
        0 < logarithmicResolventRealCoefficient z x - logarithmicResolventRealCoefficient z 3 := by
      intro x hx
      exact sub_pos.mpr (hm h3 ⟨by linarith [hx.1], by linarith [hx.2]⟩ hx.1)
    apply (setIntegral_pos_iff_support_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact (hp x hx).le) hi).mpr
    have hs : Function.support (fun x => logarithmicResolventRealCoefficient z x -
        logarithmicResolventRealCoefficient z 3) ∩ Ioc 3 4 = Ioc 3 4 := by
      apply inter_eq_right.mpr
      intro x hx
      exact ne_of_gt (hp x hx)
    change 0 < volume (Function.support (fun x => logarithmicResolventRealCoefficient z x -
      logarithmicResolventRealCoefficient z 3) ∩ Ioc 3 4)
    rw [hs, Real.volume_Ioc]
    norm_num
  rw [nativeC9Beta_real_centered z hz]
  nlinarith

def nativeC9WitnessPoint : ℂ := 4 + Complex.I / 8

theorem log_six_lt_two : Real.log 6 < 2 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem nativeC9WitnessPoint_admissible :
    nativeC9WitnessPoint.im ≠ 0 ∧
      1 + Real.log 6 + |nativeC9WitnessPoint.im| < nativeC9WitnessPoint.re := by
  norm_num [nativeC9WitnessPoint, Complex.ext_iff]
  linarith [log_six_lt_two]

theorem nativeC9Beta_witness_ne_zero : nativeC9Beta nativeC9WitnessPoint ≠ 0 := by
  have hp := nativeC9Beta_real_pos _ nativeC9WitnessPoint_admissible.1
    nativeC9WitnessPoint_admissible.2
  intro he
  simp [he] at hp

end
end CarrySelfAdjointOperator.GammaMaterialSewing
