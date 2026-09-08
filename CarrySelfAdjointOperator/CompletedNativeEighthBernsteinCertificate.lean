import CarrySelfAdjointOperator.CompletedNativeThetaRefinedTail
import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

noncomputable section
set_option autoImplicit false

def xiEighthMomentNumerator (a b c d e : ℝ) : ℝ :=
  10 * a ^ 2 * c * e - 21 * a ^ 2 * d ^ 2 - 30 * a * b ^ 2 * e +
    350 * a * b * c * d - 350 * a * c ^ 3 - 420 * b ^ 3 * d + 525 * b ^ 2 * c ^ 2

private theorem mul3_le_of_nonneg {x X y Y z Z : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ X)
    (hy0 : 0 ≤ y) (hy : y ≤ Y) (hY0 : 0 ≤ Y)
    (hz : z ≤ Z) (hZ0 : 0 ≤ Z) :
    x * y * z ≤ X * Y * Z := by
  have h1 : 0 ≤ (X - x) * Y * Z :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) hY0) hZ0
  have h2 : 0 ≤ x * (Y - y) * Z :=
    mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hy)) hZ0
  have h3 : 0 ≤ x * y * (Z - z) :=
    mul_nonneg (mul_nonneg hx0 hy0) (sub_nonneg.mpr hz)
  calc
    x * y * z ≤ x * y * z + (X - x) * Y * Z + x * (Y - y) * Z + x * y * (Z - z) := by
      linarith
    _ = X * Y * Z := by ring

private theorem xiEighthMoment_numerator_q0_nonpos (a b c d e : ℝ)
    (ha0 : (7767507 / 15625000 : ℝ) ≤ a) (ha1 : a ≤ (19884837 / 40000000 : ℝ))
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (hc1 : c ≤ (740861 / 250000000 : ℝ))
    (hd0 : (299619 / 500000000 : ℝ) ≤ d) (hd1 : d ≤ (600193 / 1000000000 : ℝ))
    (he0 : (10059 / 62500000 : ℝ) ≤ e) (he1 : e ≤ (161051 / 1000000000 : ℝ)) :
    10 * (a + (19884837 / 40000000 : ℝ)) * c * e -
        21 * (a + (19884837 / 40000000 : ℝ)) * d ^ 2 -
        30 * b ^ 2 * e + 350 * b * c * d - 350 * c ^ 3 ≤ 0 := by
  have ha0' : 0 ≤ a := by nlinarith
  have hb0' : 0 ≤ b := by nlinarith
  have hc0' : 0 ≤ c := by nlinarith
  have hd0' : 0 ≤ d := by nlinarith
  have he0' : 0 ≤ e := by nlinarith
  have hsum0 : 0 ≤ a + (19884837 / 40000000 : ℝ) := by positivity
  have hsumlo : (7767507 / 15625000 : ℝ) + (19884837 / 40000000 : ℝ) ≤
      a + (19884837 / 40000000 : ℝ) := by linarith
  have hsumhi : a + (19884837 / 40000000 : ℝ) ≤
      (19884837 / 40000000 : ℝ) + (19884837 / 40000000 : ℝ) := by linarith
  have hp1 := mul3_le_of_nonneg hsum0 hsumhi
    hc0' hc1 (by norm_num : 0 ≤ (740861 / 250000000 : ℝ))
    he1 (by norm_num : 0 ≤ (161051 / 1000000000 : ℝ))
  have hp2 := mul3_le_of_nonneg hb0' hb1
    hc0' hc1 (by norm_num : 0 ≤ (740861 / 250000000 : ℝ))
    hd1 (by norm_num : 0 ≤ (600193 / 1000000000 : ℝ))
  have hn1 := mul3_le_of_nonneg (by norm_num : 0 ≤ (7767507 / 15625000 : ℝ) + (19884837 / 40000000 : ℝ)) hsumlo
    (by norm_num : 0 ≤ (299619 / 500000000 : ℝ)) hd0 hd0'
    hd0 hd0'
  have hn2 := mul3_le_of_nonneg (by norm_num : 0 ≤ (574269 / 25000000 : ℝ)) hb0
    (by norm_num : 0 ≤ (574269 / 25000000 : ℝ)) hb0 hb0'
    he0 he0'
  have hn3 := mul3_le_of_nonneg (by norm_num : 0 ≤ (2962661 / 1000000000 : ℝ)) hc0
    (by norm_num : 0 ≤ (2962661 / 1000000000 : ℝ)) hc0 hc0'
    hc0 hc0'
  have hnum :
      10 * ((19884837 / 40000000 : ℝ) + (19884837 / 40000000 : ℝ)) *
          (740861 / 250000000 : ℝ) * (161051 / 1000000000 : ℝ) +
        350 * (22974587 / 1000000000 : ℝ) * (740861 / 250000000 : ℝ) *
          (600193 / 1000000000 : ℝ) ≤
      21 * ((7767507 / 15625000 : ℝ) + (19884837 / 40000000 : ℝ)) *
          (299619 / 500000000 : ℝ) * (299619 / 500000000 : ℝ) +
        30 * (574269 / 25000000 : ℝ) * (574269 / 25000000 : ℝ) *
          (10059 / 62500000 : ℝ) +
        350 * (2962661 / 1000000000 : ℝ) * (2962661 / 1000000000 : ℝ) *
          (2962661 / 1000000000 : ℝ) := by norm_num
  nlinarith

private theorem xiEighthMoment_numerator_q2_nonneg (b c d e : ℝ)
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (_hc1 : c ≤ (740861 / 250000000 : ℝ))
    (hd0 : (299619 / 500000000 : ℝ) ≤ d) (hd1 : d ≤ (600193 / 1000000000 : ℝ))
    (he0 : (10059 / 62500000 : ℝ) ≤ e) (he1 : e ≤ (161051 / 1000000000 : ℝ)) :
    0 ≤ -30 * (19884837 / 40000000 : ℝ) *
        (b + (574269 / 25000000 : ℝ)) * e +
      350 * (19884837 / 40000000 : ℝ) * c * d -
      420 * (b ^ 2 + b * (574269 / 25000000 : ℝ) +
        (574269 / 25000000 : ℝ) ^ 2) * d +
      525 * (b + (574269 / 25000000 : ℝ)) * c ^ 2 := by
  have hb0' : 0 ≤ b := by nlinarith
  have hc0' : 0 ≤ c := by nlinarith
  have hd0' : 0 ≤ d := by nlinarith
  have he0' : 0 ≤ e := by nlinarith
  have hsum0 : 0 ≤ b + (574269 / 25000000 : ℝ) := by positivity
  have hsumlo : (574269 / 25000000 : ℝ) + (574269 / 25000000 : ℝ) ≤
      b + (574269 / 25000000 : ℝ) := by linarith
  have hsumhi : b + (574269 / 25000000 : ℝ) ≤
      (22974587 / 1000000000 : ℝ) + (574269 / 25000000 : ℝ) := by linarith
  have hpoly0 : 0 ≤ b ^ 2 + b * (574269 / 25000000 : ℝ) +
      (574269 / 25000000 : ℝ) ^ 2 := by positivity
  have hpolyhi : b ^ 2 + b * (574269 / 25000000 : ℝ) +
      (574269 / 25000000 : ℝ) ^ 2 ≤
      (22974587 / 1000000000 : ℝ) ^ 2 +
        (22974587 / 1000000000 : ℝ) * (574269 / 25000000 : ℝ) +
        (574269 / 25000000 : ℝ) ^ 2 := by
    have hfac : 0 ≤ ((22974587 / 1000000000 : ℝ) - b) *
        ((22974587 / 1000000000 : ℝ) + b + (574269 / 25000000 : ℝ)) := by positivity
    nlinarith
  have hp1 := mul3_le_of_nonneg (by norm_num : 0 ≤ (19884837 / 40000000 : ℝ)) (by rfl)
    (by norm_num : 0 ≤ (2962661 / 1000000000 : ℝ)) hc0 hc0'
    hd0 hd0'
  have hp2 := mul3_le_of_nonneg (by norm_num : 0 ≤ (574269 / 25000000 : ℝ) + (574269 / 25000000 : ℝ)) hsumlo
    (by norm_num : 0 ≤ (2962661 / 1000000000 : ℝ)) hc0 hc0'
    hc0 hc0'
  have hn1 := mul3_le_of_nonneg (by norm_num : 0 ≤ (19884837 / 40000000 : ℝ)) (by rfl)
    hsum0 hsumhi (by norm_num : 0 ≤ (22974587 / 1000000000 : ℝ) + (574269 / 25000000 : ℝ))
    he1 (by norm_num : 0 ≤ (161051 / 1000000000 : ℝ))
  have hn2 : (b ^ 2 + b * (574269 / 25000000 : ℝ) +
        (574269 / 25000000 : ℝ) ^ 2) * d ≤
      ((22974587 / 1000000000 : ℝ) ^ 2 +
        (22974587 / 1000000000 : ℝ) * (574269 / 25000000 : ℝ) +
        (574269 / 25000000 : ℝ) ^ 2) * (600193 / 1000000000 : ℝ) := by
    exact mul_le_mul hpolyhi hd1 hd0' (by positivity)
  have hnum :
      30 * (19884837 / 40000000 : ℝ) *
          ((22974587 / 1000000000 : ℝ) + (574269 / 25000000 : ℝ)) *
          (161051 / 1000000000 : ℝ) +
        420 * ((22974587 / 1000000000 : ℝ) ^ 2 +
          (22974587 / 1000000000 : ℝ) * (574269 / 25000000 : ℝ) +
          (574269 / 25000000 : ℝ) ^ 2) * (600193 / 1000000000 : ℝ) ≤
      350 * (19884837 / 40000000 : ℝ) * (2962661 / 1000000000 : ℝ) *
          (299619 / 500000000 : ℝ) +
        525 * ((574269 / 25000000 : ℝ) + (574269 / 25000000 : ℝ)) *
          (2962661 / 1000000000 : ℝ) * (2962661 / 1000000000 : ℝ) := by norm_num
  nlinarith

private theorem xiEighthMoment_numerator_q4_nonpos (a b c d e : ℝ)
    (ha0 : (7767507 / 15625000 : ℝ) ≤ a) (ha1 : a ≤ (19884837 / 40000000 : ℝ))
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (hc1 : c ≤ (740861 / 250000000 : ℝ))
    (hd0 : (299619 / 500000000 : ℝ) ≤ d) (hd1 : d ≤ (600193 / 1000000000 : ℝ))
    (he0 : (10059 / 62500000 : ℝ) ≤ e) (he1 : e ≤ (161051 / 1000000000 : ℝ)) :
    10 * a ^ 2 * e + 350 * a * b * d -
      350 * a * (c ^ 2 + c * (740861 / 250000000 : ℝ) +
        (740861 / 250000000 : ℝ) ^ 2) +
      525 * b ^ 2 * (c + (740861 / 250000000 : ℝ)) ≤ 0 := by
  have ha0' : 0 ≤ a := by nlinarith
  have hb0' : 0 ≤ b := by nlinarith
  have hc0' : 0 ≤ c := by nlinarith
  have hd0' : 0 ≤ d := by nlinarith
  have he0' : 0 ≤ e := by nlinarith
  have hpolylo : (2962661 / 1000000000 : ℝ) ^ 2 +
      (2962661 / 1000000000 : ℝ) * (740861 / 250000000 : ℝ) +
      (740861 / 250000000 : ℝ) ^ 2 ≤
      c ^ 2 + c * (740861 / 250000000 : ℝ) +
        (740861 / 250000000 : ℝ) ^ 2 := by
    have hfac : 0 ≤ (c - (2962661 / 1000000000 : ℝ)) *
        (c + (2962661 / 1000000000 : ℝ) + (740861 / 250000000 : ℝ)) := by positivity
    nlinarith
  have hp1 := mul3_le_of_nonneg ha0' ha1
    ha0' ha1 (by norm_num : 0 ≤ (19884837 / 40000000 : ℝ))
    he1 (by norm_num : 0 ≤ (161051 / 1000000000 : ℝ))
  have hp2 := mul3_le_of_nonneg ha0' ha1
    hb0' hb1 (by norm_num : 0 ≤ (22974587 / 1000000000 : ℝ))
    hd1 (by norm_num : 0 ≤ (600193 / 1000000000 : ℝ))
  have hsum0 : 0 ≤ c + (740861 / 250000000 : ℝ) := by positivity
  have hsumhi : c + (740861 / 250000000 : ℝ) ≤
      (740861 / 250000000 : ℝ) + (740861 / 250000000 : ℝ) := by linarith
  have hp3 := mul3_le_of_nonneg hb0' hb1
    hb0' hb1 (by norm_num : 0 ≤ (22974587 / 1000000000 : ℝ))
    hsumhi (by norm_num : 0 ≤ (740861 / 250000000 : ℝ) + (740861 / 250000000 : ℝ))
  have hn : (7767507 / 15625000 : ℝ) *
      ((2962661 / 1000000000 : ℝ) ^ 2 +
        (2962661 / 1000000000 : ℝ) * (740861 / 250000000 : ℝ) +
        (740861 / 250000000 : ℝ) ^ 2) ≤
      a * (c ^ 2 + c * (740861 / 250000000 : ℝ) +
        (740861 / 250000000 : ℝ) ^ 2) := by
    exact mul_le_mul ha0 hpolylo (by positivity) ha0'
  have hnum :
      10 * (19884837 / 40000000 : ℝ) * (19884837 / 40000000 : ℝ) *
          (161051 / 1000000000 : ℝ) +
        350 * (19884837 / 40000000 : ℝ) * (22974587 / 1000000000 : ℝ) *
          (600193 / 1000000000 : ℝ) +
        525 * (22974587 / 1000000000 : ℝ) * (22974587 / 1000000000 : ℝ) *
          ((740861 / 250000000 : ℝ) + (740861 / 250000000 : ℝ)) ≤
      350 * (7767507 / 15625000 : ℝ) *
          ((2962661 / 1000000000 : ℝ) ^ 2 +
            (2962661 / 1000000000 : ℝ) * (740861 / 250000000 : ℝ) +
            (740861 / 250000000 : ℝ) ^ 2) := by norm_num
  nlinarith

private theorem xiEighthMoment_numerator_q6_nonneg (a b c d : ℝ)
    (ha0 : (7767507 / 15625000 : ℝ) ≤ a) (ha1 : a ≤ (19884837 / 40000000 : ℝ))
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (_hc1 : c ≤ (740861 / 250000000 : ℝ))
    (hd0 : (299619 / 500000000 : ℝ) ≤ d) (hd1 : d ≤ (600193 / 1000000000 : ℝ)) :
    0 ≤ -21 * a ^ 2 * (d + (299619 / 500000000 : ℝ)) +
      350 * a * b * c - 420 * b ^ 3 := by
  have ha0' : 0 ≤ a := by nlinarith
  have hb0' : 0 ≤ b := by nlinarith
  have hc0' : 0 ≤ c := by nlinarith
  have hd0' : 0 ≤ d := by nlinarith
  have hsum0 : 0 ≤ d + (299619 / 500000000 : ℝ) := by positivity
  have hsumhi : d + (299619 / 500000000 : ℝ) ≤
      (600193 / 1000000000 : ℝ) + (299619 / 500000000 : ℝ) := by linarith
  have hp := mul3_le_of_nonneg (by norm_num : 0 ≤ (7767507 / 15625000 : ℝ)) ha0
    (by norm_num : 0 ≤ (574269 / 25000000 : ℝ)) hb0 hb0'
    hc0 hc0'
  have hn1 := mul3_le_of_nonneg ha0' ha1
    ha0' ha1 (by norm_num : 0 ≤ (19884837 / 40000000 : ℝ))
    hsumhi (by norm_num : 0 ≤ (600193 / 1000000000 : ℝ) + (299619 / 500000000 : ℝ))
  have hn2 := mul3_le_of_nonneg hb0' hb1
    hb0' hb1 (by norm_num : 0 ≤ (22974587 / 1000000000 : ℝ))
    hb1 (by norm_num : 0 ≤ (22974587 / 1000000000 : ℝ))
  have hnum :
      21 * (19884837 / 40000000 : ℝ) * (19884837 / 40000000 : ℝ) *
          ((600193 / 1000000000 : ℝ) + (299619 / 500000000 : ℝ)) +
        420 * (22974587 / 1000000000 : ℝ) * (22974587 / 1000000000 : ℝ) *
          (22974587 / 1000000000 : ℝ) ≤
      350 * (7767507 / 15625000 : ℝ) * (574269 / 25000000 : ℝ) *
          (2962661 / 1000000000 : ℝ) := by norm_num
  nlinarith

private theorem xiEighthMoment_numerator_q8_nonpos (a b c : ℝ)
    (ha0 : (7767507 / 15625000 : ℝ) ≤ a) (ha1 : a ≤ (19884837 / 40000000 : ℝ))
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (_hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (hc1 : c ≤ (740861 / 250000000 : ℝ)) :
    10 * a ^ 2 * c - 30 * a * b ^ 2 ≤ 0 := by
  have ha0' : 0 ≤ a := by nlinarith
  have hb0' : 0 ≤ b := by nlinarith
  have hc0' : 0 ≤ c := by nlinarith
  have hp := mul3_le_of_nonneg ha0' ha1
    ha0' ha1 (by norm_num : 0 ≤ (19884837 / 40000000 : ℝ))
    hc1 (by norm_num : 0 ≤ (740861 / 250000000 : ℝ))
  have hn := mul3_le_of_nonneg (by norm_num : 0 ≤ (7767507 / 15625000 : ℝ)) ha0
    (by norm_num : 0 ≤ (574269 / 25000000 : ℝ)) hb0 hb0'
    hb0 hb0'
  have hnum :
      10 * (19884837 / 40000000 : ℝ) * (19884837 / 40000000 : ℝ) *
          (740861 / 250000000 : ℝ) ≤
      30 * (7767507 / 15625000 : ℝ) * (574269 / 25000000 : ℝ) *
          (574269 / 25000000 : ℝ) := by norm_num
  nlinarith

theorem xiEighthMoment_numerator_lower_bound_of_refined_box (a b c d e : ℝ)
    (ha0 : (7767507 / 15625000 : ℝ) ≤ a) (ha1 : a ≤ (19884837 / 40000000 : ℝ))
    (hb0 : (574269 / 25000000 : ℝ) ≤ b) (hb1 : b ≤ (22974587 / 1000000000 : ℝ))
    (hc0 : (2962661 / 1000000000 : ℝ) ≤ c) (hc1 : c ≤ (740861 / 250000000 : ℝ))
    (hd0 : (299619 / 500000000 : ℝ) ≤ d) (hd1 : d ≤ (600193 / 1000000000 : ℝ))
    (he0 : (10059 / 62500000 : ℝ) ≤ e) (he1 : e ≤ (161051 / 1000000000 : ℝ)) :
    (1 / 10000000000 : ℝ) ≤ xiEighthMomentNumerator a b c d e := by
  have hqa := xiEighthMoment_numerator_q0_nonpos a b c d e ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 he0 he1
  have hA : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) b c d e ≤ xiEighthMomentNumerator a b c d e := by
    have hfac : xiEighthMomentNumerator a b c d e - xiEighthMomentNumerator (19884837 / 40000000 : ℝ) b c d e =
        (a - (19884837 / 40000000 : ℝ)) *
          (10 * (a + (19884837 / 40000000 : ℝ)) * c * e -
            21 * (a + (19884837 / 40000000 : ℝ)) * d ^ 2 -
            30 * b ^ 2 * e + 350 * b * c * d - 350 * c ^ 3) := by
      unfold xiEighthMomentNumerator
      ring
    have hprod : 0 ≤ (a - (19884837 / 40000000 : ℝ)) *
        (10 * (a + (19884837 / 40000000 : ℝ)) * c * e -
          21 * (a + (19884837 / 40000000 : ℝ)) * d ^ 2 -
          30 * b ^ 2 * e + 350 * b * c * d - 350 * c ^ 3) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hqa
    linarith
  have hqb := xiEighthMoment_numerator_q2_nonneg b c d e hb0 hb1 hc0 hc1 hd0 hd1 he0 he1
  have hB : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ) c d e ≤
      xiEighthMomentNumerator (19884837 / 40000000 : ℝ) b c d e := by
    have hfac : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) b c d e -
        xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ) c d e =
        (b - (574269 / 25000000 : ℝ)) *
          (-30 * (19884837 / 40000000 : ℝ) *
              (b + (574269 / 25000000 : ℝ)) * e +
            350 * (19884837 / 40000000 : ℝ) * c * d -
            420 * (b ^ 2 + b * (574269 / 25000000 : ℝ) +
              (574269 / 25000000 : ℝ) ^ 2) * d +
            525 * (b + (574269 / 25000000 : ℝ)) * c ^ 2) := by
      unfold xiEighthMomentNumerator
      ring
    have hprod : 0 ≤ (b - (574269 / 25000000 : ℝ)) *
        (-30 * (19884837 / 40000000 : ℝ) *
            (b + (574269 / 25000000 : ℝ)) * e +
          350 * (19884837 / 40000000 : ℝ) * c * d -
          420 * (b ^ 2 + b * (574269 / 25000000 : ℝ) +
            (574269 / 25000000 : ℝ) ^ 2) * d +
          525 * (b + (574269 / 25000000 : ℝ)) * c ^ 2) :=
      mul_nonneg (by linarith) hqb
    linarith
  have hqc := xiEighthMoment_numerator_q4_nonpos (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ) c d e
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc0 hc1 hd0 hd1 he0 he1
  have hC : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) d e ≤
      xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ) c d e := by
    have hfac : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ) c d e -
        xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
          (740861 / 250000000 : ℝ) d e =
        (c - (740861 / 250000000 : ℝ)) *
          (10 * (19884837 / 40000000 : ℝ) ^ 2 * e +
            350 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) * d -
            350 * (19884837 / 40000000 : ℝ) *
              (c ^ 2 + c * (740861 / 250000000 : ℝ) +
                (740861 / 250000000 : ℝ) ^ 2) +
            525 * (574269 / 25000000 : ℝ) ^ 2 *
              (c + (740861 / 250000000 : ℝ))) := by
      unfold xiEighthMomentNumerator
      ring
    have hprod : 0 ≤ (c - (740861 / 250000000 : ℝ)) *
        (10 * (19884837 / 40000000 : ℝ) ^ 2 * e +
          350 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) * d -
          350 * (19884837 / 40000000 : ℝ) *
            (c ^ 2 + c * (740861 / 250000000 : ℝ) +
              (740861 / 250000000 : ℝ) ^ 2) +
          525 * (574269 / 25000000 : ℝ) ^ 2 *
            (c + (740861 / 250000000 : ℝ))) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hqc
    linarith
  have hqd := xiEighthMoment_numerator_q6_nonneg (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
    (740861 / 250000000 : ℝ) d
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd0 hd1
  have hD : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ) e ≤
      xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) d e := by
    have hfac : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
          (740861 / 250000000 : ℝ) d e -
        xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
          (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ) e =
        (d - (299619 / 500000000 : ℝ)) *
          (-21 * (19884837 / 40000000 : ℝ) ^ 2 *
              (d + (299619 / 500000000 : ℝ)) +
            350 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) *
              (740861 / 250000000 : ℝ) -
            420 * (574269 / 25000000 : ℝ) ^ 3) := by
      unfold xiEighthMomentNumerator
      ring
    have hprod : 0 ≤ (d - (299619 / 500000000 : ℝ)) *
        (-21 * (19884837 / 40000000 : ℝ) ^ 2 *
            (d + (299619 / 500000000 : ℝ)) +
          350 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) *
            (740861 / 250000000 : ℝ) -
          420 * (574269 / 25000000 : ℝ) ^ 3) := mul_nonneg (by linarith) hqd
    linarith
  have hqe := xiEighthMoment_numerator_q8_nonpos (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
    (740861 / 250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hE : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ)
        (161051 / 1000000000 : ℝ) ≤
      xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ) e := by
    have hfac : xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
          (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ) e -
        xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
          (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ)
          (161051 / 1000000000 : ℝ) =
        (e - (161051 / 1000000000 : ℝ)) *
          (10 * (19884837 / 40000000 : ℝ) ^ 2 * (740861 / 250000000 : ℝ) -
            30 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) ^ 2) := by
      unfold xiEighthMomentNumerator
      ring
    have hprod : 0 ≤ (e - (161051 / 1000000000 : ℝ)) *
        (10 * (19884837 / 40000000 : ℝ) ^ 2 * (740861 / 250000000 : ℝ) -
          30 * (19884837 / 40000000 : ℝ) * (574269 / 25000000 : ℝ) ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hqe
    linarith
  have hvertex : (1 / 10000000000 : ℝ) ≤
      xiEighthMomentNumerator (19884837 / 40000000 : ℝ) (574269 / 25000000 : ℝ)
        (740861 / 250000000 : ℝ) (299619 / 500000000 : ℝ)
        (161051 / 1000000000 : ℝ) := by norm_num [xiEighthMomentNumerator]
  linarith

end
end CarrySelfAdjointOperator
