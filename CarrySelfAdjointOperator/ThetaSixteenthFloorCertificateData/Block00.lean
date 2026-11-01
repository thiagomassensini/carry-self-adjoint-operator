import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_00
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_000 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((0 : ℝ)/512)^2 *
        (∫ x in (0/1:ℝ)..(1/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_000).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((0 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((0 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((0 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((0 : ℝ)/512)^2 *
        (∫ x in (0/1:ℝ)..(1/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_001 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((1 : ℝ)/512)^2 *
        (∫ x in (1/512:ℝ)..(1/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_001).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((1 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((1 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((1 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((1 : ℝ)/512)^2 *
        (∫ x in (1/512:ℝ)..(1/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_002 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((2 : ℝ)/512)^2 *
        (∫ x in (1/256:ℝ)..(3/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_002).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((2 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((2 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((2 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((2 : ℝ)/512)^2 *
        (∫ x in (1/256:ℝ)..(3/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_003 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((3 : ℝ)/512)^2 *
        (∫ x in (3/512:ℝ)..(1/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_003).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((3 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((3 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((3 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((3 : ℝ)/512)^2 *
        (∫ x in (3/512:ℝ)..(1/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_004 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((4 : ℝ)/512)^2 *
        (∫ x in (1/128:ℝ)..(5/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_004).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((4 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((4 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((4 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((4 : ℝ)/512)^2 *
        (∫ x in (1/128:ℝ)..(5/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_005 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((5 : ℝ)/512)^2 *
        (∫ x in (5/512:ℝ)..(3/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_005).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((5 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((5 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((5 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((5 : ℝ)/512)^2 *
        (∫ x in (5/512:ℝ)..(3/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_006 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((6 : ℝ)/512)^2 *
        (∫ x in (3/256:ℝ)..(7/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_006).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((6 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((6 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((6 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((6 : ℝ)/512)^2 *
        (∫ x in (3/256:ℝ)..(7/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_007 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((7 : ℝ)/512)^2 *
        (∫ x in (7/512:ℝ)..(1/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_007).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((7 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((7 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((7 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((7 : ℝ)/512)^2 *
        (∫ x in (7/512:ℝ)..(1/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_008 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((8 : ℝ)/512)^2 *
        (∫ x in (1/64:ℝ)..(9/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_008).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((8 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((8 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((8 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((8 : ℝ)/512)^2 *
        (∫ x in (1/64:ℝ)..(9/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_009 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((9 : ℝ)/512)^2 *
        (∫ x in (9/512:ℝ)..(5/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_009).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((9 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((9 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((9 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((9 : ℝ)/512)^2 *
        (∫ x in (9/512:ℝ)..(5/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_010 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((10 : ℝ)/512)^2 *
        (∫ x in (5/256:ℝ)..(11/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_010).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((10 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((10 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((10 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((10 : ℝ)/512)^2 *
        (∫ x in (5/256:ℝ)..(11/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_011 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((11 : ℝ)/512)^2 *
        (∫ x in (11/512:ℝ)..(3/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_011).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((11 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((11 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((11 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((11 : ℝ)/512)^2 *
        (∫ x in (11/512:ℝ)..(3/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_012 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((12 : ℝ)/512)^2 *
        (∫ x in (3/128:ℝ)..(13/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_012).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((12 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((12 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((12 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((12 : ℝ)/512)^2 *
        (∫ x in (3/128:ℝ)..(13/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_013 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((13 : ℝ)/512)^2 *
        (∫ x in (13/512:ℝ)..(7/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_013).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((13 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((13 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((13 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((13 : ℝ)/512)^2 *
        (∫ x in (13/512:ℝ)..(7/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_014 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((14 : ℝ)/512)^2 *
        (∫ x in (7/256:ℝ)..(15/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_014).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((14 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((14 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((14 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((14 : ℝ)/512)^2 *
        (∫ x in (7/256:ℝ)..(15/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_015 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((15 : ℝ)/512)^2 *
        (∫ x in (15/512:ℝ)..(1/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_015).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((15 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((15 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((15 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((15 : ℝ)/512)^2 *
        (∫ x in (15/512:ℝ)..(1/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_016 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((16 : ℝ)/512)^2 *
        (∫ x in (1/32:ℝ)..(17/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_016).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((16 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((16 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((16 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((16 : ℝ)/512)^2 *
        (∫ x in (1/32:ℝ)..(17/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_017 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((17 : ℝ)/512)^2 *
        (∫ x in (17/512:ℝ)..(9/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_017).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((17 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((17 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((17 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((17 : ℝ)/512)^2 *
        (∫ x in (17/512:ℝ)..(9/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_018 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((18 : ℝ)/512)^2 *
        (∫ x in (9/256:ℝ)..(19/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_018).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((18 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((18 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((18 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((18 : ℝ)/512)^2 *
        (∫ x in (9/256:ℝ)..(19/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_019 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((19 : ℝ)/512)^2 *
        (∫ x in (19/512:ℝ)..(5/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_019).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((19 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((19 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((19 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((19 : ℝ)/512)^2 *
        (∫ x in (19/512:ℝ)..(5/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_020 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((20 : ℝ)/512)^2 *
        (∫ x in (5/128:ℝ)..(21/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_020).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((20 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((20 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((20 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((20 : ℝ)/512)^2 *
        (∫ x in (5/128:ℝ)..(21/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_021 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((21 : ℝ)/512)^2 *
        (∫ x in (21/512:ℝ)..(11/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_021).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((21 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((21 : ℝ)/512)^2 *
          (0/1 : ℝ) := by
    norm_num
  have ht :
      ((21 : ℝ)/512)^2 *
        (0/1 : ℝ) ≤
      ((21 : ℝ)/512)^2 *
        (∫ x in (21/512:ℝ)..(11/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_022 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((22 : ℝ)/512)^2 *
        (∫ x in (11/256:ℝ)..(23/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_022).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((22 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((22 : ℝ)/512)^2 *
          (1/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((22 : ℝ)/512)^2 *
        (1/100000000000000000000000 : ℝ) ≤
      ((22 : ℝ)/512)^2 *
        (∫ x in (11/256:ℝ)..(23/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_023 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((23 : ℝ)/512)^2 *
        (∫ x in (23/512:ℝ)..(3/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_023).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((23 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((23 : ℝ)/512)^2 *
          (1/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((23 : ℝ)/512)^2 *
        (1/50000000000000000000000 : ℝ) ≤
      ((23 : ℝ)/512)^2 *
        (∫ x in (23/512:ℝ)..(3/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_024 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((24 : ℝ)/512)^2 *
        (∫ x in (3/64:ℝ)..(25/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_024).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((24 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((24 : ℝ)/512)^2 *
          (1/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((24 : ℝ)/512)^2 *
        (1/25000000000000000000000 : ℝ) ≤
      ((24 : ℝ)/512)^2 *
        (∫ x in (3/64:ℝ)..(25/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_025 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((25 : ℝ)/512)^2 *
        (∫ x in (25/512:ℝ)..(13/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_025).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((25 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((25 : ℝ)/512)^2 *
          (7/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((25 : ℝ)/512)^2 *
        (7/100000000000000000000000 : ℝ) ≤
      ((25 : ℝ)/512)^2 *
        (∫ x in (25/512:ℝ)..(13/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_026 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((26 : ℝ)/512)^2 *
        (∫ x in (13/256:ℝ)..(27/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_026).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((26 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((26 : ℝ)/512)^2 *
          (3/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((26 : ℝ)/512)^2 *
        (3/25000000000000000000000 : ℝ) ≤
      ((26 : ℝ)/512)^2 *
        (∫ x in (13/256:ℝ)..(27/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_027 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((27 : ℝ)/512)^2 *
        (∫ x in (27/512:ℝ)..(7/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_027).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((27 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((27 : ℝ)/512)^2 *
          (1/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((27 : ℝ)/512)^2 *
        (1/5000000000000000000000 : ℝ) ≤
      ((27 : ℝ)/512)^2 *
        (∫ x in (27/512:ℝ)..(7/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_028 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((28 : ℝ)/512)^2 *
        (∫ x in (7/128:ℝ)..(29/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_028).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((28 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((28 : ℝ)/512)^2 *
          (33/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((28 : ℝ)/512)^2 *
        (33/100000000000000000000000 : ℝ) ≤
      ((28 : ℝ)/512)^2 *
        (∫ x in (7/128:ℝ)..(29/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_029 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((29 : ℝ)/512)^2 *
        (∫ x in (29/512:ℝ)..(15/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_029).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((29 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((29 : ℝ)/512)^2 *
          (53/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((29 : ℝ)/512)^2 *
        (53/100000000000000000000000 : ℝ) ≤
      ((29 : ℝ)/512)^2 *
        (∫ x in (29/512:ℝ)..(15/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_030 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((30 : ℝ)/512)^2 *
        (∫ x in (15/256:ℝ)..(31/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_030).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((30 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((30 : ℝ)/512)^2 *
          (83/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((30 : ℝ)/512)^2 *
        (83/100000000000000000000000 : ℝ) ≤
      ((30 : ℝ)/512)^2 *
        (∫ x in (15/256:ℝ)..(31/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_031 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((31 : ℝ)/512)^2 *
        (∫ x in (31/512:ℝ)..(1/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_031).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((31 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((31 : ℝ)/512)^2 *
          (129/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((31 : ℝ)/512)^2 *
        (129/100000000000000000000000 : ℝ) ≤
      ((31 : ℝ)/512)^2 *
        (∫ x in (31/512:ℝ)..(1/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
