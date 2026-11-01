import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_01
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_032 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((32 : ℝ)/512)^2 *
        (∫ x in (1/16:ℝ)..(33/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_032).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((32 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((32 : ℝ)/512)^2 *
          (197/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((32 : ℝ)/512)^2 *
        (197/100000000000000000000000 : ℝ) ≤
      ((32 : ℝ)/512)^2 *
        (∫ x in (1/16:ℝ)..(33/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_033 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((33 : ℝ)/512)^2 *
        (∫ x in (33/512:ℝ)..(17/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_033).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((33 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((33 : ℝ)/512)^2 *
          (149/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((33 : ℝ)/512)^2 *
        (149/50000000000000000000000 : ℝ) ≤
      ((33 : ℝ)/512)^2 *
        (∫ x in (33/512:ℝ)..(17/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_034 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((34 : ℝ)/512)^2 *
        (∫ x in (17/256:ℝ)..(35/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_034).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((34 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((34 : ℝ)/512)^2 *
          (111/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((34 : ℝ)/512)^2 *
        (111/25000000000000000000000 : ℝ) ≤
      ((34 : ℝ)/512)^2 *
        (∫ x in (17/256:ℝ)..(35/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_035 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((35 : ℝ)/512)^2 *
        (∫ x in (35/512:ℝ)..(9/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_035).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((35 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((35 : ℝ)/512)^2 *
          (653/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((35 : ℝ)/512)^2 *
        (653/100000000000000000000000 : ℝ) ≤
      ((35 : ℝ)/512)^2 *
        (∫ x in (35/512:ℝ)..(9/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_036 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((36 : ℝ)/512)^2 *
        (∫ x in (9/128:ℝ)..(37/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_036).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((36 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((36 : ℝ)/512)^2 *
          (951/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((36 : ℝ)/512)^2 *
        (951/100000000000000000000000 : ℝ) ≤
      ((36 : ℝ)/512)^2 *
        (∫ x in (9/128:ℝ)..(37/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_037 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((37 : ℝ)/512)^2 *
        (∫ x in (37/512:ℝ)..(19/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_037).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((37 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((37 : ℝ)/512)^2 *
          (137/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((37 : ℝ)/512)^2 *
        (137/10000000000000000000000 : ℝ) ≤
      ((37 : ℝ)/512)^2 *
        (∫ x in (37/512:ℝ)..(19/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_038 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((38 : ℝ)/512)^2 *
        (∫ x in (19/256:ℝ)..(39/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_038).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((38 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((38 : ℝ)/512)^2 *
          (977/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((38 : ℝ)/512)^2 *
        (977/50000000000000000000000 : ℝ) ≤
      ((38 : ℝ)/512)^2 *
        (∫ x in (19/256:ℝ)..(39/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_039 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((39 : ℝ)/512)^2 *
        (∫ x in (39/512:ℝ)..(5/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_039).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((39 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((39 : ℝ)/512)^2 *
          (69/2500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((39 : ℝ)/512)^2 *
        (69/2500000000000000000000 : ℝ) ≤
      ((39 : ℝ)/512)^2 *
        (∫ x in (39/512:ℝ)..(5/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_040 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((40 : ℝ)/512)^2 *
        (∫ x in (5/64:ℝ)..(41/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_040).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((40 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((40 : ℝ)/512)^2 *
          (483/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((40 : ℝ)/512)^2 *
        (483/12500000000000000000000 : ℝ) ≤
      ((40 : ℝ)/512)^2 *
        (∫ x in (5/64:ℝ)..(41/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_041 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((41 : ℝ)/512)^2 *
        (∫ x in (41/512:ℝ)..(21/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_041).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((41 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((41 : ℝ)/512)^2 *
          (1341/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((41 : ℝ)/512)^2 *
        (1341/25000000000000000000000 : ℝ) ≤
      ((41 : ℝ)/512)^2 *
        (∫ x in (41/512:ℝ)..(21/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_042 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((42 : ℝ)/512)^2 *
        (∫ x in (21/256:ℝ)..(43/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_042).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((42 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((42 : ℝ)/512)^2 *
          (923/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((42 : ℝ)/512)^2 *
        (923/12500000000000000000000 : ℝ) ≤
      ((42 : ℝ)/512)^2 *
        (∫ x in (21/256:ℝ)..(43/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_043 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((43 : ℝ)/512)^2 *
        (∫ x in (43/512:ℝ)..(11/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_043).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((43 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((43 : ℝ)/512)^2 *
          (10087/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((43 : ℝ)/512)^2 *
        (10087/100000000000000000000000 : ℝ) ≤
      ((43 : ℝ)/512)^2 *
        (∫ x in (43/512:ℝ)..(11/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_044 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((44 : ℝ)/512)^2 *
        (∫ x in (11/128:ℝ)..(45/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_044).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((44 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((44 : ℝ)/512)^2 *
          (13677/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((44 : ℝ)/512)^2 *
        (13677/100000000000000000000000 : ℝ) ≤
      ((44 : ℝ)/512)^2 *
        (∫ x in (11/128:ℝ)..(45/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_045 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((45 : ℝ)/512)^2 *
        (∫ x in (45/512:ℝ)..(23/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_045).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((45 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((45 : ℝ)/512)^2 *
          (4603/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((45 : ℝ)/512)^2 *
        (4603/25000000000000000000000 : ℝ) ≤
      ((45 : ℝ)/512)^2 *
        (∫ x in (45/512:ℝ)..(23/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_046 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((46 : ℝ)/512)^2 *
        (∫ x in (23/256:ℝ)..(47/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_046).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((46 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((46 : ℝ)/512)^2 *
          (24619/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((46 : ℝ)/512)^2 *
        (24619/100000000000000000000000 : ℝ) ≤
      ((46 : ℝ)/512)^2 *
        (∫ x in (23/256:ℝ)..(47/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_047 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((47 : ℝ)/512)^2 *
        (∫ x in (47/512:ℝ)..(3/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_047).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((47 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((47 : ℝ)/512)^2 *
          (511/1562500000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((47 : ℝ)/512)^2 *
        (511/1562500000000000000000 : ℝ) ≤
      ((47 : ℝ)/512)^2 *
        (∫ x in (47/512:ℝ)..(3/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_048 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((48 : ℝ)/512)^2 *
        (∫ x in (3/32:ℝ)..(49/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_048).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((48 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((48 : ℝ)/512)^2 *
          (43173/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((48 : ℝ)/512)^2 *
        (43173/100000000000000000000000 : ℝ) ≤
      ((48 : ℝ)/512)^2 *
        (∫ x in (3/32:ℝ)..(49/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_049 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((49 : ℝ)/512)^2 *
        (∫ x in (49/512:ℝ)..(25/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_049).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((49 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((49 : ℝ)/512)^2 *
          (56653/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((49 : ℝ)/512)^2 *
        (56653/100000000000000000000000 : ℝ) ≤
      ((49 : ℝ)/512)^2 *
        (∫ x in (49/512:ℝ)..(25/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_050 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((50 : ℝ)/512)^2 *
        (∫ x in (25/256:ℝ)..(51/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_050).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((50 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((50 : ℝ)/512)^2 *
          (36957/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((50 : ℝ)/512)^2 *
        (36957/50000000000000000000000 : ℝ) ≤
      ((50 : ℝ)/512)^2 *
        (∫ x in (25/256:ℝ)..(51/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_051 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((51 : ℝ)/512)^2 *
        (∫ x in (51/512:ℝ)..(13/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_051).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((51 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((51 : ℝ)/512)^2 *
          (959/1000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((51 : ℝ)/512)^2 *
        (959/1000000000000000000000 : ℝ) ≤
      ((51 : ℝ)/512)^2 *
        (∫ x in (51/512:ℝ)..(13/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_052 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((52 : ℝ)/512)^2 *
        (∫ x in (13/128:ℝ)..(53/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_052).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((52 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((52 : ℝ)/512)^2 *
          (24753/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((52 : ℝ)/512)^2 *
        (24753/20000000000000000000000 : ℝ) ≤
      ((52 : ℝ)/512)^2 *
        (∫ x in (13/128:ℝ)..(53/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_053 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((53 : ℝ)/512)^2 *
        (∫ x in (53/512:ℝ)..(27/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_053).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((53 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((53 : ℝ)/512)^2 *
          (158909/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((53 : ℝ)/512)^2 *
        (158909/100000000000000000000000 : ℝ) ≤
      ((53 : ℝ)/512)^2 *
        (∫ x in (53/512:ℝ)..(27/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_054 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((54 : ℝ)/512)^2 *
        (∫ x in (27/256:ℝ)..(55/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_054).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((54 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((54 : ℝ)/512)^2 *
          (8121/4000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((54 : ℝ)/512)^2 *
        (8121/4000000000000000000000 : ℝ) ≤
      ((54 : ℝ)/512)^2 *
        (∫ x in (27/256:ℝ)..(55/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_055 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((55 : ℝ)/512)^2 *
        (∫ x in (55/512:ℝ)..(7/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_055).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((55 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((55 : ℝ)/512)^2 *
          (51631/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((55 : ℝ)/512)^2 *
        (51631/20000000000000000000000 : ℝ) ≤
      ((55 : ℝ)/512)^2 *
        (∫ x in (55/512:ℝ)..(7/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_056 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((56 : ℝ)/512)^2 *
        (∫ x in (7/64:ℝ)..(57/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_056).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((56 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((56 : ℝ)/512)^2 *
          (81687/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((56 : ℝ)/512)^2 *
        (81687/25000000000000000000000 : ℝ) ≤
      ((56 : ℝ)/512)^2 *
        (∫ x in (7/64:ℝ)..(57/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_057 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((57 : ℝ)/512)^2 *
        (∫ x in (57/512:ℝ)..(29/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_057).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((57 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((57 : ℝ)/512)^2 *
          (411733/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((57 : ℝ)/512)^2 *
        (411733/100000000000000000000000 : ℝ) ≤
      ((57 : ℝ)/512)^2 *
        (∫ x in (57/512:ℝ)..(29/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_058 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((58 : ℝ)/512)^2 *
        (∫ x in (29/256:ℝ)..(59/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_058).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((58 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((58 : ℝ)/512)^2 *
          (516601/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((58 : ℝ)/512)^2 *
        (516601/100000000000000000000000 : ℝ) ≤
      ((58 : ℝ)/512)^2 *
        (∫ x in (29/256:ℝ)..(59/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_059 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((59 : ℝ)/512)^2 *
        (∫ x in (59/512:ℝ)..(15/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_059).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((59 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((59 : ℝ)/512)^2 *
          (80687/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((59 : ℝ)/512)^2 *
        (80687/12500000000000000000000 : ℝ) ≤
      ((59 : ℝ)/512)^2 *
        (∫ x in (59/512:ℝ)..(15/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_060 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((60 : ℝ)/512)^2 *
        (∫ x in (15/128:ℝ)..(61/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_060).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((60 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((60 : ℝ)/512)^2 *
          (401661/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((60 : ℝ)/512)^2 *
        (401661/50000000000000000000000 : ℝ) ≤
      ((60 : ℝ)/512)^2 *
        (∫ x in (15/128:ℝ)..(61/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_061 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((61 : ℝ)/512)^2 *
        (∫ x in (61/512:ℝ)..(31/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_061).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((61 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((61 : ℝ)/512)^2 *
          (995861/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((61 : ℝ)/512)^2 *
        (995861/100000000000000000000000 : ℝ) ≤
      ((61 : ℝ)/512)^2 *
        (∫ x in (61/512:ℝ)..(31/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_062 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((62 : ℝ)/512)^2 *
        (∫ x in (31/256:ℝ)..(63/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_062).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((62 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((62 : ℝ)/512)^2 *
          (307479/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((62 : ℝ)/512)^2 *
        (307479/25000000000000000000000 : ℝ) ≤
      ((62 : ℝ)/512)^2 *
        (∫ x in (31/256:ℝ)..(63/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_063 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((63 : ℝ)/512)^2 *
        (∫ x in (63/512:ℝ)..(1/8:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_063).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((63 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((63 : ℝ)/512)^2 *
          (94591/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((63 : ℝ)/512)^2 *
        (94591/6250000000000000000000 : ℝ) ≤
      ((63 : ℝ)/512)^2 *
        (∫ x in (63/512:ℝ)..(1/8:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
