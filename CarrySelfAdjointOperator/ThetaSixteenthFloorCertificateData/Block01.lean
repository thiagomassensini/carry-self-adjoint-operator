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
        (∫ x in (((32 : ℝ)/512))..((((32+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_032).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((32 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((32 : ℝ)/512)^2 *
          (197/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (1/16 : ℝ) = ((32 : ℝ)/512) := by
    norm_num
  have hright :
      (33/512 : ℝ) = (((( 32+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((32 : ℝ)/512)^2 *
        (197/100000000000000000000000 : ℝ) ≤
      ((32 : ℝ)/512)^2 *
        (∫ x in (((32 : ℝ)/512))..((((32+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_033 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((33 : ℝ)/512)^2 *
        (∫ x in (((33 : ℝ)/512))..((((33+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_033).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((33 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((33 : ℝ)/512)^2 *
          (149/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (33/512 : ℝ) = ((33 : ℝ)/512) := by
    norm_num
  have hright :
      (17/256 : ℝ) = (((( 33+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((33 : ℝ)/512)^2 *
        (149/50000000000000000000000 : ℝ) ≤
      ((33 : ℝ)/512)^2 *
        (∫ x in (((33 : ℝ)/512))..((((33+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_034 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((34 : ℝ)/512)^2 *
        (∫ x in (((34 : ℝ)/512))..((((34+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_034).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((34 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((34 : ℝ)/512)^2 *
          (111/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (17/256 : ℝ) = ((34 : ℝ)/512) := by
    norm_num
  have hright :
      (35/512 : ℝ) = (((( 34+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((34 : ℝ)/512)^2 *
        (111/25000000000000000000000 : ℝ) ≤
      ((34 : ℝ)/512)^2 *
        (∫ x in (((34 : ℝ)/512))..((((34+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_035 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((35 : ℝ)/512)^2 *
        (∫ x in (((35 : ℝ)/512))..((((35+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_035).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((35 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((35 : ℝ)/512)^2 *
          (653/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (35/512 : ℝ) = ((35 : ℝ)/512) := by
    norm_num
  have hright :
      (9/128 : ℝ) = (((( 35+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((35 : ℝ)/512)^2 *
        (653/100000000000000000000000 : ℝ) ≤
      ((35 : ℝ)/512)^2 *
        (∫ x in (((35 : ℝ)/512))..((((35+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_036 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((36 : ℝ)/512)^2 *
        (∫ x in (((36 : ℝ)/512))..((((36+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_036).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((36 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((36 : ℝ)/512)^2 *
          (951/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (9/128 : ℝ) = ((36 : ℝ)/512) := by
    norm_num
  have hright :
      (37/512 : ℝ) = (((( 36+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((36 : ℝ)/512)^2 *
        (951/100000000000000000000000 : ℝ) ≤
      ((36 : ℝ)/512)^2 *
        (∫ x in (((36 : ℝ)/512))..((((36+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_037 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((37 : ℝ)/512)^2 *
        (∫ x in (((37 : ℝ)/512))..((((37+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_037).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((37 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((37 : ℝ)/512)^2 *
          (137/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (37/512 : ℝ) = ((37 : ℝ)/512) := by
    norm_num
  have hright :
      (19/256 : ℝ) = (((( 37+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((37 : ℝ)/512)^2 *
        (137/10000000000000000000000 : ℝ) ≤
      ((37 : ℝ)/512)^2 *
        (∫ x in (((37 : ℝ)/512))..((((37+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_038 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((38 : ℝ)/512)^2 *
        (∫ x in (((38 : ℝ)/512))..((((38+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_038).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((38 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((38 : ℝ)/512)^2 *
          (977/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (19/256 : ℝ) = ((38 : ℝ)/512) := by
    norm_num
  have hright :
      (39/512 : ℝ) = (((( 38+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((38 : ℝ)/512)^2 *
        (977/50000000000000000000000 : ℝ) ≤
      ((38 : ℝ)/512)^2 *
        (∫ x in (((38 : ℝ)/512))..((((38+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_039 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((39 : ℝ)/512)^2 *
        (∫ x in (((39 : ℝ)/512))..((((39+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_039).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((39 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((39 : ℝ)/512)^2 *
          (69/2500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (39/512 : ℝ) = ((39 : ℝ)/512) := by
    norm_num
  have hright :
      (5/64 : ℝ) = (((( 39+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((39 : ℝ)/512)^2 *
        (69/2500000000000000000000 : ℝ) ≤
      ((39 : ℝ)/512)^2 *
        (∫ x in (((39 : ℝ)/512))..((((39+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_040 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((40 : ℝ)/512)^2 *
        (∫ x in (((40 : ℝ)/512))..((((40+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_040).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((40 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((40 : ℝ)/512)^2 *
          (483/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (5/64 : ℝ) = ((40 : ℝ)/512) := by
    norm_num
  have hright :
      (41/512 : ℝ) = (((( 40+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((40 : ℝ)/512)^2 *
        (483/12500000000000000000000 : ℝ) ≤
      ((40 : ℝ)/512)^2 *
        (∫ x in (((40 : ℝ)/512))..((((40+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_041 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((41 : ℝ)/512)^2 *
        (∫ x in (((41 : ℝ)/512))..((((41+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_041).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((41 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((41 : ℝ)/512)^2 *
          (1341/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (41/512 : ℝ) = ((41 : ℝ)/512) := by
    norm_num
  have hright :
      (21/256 : ℝ) = (((( 41+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((41 : ℝ)/512)^2 *
        (1341/25000000000000000000000 : ℝ) ≤
      ((41 : ℝ)/512)^2 *
        (∫ x in (((41 : ℝ)/512))..((((41+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_042 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((42 : ℝ)/512)^2 *
        (∫ x in (((42 : ℝ)/512))..((((42+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_042).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((42 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((42 : ℝ)/512)^2 *
          (923/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (21/256 : ℝ) = ((42 : ℝ)/512) := by
    norm_num
  have hright :
      (43/512 : ℝ) = (((( 42+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((42 : ℝ)/512)^2 *
        (923/12500000000000000000000 : ℝ) ≤
      ((42 : ℝ)/512)^2 *
        (∫ x in (((42 : ℝ)/512))..((((42+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_043 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((43 : ℝ)/512)^2 *
        (∫ x in (((43 : ℝ)/512))..((((43+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_043).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((43 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((43 : ℝ)/512)^2 *
          (10087/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (43/512 : ℝ) = ((43 : ℝ)/512) := by
    norm_num
  have hright :
      (11/128 : ℝ) = (((( 43+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((43 : ℝ)/512)^2 *
        (10087/100000000000000000000000 : ℝ) ≤
      ((43 : ℝ)/512)^2 *
        (∫ x in (((43 : ℝ)/512))..((((43+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_044 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((44 : ℝ)/512)^2 *
        (∫ x in (((44 : ℝ)/512))..((((44+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_044).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((44 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((44 : ℝ)/512)^2 *
          (13677/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (11/128 : ℝ) = ((44 : ℝ)/512) := by
    norm_num
  have hright :
      (45/512 : ℝ) = (((( 44+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((44 : ℝ)/512)^2 *
        (13677/100000000000000000000000 : ℝ) ≤
      ((44 : ℝ)/512)^2 *
        (∫ x in (((44 : ℝ)/512))..((((44+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_045 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((45 : ℝ)/512)^2 *
        (∫ x in (((45 : ℝ)/512))..((((45+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_045).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((45 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((45 : ℝ)/512)^2 *
          (4603/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (45/512 : ℝ) = ((45 : ℝ)/512) := by
    norm_num
  have hright :
      (23/256 : ℝ) = (((( 45+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((45 : ℝ)/512)^2 *
        (4603/25000000000000000000000 : ℝ) ≤
      ((45 : ℝ)/512)^2 *
        (∫ x in (((45 : ℝ)/512))..((((45+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_046 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((46 : ℝ)/512)^2 *
        (∫ x in (((46 : ℝ)/512))..((((46+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_046).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((46 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((46 : ℝ)/512)^2 *
          (24619/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (23/256 : ℝ) = ((46 : ℝ)/512) := by
    norm_num
  have hright :
      (47/512 : ℝ) = (((( 46+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((46 : ℝ)/512)^2 *
        (24619/100000000000000000000000 : ℝ) ≤
      ((46 : ℝ)/512)^2 *
        (∫ x in (((46 : ℝ)/512))..((((46+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_047 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((47 : ℝ)/512)^2 *
        (∫ x in (((47 : ℝ)/512))..((((47+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_047).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((47 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((47 : ℝ)/512)^2 *
          (511/1562500000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (47/512 : ℝ) = ((47 : ℝ)/512) := by
    norm_num
  have hright :
      (3/32 : ℝ) = (((( 47+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((47 : ℝ)/512)^2 *
        (511/1562500000000000000000 : ℝ) ≤
      ((47 : ℝ)/512)^2 *
        (∫ x in (((47 : ℝ)/512))..((((47+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_048 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((48 : ℝ)/512)^2 *
        (∫ x in (((48 : ℝ)/512))..((((48+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_048).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((48 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((48 : ℝ)/512)^2 *
          (43173/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (3/32 : ℝ) = ((48 : ℝ)/512) := by
    norm_num
  have hright :
      (49/512 : ℝ) = (((( 48+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((48 : ℝ)/512)^2 *
        (43173/100000000000000000000000 : ℝ) ≤
      ((48 : ℝ)/512)^2 *
        (∫ x in (((48 : ℝ)/512))..((((48+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_049 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((49 : ℝ)/512)^2 *
        (∫ x in (((49 : ℝ)/512))..((((49+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_049).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((49 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((49 : ℝ)/512)^2 *
          (56653/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (49/512 : ℝ) = ((49 : ℝ)/512) := by
    norm_num
  have hright :
      (25/256 : ℝ) = (((( 49+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((49 : ℝ)/512)^2 *
        (56653/100000000000000000000000 : ℝ) ≤
      ((49 : ℝ)/512)^2 *
        (∫ x in (((49 : ℝ)/512))..((((49+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_050 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((50 : ℝ)/512)^2 *
        (∫ x in (((50 : ℝ)/512))..((((50+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_050).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((50 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((50 : ℝ)/512)^2 *
          (36957/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (25/256 : ℝ) = ((50 : ℝ)/512) := by
    norm_num
  have hright :
      (51/512 : ℝ) = (((( 50+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((50 : ℝ)/512)^2 *
        (36957/50000000000000000000000 : ℝ) ≤
      ((50 : ℝ)/512)^2 *
        (∫ x in (((50 : ℝ)/512))..((((50+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_051 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((51 : ℝ)/512)^2 *
        (∫ x in (((51 : ℝ)/512))..((((51+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_051).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((51 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((51 : ℝ)/512)^2 *
          (959/1000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (51/512 : ℝ) = ((51 : ℝ)/512) := by
    norm_num
  have hright :
      (13/128 : ℝ) = (((( 51+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((51 : ℝ)/512)^2 *
        (959/1000000000000000000000 : ℝ) ≤
      ((51 : ℝ)/512)^2 *
        (∫ x in (((51 : ℝ)/512))..((((51+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_052 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((52 : ℝ)/512)^2 *
        (∫ x in (((52 : ℝ)/512))..((((52+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_052).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((52 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((52 : ℝ)/512)^2 *
          (24753/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (13/128 : ℝ) = ((52 : ℝ)/512) := by
    norm_num
  have hright :
      (53/512 : ℝ) = (((( 52+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((52 : ℝ)/512)^2 *
        (24753/20000000000000000000000 : ℝ) ≤
      ((52 : ℝ)/512)^2 *
        (∫ x in (((52 : ℝ)/512))..((((52+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_053 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((53 : ℝ)/512)^2 *
        (∫ x in (((53 : ℝ)/512))..((((53+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_053).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((53 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((53 : ℝ)/512)^2 *
          (158909/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (53/512 : ℝ) = ((53 : ℝ)/512) := by
    norm_num
  have hright :
      (27/256 : ℝ) = (((( 53+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((53 : ℝ)/512)^2 *
        (158909/100000000000000000000000 : ℝ) ≤
      ((53 : ℝ)/512)^2 *
        (∫ x in (((53 : ℝ)/512))..((((53+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_054 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((54 : ℝ)/512)^2 *
        (∫ x in (((54 : ℝ)/512))..((((54+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_054).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((54 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((54 : ℝ)/512)^2 *
          (8121/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (27/256 : ℝ) = ((54 : ℝ)/512) := by
    norm_num
  have hright :
      (55/512 : ℝ) = (((( 54+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((54 : ℝ)/512)^2 *
        (8121/4000000000000000000000 : ℝ) ≤
      ((54 : ℝ)/512)^2 *
        (∫ x in (((54 : ℝ)/512))..((((54+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_055 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((55 : ℝ)/512)^2 *
        (∫ x in (((55 : ℝ)/512))..((((55+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_055).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((55 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((55 : ℝ)/512)^2 *
          (51631/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (55/512 : ℝ) = ((55 : ℝ)/512) := by
    norm_num
  have hright :
      (7/64 : ℝ) = (((( 55+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((55 : ℝ)/512)^2 *
        (51631/20000000000000000000000 : ℝ) ≤
      ((55 : ℝ)/512)^2 *
        (∫ x in (((55 : ℝ)/512))..((((55+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_056 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((56 : ℝ)/512)^2 *
        (∫ x in (((56 : ℝ)/512))..((((56+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_056).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((56 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((56 : ℝ)/512)^2 *
          (81687/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (7/64 : ℝ) = ((56 : ℝ)/512) := by
    norm_num
  have hright :
      (57/512 : ℝ) = (((( 56+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((56 : ℝ)/512)^2 *
        (81687/25000000000000000000000 : ℝ) ≤
      ((56 : ℝ)/512)^2 *
        (∫ x in (((56 : ℝ)/512))..((((56+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_057 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((57 : ℝ)/512)^2 *
        (∫ x in (((57 : ℝ)/512))..((((57+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_057).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((57 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((57 : ℝ)/512)^2 *
          (411733/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (57/512 : ℝ) = ((57 : ℝ)/512) := by
    norm_num
  have hright :
      (29/256 : ℝ) = (((( 57+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((57 : ℝ)/512)^2 *
        (411733/100000000000000000000000 : ℝ) ≤
      ((57 : ℝ)/512)^2 *
        (∫ x in (((57 : ℝ)/512))..((((57+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_058 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((58 : ℝ)/512)^2 *
        (∫ x in (((58 : ℝ)/512))..((((58+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_058).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((58 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((58 : ℝ)/512)^2 *
          (516601/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (29/256 : ℝ) = ((58 : ℝ)/512) := by
    norm_num
  have hright :
      (59/512 : ℝ) = (((( 58+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((58 : ℝ)/512)^2 *
        (516601/100000000000000000000000 : ℝ) ≤
      ((58 : ℝ)/512)^2 *
        (∫ x in (((58 : ℝ)/512))..((((58+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_059 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((59 : ℝ)/512)^2 *
        (∫ x in (((59 : ℝ)/512))..((((59+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_059).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((59 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((59 : ℝ)/512)^2 *
          (80687/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (59/512 : ℝ) = ((59 : ℝ)/512) := by
    norm_num
  have hright :
      (15/128 : ℝ) = (((( 59+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((59 : ℝ)/512)^2 *
        (80687/12500000000000000000000 : ℝ) ≤
      ((59 : ℝ)/512)^2 *
        (∫ x in (((59 : ℝ)/512))..((((59+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_060 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((60 : ℝ)/512)^2 *
        (∫ x in (((60 : ℝ)/512))..((((60+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_060).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((60 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((60 : ℝ)/512)^2 *
          (401661/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (15/128 : ℝ) = ((60 : ℝ)/512) := by
    norm_num
  have hright :
      (61/512 : ℝ) = (((( 60+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((60 : ℝ)/512)^2 *
        (401661/50000000000000000000000 : ℝ) ≤
      ((60 : ℝ)/512)^2 *
        (∫ x in (((60 : ℝ)/512))..((((60+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_061 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((61 : ℝ)/512)^2 *
        (∫ x in (((61 : ℝ)/512))..((((61+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_061).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((61 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((61 : ℝ)/512)^2 *
          (995861/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (61/512 : ℝ) = ((61 : ℝ)/512) := by
    norm_num
  have hright :
      (31/256 : ℝ) = (((( 61+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((61 : ℝ)/512)^2 *
        (995861/100000000000000000000000 : ℝ) ≤
      ((61 : ℝ)/512)^2 *
        (∫ x in (((61 : ℝ)/512))..((((61+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_062 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((62 : ℝ)/512)^2 *
        (∫ x in (((62 : ℝ)/512))..((((62+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_062).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((62 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((62 : ℝ)/512)^2 *
          (307479/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (31/256 : ℝ) = ((62 : ℝ)/512) := by
    norm_num
  have hright :
      (63/512 : ℝ) = (((( 62+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((62 : ℝ)/512)^2 *
        (307479/25000000000000000000000 : ℝ) ≤
      ((62 : ℝ)/512)^2 *
        (∫ x in (((62 : ℝ)/512))..((((62+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_063 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((63 : ℝ)/512)^2 *
        (∫ x in (((63 : ℝ)/512))..((((63+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_063).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((63 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((63 : ℝ)/512)^2 *
          (94591/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (63/512 : ℝ) = ((63 : ℝ)/512) := by
    norm_num
  have hright :
      (1/8 : ℝ) = (((( 63+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((63 : ℝ)/512)^2 *
        (94591/6250000000000000000000 : ℝ) ≤
      ((63 : ℝ)/512)^2 *
        (∫ x in (((63 : ℝ)/512))..((((63+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
