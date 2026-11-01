import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_15
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_480 :
    (2749228 : ℝ) / 1000000000000000000 ≤
      ((480 : ℝ)/512)^2 *
        (∫ x in (15/16:ℝ)..(481/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_480).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((480 : ℝ)/512)^2 by positivity)
  have hn :
      (2749228 : ℝ) / 1000000000000000000 ≤
        ((480 : ℝ)/512)^2 *
          (31280106921/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((480 : ℝ)/512)^2 *
        (31280106921/10000000000000000000000 : ℝ) ≤
      ((480 : ℝ)/512)^2 *
        (∫ x in (15/16:ℝ)..(481/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_481 :
    (2625393 : ℝ) / 1000000000000000000 ≤
      ((481 : ℝ)/512)^2 *
        (∫ x in (481/512:ℝ)..(241/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_481).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((481 : ℝ)/512)^2 by positivity)
  have hn :
      (2625393 : ℝ) / 1000000000000000000 ≤
        ((481 : ℝ)/512)^2 *
          (3718383933/1250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((481 : ℝ)/512)^2 *
        (3718383933/1250000000000000000000 : ℝ) ≤
      ((481 : ℝ)/512)^2 *
        (∫ x in (481/512:ℝ)..(241/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_482 :
    (2506176 : ℝ) / 1000000000000000000 ≤
      ((482 : ℝ)/512)^2 *
        (∫ x in (241/256:ℝ)..(483/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_482).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((482 : ℝ)/512)^2 by positivity)
  have hn :
      (2506176 : ℝ) / 1000000000000000000 ≤
        ((482 : ℝ)/512)^2 *
          (14139284631/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((482 : ℝ)/512)^2 *
        (14139284631/5000000000000000000000 : ℝ) ≤
      ((482 : ℝ)/512)^2 *
        (∫ x in (241/256:ℝ)..(483/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_483 :
    (2391452 : ℝ) / 1000000000000000000 ≤
      ((483 : ℝ)/512)^2 *
        (∫ x in (483/512:ℝ)..(121/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_483).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((483 : ℝ)/512)^2 by positivity)
  have hn :
      (2391452 : ℝ) / 1000000000000000000 ≤
        ((483 : ℝ)/512)^2 *
          (268724616069/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((483 : ℝ)/512)^2 *
        (268724616069/100000000000000000000000 : ℝ) ≤
      ((483 : ℝ)/512)^2 *
        (∫ x in (483/512:ℝ)..(121/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_484 :
    (2281101 : ℝ) / 1000000000000000000 ≤
      ((484 : ℝ)/512)^2 *
        (∫ x in (121/128:ℝ)..(485/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_484).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((484 : ℝ)/512)^2 by positivity)
  have hn :
      (2281101 : ℝ) / 1000000000000000000 ≤
        ((484 : ℝ)/512)^2 *
          (255266511351/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((484 : ℝ)/512)^2 *
        (255266511351/100000000000000000000000 : ℝ) ≤
      ((484 : ℝ)/512)^2 *
        (∫ x in (121/128:ℝ)..(485/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_485 :
    (2175002 : ℝ) / 1000000000000000000 ≤
      ((485 : ℝ)/512)^2 *
        (∫ x in (485/512:ℝ)..(243/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_485).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((485 : ℝ)/512)^2 by positivity)
  have hn :
      (2175002 : ℝ) / 1000000000000000000 ≤
        ((485 : ℝ)/512)^2 *
          (60597706323/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((485 : ℝ)/512)^2 *
        (60597706323/25000000000000000000000 : ℝ) ≤
      ((485 : ℝ)/512)^2 *
        (∫ x in (485/512:ℝ)..(243/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_486 :
    (2073035 : ℝ) / 1000000000000000000 ≤
      ((486 : ℝ)/512)^2 *
        (∫ x in (243/256:ℝ)..(487/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_486).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((486 : ℝ)/512)^2 by positivity)
  have hn :
      (2073035 : ℝ) / 1000000000000000000 ≤
        ((486 : ℝ)/512)^2 *
          (115038715621/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((486 : ℝ)/512)^2 *
        (115038715621/50000000000000000000000 : ℝ) ≤
      ((486 : ℝ)/512)^2 *
        (∫ x in (243/256:ℝ)..(487/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_487 :
    (1975081 : ℝ) / 1000000000000000000 ≤
      ((487 : ℝ)/512)^2 *
        (∫ x in (487/512:ℝ)..(61/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_487).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((487 : ℝ)/512)^2 by positivity)
  have hn :
      (1975081 : ℝ) / 1000000000000000000 ≤
        ((487 : ℝ)/512)^2 *
          (6822082319/3125000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((487 : ℝ)/512)^2 *
        (6822082319/3125000000000000000000 : ℝ) ≤
      ((487 : ℝ)/512)^2 *
        (∫ x in (487/512:ℝ)..(61/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_488 :
    (1881023 : ℝ) / 1000000000000000000 ≤
      ((488 : ℝ)/512)^2 *
        (∫ x in (61/64:ℝ)..(489/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_488).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((488 : ℝ)/512)^2 by positivity)
  have hn :
      (1881023 : ℝ) / 1000000000000000000 ≤
        ((488 : ℝ)/512)^2 *
          (103529587543/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((488 : ℝ)/512)^2 *
        (103529587543/50000000000000000000000 : ℝ) ≤
      ((488 : ℝ)/512)^2 *
        (∫ x in (61/64:ℝ)..(489/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_489 :
    (1790746 : ℝ) / 1000000000000000000 ≤
      ((489 : ℝ)/512)^2 *
        (∫ x in (489/512:ℝ)..(245/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_489).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((489 : ℝ)/512)^2 by positivity)
  have hn :
      (1790746 : ℝ) / 1000000000000000000 ≤
        ((489 : ℝ)/512)^2 *
          (196316234039/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((489 : ℝ)/512)^2 *
        (196316234039/100000000000000000000000 : ℝ) ≤
      ((489 : ℝ)/512)^2 *
        (∫ x in (489/512:ℝ)..(245/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_490 :
    (1704134 : ℝ) / 1000000000000000000 ≤
      ((490 : ℝ)/512)^2 *
        (∫ x in (245/256:ℝ)..(491/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_490).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((490 : ℝ)/512)^2 by positivity)
  have hn :
      (1704134 : ℝ) / 1000000000000000000 ≤
        ((490 : ℝ)/512)^2 *
          (23257429129/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((490 : ℝ)/512)^2 *
        (23257429129/12500000000000000000000 : ℝ) ≤
      ((490 : ℝ)/512)^2 *
        (∫ x in (245/256:ℝ)..(491/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_491 :
    (1621076 : ℝ) / 1000000000000000000 ≤
      ((491 : ℝ)/512)^2 *
        (∫ x in (491/512:ℝ)..(123/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_491).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((491 : ℝ)/512)^2 by positivity)
  have hn :
      (1621076 : ℝ) / 1000000000000000000 ≤
        ((491 : ℝ)/512)^2 *
          (8813541879/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((491 : ℝ)/512)^2 *
        (8813541879/5000000000000000000000 : ℝ) ≤
      ((491 : ℝ)/512)^2 *
        (∫ x in (491/512:ℝ)..(123/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_492 :
    (1541460 : ℝ) / 1000000000000000000 ≤
      ((492 : ℝ)/512)^2 *
        (∫ x in (123/128:ℝ)..(493/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_492).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((492 : ℝ)/512)^2 by positivity)
  have hn :
      (1541460 : ℝ) / 1000000000000000000 ≤
        ((492 : ℝ)/512)^2 *
          (83466478859/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((492 : ℝ)/512)^2 *
        (83466478859/50000000000000000000000 : ℝ) ≤
      ((492 : ℝ)/512)^2 *
        (∫ x in (123/128:ℝ)..(493/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_493 :
    (1465176 : ℝ) / 1000000000000000000 ≤
      ((493 : ℝ)/512)^2 *
        (∫ x in (493/512:ℝ)..(247/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_493).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((493 : ℝ)/512)^2 by positivity)
  have hn :
      (1465176 : ℝ) / 1000000000000000000 ≤
        ((493 : ℝ)/512)^2 *
          (632114993/400000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((493 : ℝ)/512)^2 *
        (632114993/400000000000000000000 : ℝ) ≤
      ((493 : ℝ)/512)^2 *
        (∫ x in (493/512:ℝ)..(247/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_494 :
    (1392117 : ℝ) / 1000000000000000000 ≤
      ((494 : ℝ)/512)^2 *
        (∫ x in (247/256:ℝ)..(495/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_494).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((494 : ℝ)/512)^2 by positivity)
  have hn :
      (1392117 : ℝ) / 1000000000000000000 ≤
        ((494 : ℝ)/512)^2 *
          (18692701037/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((494 : ℝ)/512)^2 *
        (18692701037/12500000000000000000000 : ℝ) ≤
      ((494 : ℝ)/512)^2 *
        (∫ x in (247/256:ℝ)..(495/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_495 :
    (1322178 : ℝ) / 1000000000000000000 ≤
      ((495 : ℝ)/512)^2 *
        (∫ x in (495/512:ℝ)..(31/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_495).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((495 : ℝ)/512)^2 by positivity)
  have hn :
      (1322178 : ℝ) / 1000000000000000000 ≤
        ((495 : ℝ)/512)^2 *
          (70727690083/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((495 : ℝ)/512)^2 *
        (70727690083/50000000000000000000000 : ℝ) ≤
      ((495 : ℝ)/512)^2 *
        (∫ x in (495/512:ℝ)..(31/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_496 :
    (1255253 : ℝ) / 1000000000000000000 ≤
      ((496 : ℝ)/512)^2 *
        (∫ x in (31/32:ℝ)..(497/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_496).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((496 : ℝ)/512)^2 by positivity)
  have hn :
      (1255253 : ℝ) / 1000000000000000000 ≤
        ((496 : ℝ)/512)^2 *
          (66877173809/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((496 : ℝ)/512)^2 *
        (66877173809/50000000000000000000000 : ℝ) ≤
      ((496 : ℝ)/512)^2 *
        (∫ x in (31/32:ℝ)..(497/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_497 :
    (1191241 : ℝ) / 1000000000000000000 ≤
      ((497 : ℝ)/512)^2 *
        (∫ x in (497/512:ℝ)..(249/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_497).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((497 : ℝ)/512)^2 by positivity)
  have hn :
      (1191241 : ℝ) / 1000000000000000000 ≤
        ((497 : ℝ)/512)^2 *
          (63211616749/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((497 : ℝ)/512)^2 *
        (63211616749/50000000000000000000000 : ℝ) ≤
      ((497 : ℝ)/512)^2 *
        (∫ x in (497/512:ℝ)..(249/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_498 :
    (1130042 : ℝ) / 1000000000000000000 ≤
      ((498 : ℝ)/512)^2 *
        (∫ x in (249/256:ℝ)..(499/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_498).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((498 : ℝ)/512)^2 by positivity)
  have hn :
      (1130042 : ℝ) / 1000000000000000000 ≤
        ((498 : ℝ)/512)^2 *
          (29861799207/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((498 : ℝ)/512)^2 *
        (29861799207/25000000000000000000000 : ℝ) ≤
      ((498 : ℝ)/512)^2 *
        (∫ x in (249/256:ℝ)..(499/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_499 :
    (1071558 : ℝ) / 1000000000000000000 ≤
      ((499 : ℝ)/512)^2 *
        (∫ x in (499/512:ℝ)..(125/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_499).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((499 : ℝ)/512)^2 by positivity)
  have hn :
      (1071558 : ℝ) / 1000000000000000000 ≤
        ((499 : ℝ)/512)^2 *
          (22562365871/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((499 : ℝ)/512)^2 *
        (22562365871/20000000000000000000000 : ℝ) ≤
      ((499 : ℝ)/512)^2 *
        (∫ x in (499/512:ℝ)..(125/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_500 :
    (1015693 : ℝ) / 1000000000000000000 ≤
      ((500 : ℝ)/512)^2 *
        (∫ x in (125/128:ℝ)..(501/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_500).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((500 : ℝ)/512)^2 by positivity)
  have hn :
      (1015693 : ℝ) / 1000000000000000000 ≤
        ((500 : ℝ)/512)^2 *
          (266257879/250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((500 : ℝ)/512)^2 *
        (266257879/250000000000000000000 : ℝ) ≤
      ((500 : ℝ)/512)^2 *
        (∫ x in (125/128:ℝ)..(501/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_501 :
    (962353 : ℝ) / 1000000000000000000 ≤
      ((501 : ℝ)/512)^2 *
        (∫ x in (501/512:ℝ)..(251/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_501).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((501 : ℝ)/512)^2 by positivity)
  have hn :
      (962353 : ℝ) / 1000000000000000000 ≤
        ((501 : ℝ)/512)^2 *
          (100507608431/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((501 : ℝ)/512)^2 *
        (100507608431/100000000000000000000000 : ℝ) ≤
      ((501 : ℝ)/512)^2 *
        (∫ x in (501/512:ℝ)..(251/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_502 :
    (911446 : ℝ) / 1000000000000000000 ≤
      ((502 : ℝ)/512)^2 *
        (∫ x in (251/256:ℝ)..(503/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_502).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((502 : ℝ)/512)^2 by positivity)
  have hn :
      (911446 : ℝ) / 1000000000000000000 ≤
        ((502 : ℝ)/512)^2 *
          (5925754013/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((502 : ℝ)/512)^2 *
        (5925754013/6250000000000000000000 : ℝ) ≤
      ((502 : ℝ)/512)^2 *
        (∫ x in (251/256:ℝ)..(503/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_503 :
    (862883 : ℝ) / 1000000000000000000 ≤
      ((503 : ℝ)/512)^2 *
        (∫ x in (503/512:ℝ)..(63/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_503).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((503 : ℝ)/512)^2 by positivity)
  have hn :
      (862883 : ℝ) / 1000000000000000000 ≤
        ((503 : ℝ)/512)^2 *
          (89403797511/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((503 : ℝ)/512)^2 *
        (89403797511/100000000000000000000000 : ℝ) ≤
      ((503 : ℝ)/512)^2 *
        (∫ x in (503/512:ℝ)..(63/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_504 :
    (816576 : ℝ) / 1000000000000000000 ≤
      ((504 : ℝ)/512)^2 *
        (∫ x in (63/64:ℝ)..(505/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_504).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((504 : ℝ)/512)^2 by positivity)
  have hn :
      (816576 : ℝ) / 1000000000000000000 ≤
        ((504 : ℝ)/512)^2 *
          (21067623873/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((504 : ℝ)/512)^2 *
        (21067623873/25000000000000000000000 : ℝ) ≤
      ((504 : ℝ)/512)^2 *
        (∫ x in (63/64:ℝ)..(505/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_505 :
    (772439 : ℝ) / 1000000000000000000 ≤
      ((505 : ℝ)/512)^2 *
        (∫ x in (505/512:ℝ)..(253/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_505).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((505 : ℝ)/512)^2 by positivity)
  have hn :
      (772439 : ℝ) / 1000000000000000000 ≤
        ((505 : ℝ)/512)^2 *
          (39700123941/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((505 : ℝ)/512)^2 *
        (39700123941/50000000000000000000000 : ℝ) ≤
      ((505 : ℝ)/512)^2 *
        (∫ x in (505/512:ℝ)..(253/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_506 :
    (730391 : ℝ) / 1000000000000000000 ≤
      ((506 : ℝ)/512)^2 *
        (∫ x in (253/256:ℝ)..(507/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_506).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((506 : ℝ)/512)^2 by positivity)
  have hn :
      (730391 : ℝ) / 1000000000000000000 ≤
        ((506 : ℝ)/512)^2 *
          (74781540673/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((506 : ℝ)/512)^2 *
        (74781540673/100000000000000000000000 : ℝ) ≤
      ((506 : ℝ)/512)^2 *
        (∫ x in (253/256:ℝ)..(507/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_507 :
    (690349 : ℝ) / 1000000000000000000 ≤
      ((507 : ℝ)/512)^2 *
        (∫ x in (507/512:ℝ)..(127/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_507).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((507 : ℝ)/512)^2 by positivity)
  have hn :
      (690349 : ℝ) / 1000000000000000000 ≤
        ((507 : ℝ)/512)^2 *
          (70403249513/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((507 : ℝ)/512)^2 *
        (70403249513/100000000000000000000000 : ℝ) ≤
      ((507 : ℝ)/512)^2 *
        (∫ x in (507/512:ℝ)..(127/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_508 :
    (652234 : ℝ) / 1000000000000000000 ≤
      ((508 : ℝ)/512)^2 *
        (∫ x in (127/128:ℝ)..(509/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_508).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((508 : ℝ)/512)^2 by positivity)
  have hn :
      (652234 : ℝ) / 1000000000000000000 ≤
        ((508 : ℝ)/512)^2 *
          (66254632829/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((508 : ℝ)/512)^2 *
        (66254632829/100000000000000000000000 : ℝ) ≤
      ((508 : ℝ)/512)^2 *
        (∫ x in (127/128:ℝ)..(509/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_509 :
    (615970 : ℝ) / 1000000000000000000 ≤
      ((509 : ℝ)/512)^2 *
        (∫ x in (509/512:ℝ)..(255/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_509).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((509 : ℝ)/512)^2 by positivity)
  have hn :
      (615970 : ℝ) / 1000000000000000000 ≤
        ((509 : ℝ)/512)^2 *
          (62325324721/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((509 : ℝ)/512)^2 *
        (62325324721/100000000000000000000000 : ℝ) ≤
      ((509 : ℝ)/512)^2 *
        (∫ x in (509/512:ℝ)..(255/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_510 :
    (581483 : ℝ) / 1000000000000000000 ≤
      ((510 : ℝ)/512)^2 *
        (∫ x in (255/256:ℝ)..(511/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_510).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((510 : ℝ)/512)^2 by positivity)
  have hn :
      (581483 : ℝ) / 1000000000000000000 ≤
        ((510 : ℝ)/512)^2 *
          (11721065527/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((510 : ℝ)/512)^2 *
        (11721065527/20000000000000000000000 : ℝ) ≤
      ((510 : ℝ)/512)^2 *
        (∫ x in (255/256:ℝ)..(511/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_511 :
    (548700 : ℝ) / 1000000000000000000 ≤
      ((511 : ℝ)/512)^2 *
        (∫ x in (511/512:ℝ)..(1/1:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_511).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((511 : ℝ)/512)^2 by positivity)
  have hn :
      (548700 : ℝ) / 1000000000000000000 ≤
        ((511 : ℝ)/512)^2 *
          (13771251213/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((511 : ℝ)/512)^2 *
        (13771251213/25000000000000000000000 : ℝ) ≤
      ((511 : ℝ)/512)^2 *
        (∫ x in (511/512:ℝ)..(1/1:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
