import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_16
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_512 :
    (517550 : ℝ) / 1000000000000000000 ≤
      ((512 : ℝ)/512)^2 *
        (∫ x in (((512 : ℝ)/512))..((((512+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_512).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((512 : ℝ)/512)^2 by positivity)
  have hn :
      (517550 : ℝ) / 1000000000000000000 ≤
        ((512 : ℝ)/512)^2 *
          (51755072813/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (1/1 : ℝ) = ((512 : ℝ)/512) := by
    norm_num
  have hright :
      (513/512 : ℝ) = (((( 512+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((512 : ℝ)/512)^2 *
        (51755072813/100000000000000000000000 : ℝ) ≤
      ((512 : ℝ)/512)^2 *
        (∫ x in (((512 : ℝ)/512))..((((512+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_513 :
    (487966 : ℝ) / 1000000000000000000 ≤
      ((513 : ℝ)/512)^2 *
        (∫ x in (((513 : ℝ)/512))..((((513+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_513).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((513 : ℝ)/512)^2 by positivity)
  have hn :
      (487966 : ℝ) / 1000000000000000000 ≤
        ((513 : ℝ)/512)^2 *
          (6075824163/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (513/512 : ℝ) = ((513 : ℝ)/512) := by
    norm_num
  have hright :
      (257/256 : ℝ) = (((( 513+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((513 : ℝ)/512)^2 *
        (6075824163/12500000000000000000000 : ℝ) ≤
      ((513 : ℝ)/512)^2 *
        (∫ x in (((513 : ℝ)/512))..((((513+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_514 :
    (459881 : ℝ) / 1000000000000000000 ≤
      ((514 : ℝ)/512)^2 *
        (∫ x in (((514 : ℝ)/512))..((((514+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_514).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((514 : ℝ)/512)^2 by positivity)
  have hn :
      (459881 : ℝ) / 1000000000000000000 ≤
        ((514 : ℝ)/512)^2 *
          (11407741379/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (257/256 : ℝ) = ((514 : ℝ)/512) := by
    norm_num
  have hright :
      (515/512 : ℝ) = (((( 514+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((514 : ℝ)/512)^2 *
        (11407741379/25000000000000000000000 : ℝ) ≤
      ((514 : ℝ)/512)^2 *
        (∫ x in (((514 : ℝ)/512))..((((514+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_515 :
    (433231 : ℝ) / 1000000000000000000 ≤
      ((515 : ℝ)/512)^2 *
        (∫ x in (((515 : ℝ)/512))..((((515+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_515).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((515 : ℝ)/512)^2 by positivity)
  have hn :
      (433231 : ℝ) / 1000000000000000000 ≤
        ((515 : ℝ)/512)^2 *
          (21409959009/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (515/512 : ℝ) = ((515 : ℝ)/512) := by
    norm_num
  have hright :
      (129/128 : ℝ) = (((( 515+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((515 : ℝ)/512)^2 *
        (21409959009/50000000000000000000000 : ℝ) ≤
      ((515 : ℝ)/512)^2 *
        (∫ x in (((515 : ℝ)/512))..((((515+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_516 :
    (407955 : ℝ) / 1000000000000000000 ≤
      ((516 : ℝ)/512)^2 *
        (∫ x in (((516 : ℝ)/512))..((((516+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_516).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((516 : ℝ)/512)^2 by positivity)
  have hn :
      (407955 : ℝ) / 1000000000000000000 ≤
        ((516 : ℝ)/512)^2 *
          (251034379/625000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (129/128 : ℝ) = ((516 : ℝ)/512) := by
    norm_num
  have hright :
      (517/512 : ℝ) = (((( 516+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((516 : ℝ)/512)^2 *
        (251034379/625000000000000000000 : ℝ) ≤
      ((516 : ℝ)/512)^2 *
        (∫ x in (((516 : ℝ)/512))..((((516+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_517 :
    (383992 : ℝ) / 1000000000000000000 ≤
      ((517 : ℝ)/512)^2 *
        (∫ x in (((517 : ℝ)/512))..((((517+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_517).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((517 : ℝ)/512)^2 by positivity)
  have hn :
      (383992 : ℝ) / 1000000000000000000 ≤
        ((517 : ℝ)/512)^2 *
          (18830038157/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (517/512 : ℝ) = ((517 : ℝ)/512) := by
    norm_num
  have hright :
      (259/256 : ℝ) = (((( 517+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((517 : ℝ)/512)^2 *
        (18830038157/50000000000000000000000 : ℝ) ≤
      ((517 : ℝ)/512)^2 *
        (∫ x in (((517 : ℝ)/512))..((((517+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_518 :
    (361284 : ℝ) / 1000000000000000000 ≤
      ((518 : ℝ)/512)^2 *
        (∫ x in (((518 : ℝ)/512))..((((518+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_518).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((518 : ℝ)/512)^2 by positivity)
  have hn :
      (361284 : ℝ) / 1000000000000000000 ≤
        ((518 : ℝ)/512)^2 *
          (35296312857/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (259/256 : ℝ) = ((518 : ℝ)/512) := by
    norm_num
  have hright :
      (519/512 : ℝ) = (((( 518+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((518 : ℝ)/512)^2 *
        (35296312857/100000000000000000000000 : ℝ) ≤
      ((518 : ℝ)/512)^2 *
        (∫ x in (((518 : ℝ)/512))..((((518+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_519 :
    (339775 : ℝ) / 1000000000000000000 ≤
      ((519 : ℝ)/512)^2 *
        (∫ x in (((519 : ℝ)/512))..((((519+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_519).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((519 : ℝ)/512)^2 by positivity)
  have hn :
      (339775 : ℝ) / 1000000000000000000 ≤
        ((519 : ℝ)/512)^2 *
          (1033349211/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (519/512 : ℝ) = ((519 : ℝ)/512) := by
    norm_num
  have hright :
      (65/64 : ℝ) = (((( 519+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((519 : ℝ)/512)^2 *
        (1033349211/3125000000000000000000 : ℝ) ≤
      ((519 : ℝ)/512)^2 *
        (∫ x in (((519 : ℝ)/512))..((((519+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_520 :
    (319411 : ℝ) / 1000000000000000000 ≤
      ((520 : ℝ)/512)^2 *
        (∫ x in (((520 : ℝ)/512))..((((520+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_520).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((520 : ℝ)/512)^2 by positivity)
  have hn :
      (319411 : ℝ) / 1000000000000000000 ≤
        ((520 : ℝ)/512)^2 *
          (30965914909/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (65/64 : ℝ) = ((520 : ℝ)/512) := by
    norm_num
  have hright :
      (521/512 : ℝ) = (((( 520+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((520 : ℝ)/512)^2 *
        (30965914909/100000000000000000000000 : ℝ) ≤
      ((520 : ℝ)/512)^2 *
        (∫ x in (((520 : ℝ)/512))..((((520+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_521 :
    (300140 : ℝ) / 1000000000000000000 ≤
      ((521 : ℝ)/512)^2 *
        (∫ x in (((521 : ℝ)/512))..((((521+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_521).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((521 : ℝ)/512)^2 by positivity)
  have hn :
      (300140 : ℝ) / 1000000000000000000 ≤
        ((521 : ℝ)/512)^2 *
          (5797213289/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (521/512 : ℝ) = ((521 : ℝ)/512) := by
    norm_num
  have hright :
      (261/256 : ℝ) = (((( 521+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((521 : ℝ)/512)^2 *
        (5797213289/20000000000000000000000 : ℝ) ≤
      ((521 : ℝ)/512)^2 *
        (∫ x in (((521 : ℝ)/512))..((((521+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_522 :
    (281912 : ℝ) / 1000000000000000000 ≤
      ((522 : ℝ)/512)^2 *
        (∫ x in (((522 : ℝ)/512))..((((522+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_522).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((522 : ℝ)/512)^2 by positivity)
  have hn :
      (281912 : ℝ) / 1000000000000000000 ≤
        ((522 : ℝ)/512)^2 *
          (2712143449/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (261/256 : ℝ) = ((522 : ℝ)/512) := by
    norm_num
  have hright :
      (523/512 : ℝ) = (((( 522+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((522 : ℝ)/512)^2 *
        (2712143449/10000000000000000000000 : ℝ) ≤
      ((522 : ℝ)/512)^2 *
        (∫ x in (((522 : ℝ)/512))..((((522+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_523 :
    (264677 : ℝ) / 1000000000000000000 ≤
      ((523 : ℝ)/512)^2 *
        (∫ x in (((523 : ℝ)/512))..((((523+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_523).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((523 : ℝ)/512)^2 by positivity)
  have hn :
      (264677 : ℝ) / 1000000000000000000 ≤
        ((523 : ℝ)/512)^2 *
          (6341522007/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (523/512 : ℝ) = ((523 : ℝ)/512) := by
    norm_num
  have hright :
      (131/128 : ℝ) = (((( 523+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((523 : ℝ)/512)^2 *
        (6341522007/25000000000000000000000 : ℝ) ≤
      ((523 : ℝ)/512)^2 *
        (∫ x in (((523 : ℝ)/512))..((((523+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_524 :
    (248389 : ℝ) / 1000000000000000000 ≤
      ((524 : ℝ)/512)^2 *
        (∫ x in (((524 : ℝ)/512))..((((524+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_524).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((524 : ℝ)/512)^2 by positivity)
  have hn :
      (248389 : ℝ) / 1000000000000000000 ≤
        ((524 : ℝ)/512)^2 *
          (23714351797/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (131/128 : ℝ) = ((524 : ℝ)/512) := by
    norm_num
  have hright :
      (525/512 : ℝ) = (((( 524+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((524 : ℝ)/512)^2 *
        (23714351797/100000000000000000000000 : ℝ) ≤
      ((524 : ℝ)/512)^2 *
        (∫ x in (((524 : ℝ)/512))..((((524+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_525 :
    (233004 : ℝ) / 1000000000000000000 ≤
      ((525 : ℝ)/512)^2 *
        (∫ x in (((525 : ℝ)/512))..((((525+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_525).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((525 : ℝ)/512)^2 by positivity)
  have hn :
      (233004 : ℝ) / 1000000000000000000 ≤
        ((525 : ℝ)/512)^2 *
          (11080399127/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (525/512 : ℝ) = ((525 : ℝ)/512) := by
    norm_num
  have hright :
      (263/256 : ℝ) = (((( 525+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((525 : ℝ)/512)^2 *
        (11080399127/50000000000000000000000 : ℝ) ≤
      ((525 : ℝ)/512)^2 *
        (∫ x in (((525 : ℝ)/512))..((((525+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_526 :
    (218477 : ℝ) / 1000000000000000000 ≤
      ((526 : ℝ)/512)^2 *
        (∫ x in (((526 : ℝ)/512))..((((526+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_526).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((526 : ℝ)/512)^2 by positivity)
  have hn :
      (218477 : ℝ) / 1000000000000000000 ≤
        ((526 : ℝ)/512)^2 *
          (5175059903/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (263/256 : ℝ) = ((526 : ℝ)/512) := by
    norm_num
  have hright :
      (527/512 : ℝ) = (((( 526+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((526 : ℝ)/512)^2 *
        (5175059903/25000000000000000000000 : ℝ) ≤
      ((526 : ℝ)/512)^2 *
        (∫ x in (((526 : ℝ)/512))..((((526+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_527 :
    (204767 : ℝ) / 1000000000000000000 ≤
      ((527 : ℝ)/512)^2 *
        (∫ x in (((527 : ℝ)/512))..((((527+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_527).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((527 : ℝ)/512)^2 by positivity)
  have hn :
      (204767 : ℝ) / 1000000000000000000 ≤
        ((527 : ℝ)/512)^2 *
          (9663859987/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (527/512 : ℝ) = ((527 : ℝ)/512) := by
    norm_num
  have hright :
      (33/32 : ℝ) = (((( 527+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((527 : ℝ)/512)^2 *
        (9663859987/50000000000000000000000 : ℝ) ≤
      ((527 : ℝ)/512)^2 *
        (∫ x in (((527 : ℝ)/512))..((((527+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_528 :
    (191835 : ℝ) / 1000000000000000000 ≤
      ((528 : ℝ)/512)^2 *
        (∫ x in (((528 : ℝ)/512))..((((528+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_528).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((528 : ℝ)/512)^2 by positivity)
  have hn :
      (191835 : ℝ) / 1000000000000000000 ≤
        ((528 : ℝ)/512)^2 *
          (3607701511/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (33/32 : ℝ) = ((528 : ℝ)/512) := by
    norm_num
  have hright :
      (529/512 : ℝ) = (((( 528+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((528 : ℝ)/512)^2 *
        (3607701511/20000000000000000000000 : ℝ) ≤
      ((528 : ℝ)/512)^2 *
        (∫ x in (((528 : ℝ)/512))..((((528+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_529 :
    (179641 : ℝ) / 1000000000000000000 ≤
      ((529 : ℝ)/512)^2 *
        (∫ x in (((529 : ℝ)/512))..((((529+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_529).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((529 : ℝ)/512)^2 by positivity)
  have hn :
      (179641 : ℝ) / 1000000000000000000 ≤
        ((529 : ℝ)/512)^2 *
          (16828087021/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (529/512 : ℝ) = ((529 : ℝ)/512) := by
    norm_num
  have hright :
      (265/256 : ℝ) = (((( 529+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((529 : ℝ)/512)^2 *
        (16828087021/100000000000000000000000 : ℝ) ≤
      ((529 : ℝ)/512)^2 *
        (∫ x in (((529 : ℝ)/512))..((((529+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_530 :
    (168149 : ℝ) / 1000000000000000000 ≤
      ((530 : ℝ)/512)^2 *
        (∫ x in (((530 : ℝ)/512))..((((530+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_530).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((530 : ℝ)/512)^2 by positivity)
  have hn :
      (168149 : ℝ) / 1000000000000000000 ≤
        ((530 : ℝ)/512)^2 *
          (122594937/781250000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (265/256 : ℝ) = ((530 : ℝ)/512) := by
    norm_num
  have hright :
      (531/512 : ℝ) = (((( 530+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((530 : ℝ)/512)^2 *
        (122594937/781250000000000000000 : ℝ) ≤
      ((530 : ℝ)/512)^2 *
        (∫ x in (((530 : ℝ)/512))..((((530+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_531 :
    (157323 : ℝ) / 1000000000000000000 ≤
      ((531 : ℝ)/512)^2 *
        (∫ x in (((531 : ℝ)/512))..((((531+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_531).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((531 : ℝ)/512)^2 by positivity)
  have hn :
      (157323 : ℝ) / 1000000000000000000 ≤
        ((531 : ℝ)/512)^2 *
          (3656649333/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (531/512 : ℝ) = ((531 : ℝ)/512) := by
    norm_num
  have hright :
      (133/128 : ℝ) = (((( 531+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((531 : ℝ)/512)^2 *
        (3656649333/25000000000000000000000 : ℝ) ≤
      ((531 : ℝ)/512)^2 *
        (∫ x in (((531 : ℝ)/512))..((((531+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_532 :
    (147129 : ℝ) / 1000000000000000000 ≤
      ((532 : ℝ)/512)^2 *
        (∫ x in (((532 : ℝ)/512))..((((532+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_532).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((532 : ℝ)/512)^2 by positivity)
  have hn :
      (147129 : ℝ) / 1000000000000000000 ≤
        ((532 : ℝ)/512)^2 *
          (13627512419/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (133/128 : ℝ) = ((532 : ℝ)/512) := by
    norm_num
  have hright :
      (533/512 : ℝ) = (((( 532+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((532 : ℝ)/512)^2 *
        (13627512419/100000000000000000000000 : ℝ) ≤
      ((532 : ℝ)/512)^2 *
        (∫ x in (((532 : ℝ)/512))..((((532+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_533 :
    (137535 : ℝ) / 1000000000000000000 ≤
      ((533 : ℝ)/512)^2 *
        (∫ x in (((533 : ℝ)/512))..((((533+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_533).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((533 : ℝ)/512)^2 by positivity)
  have hn :
      (137535 : ℝ) / 1000000000000000000 ≤
        ((533 : ℝ)/512)^2 *
          (2538234683/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (533/512 : ℝ) = ((533 : ℝ)/512) := by
    norm_num
  have hright :
      (267/256 : ℝ) = (((( 533+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((533 : ℝ)/512)^2 *
        (2538234683/20000000000000000000000 : ℝ) ≤
      ((533 : ℝ)/512)^2 *
        (∫ x in (((533 : ℝ)/512))..((((533+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_534 :
    (128511 : ℝ) / 1000000000000000000 ≤
      ((534 : ℝ)/512)^2 *
        (∫ x in (((534 : ℝ)/512))..((((534+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_534).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((534 : ℝ)/512)^2 by positivity)
  have hn :
      (128511 : ℝ) / 1000000000000000000 ≤
        ((534 : ℝ)/512)^2 *
          (11814036533/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (267/256 : ℝ) = ((534 : ℝ)/512) := by
    norm_num
  have hright :
      (535/512 : ℝ) = (((( 534+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((534 : ℝ)/512)^2 *
        (11814036533/100000000000000000000000 : ℝ) ≤
      ((534 : ℝ)/512)^2 *
        (∫ x in (((534 : ℝ)/512))..((((534+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_535 :
    (120025 : ℝ) / 1000000000000000000 ≤
      ((535 : ℝ)/512)^2 *
        (∫ x in (((535 : ℝ)/512))..((((535+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_535).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((535 : ℝ)/512)^2 by positivity)
  have hn :
      (120025 : ℝ) / 1000000000000000000 ≤
        ((535 : ℝ)/512)^2 *
          (10992731107/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (535/512 : ℝ) = ((535 : ℝ)/512) := by
    norm_num
  have hright :
      (67/64 : ℝ) = (((( 535+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((535 : ℝ)/512)^2 *
        (10992731107/100000000000000000000000 : ℝ) ≤
      ((535 : ℝ)/512)^2 *
        (∫ x in (((535 : ℝ)/512))..((((535+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_536 :
    (112050 : ℝ) / 1000000000000000000 ≤
      ((536 : ℝ)/512)^2 *
        (∫ x in (((536 : ℝ)/512))..((((536+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_536).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((536 : ℝ)/512)^2 by positivity)
  have hn :
      (112050 : ℝ) / 1000000000000000000 ≤
        ((536 : ℝ)/512)^2 *
          (2044810573/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (67/64 : ℝ) = ((536 : ℝ)/512) := by
    norm_num
  have hright :
      (537/512 : ℝ) = (((( 536+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((536 : ℝ)/512)^2 *
        (2044810573/20000000000000000000000 : ℝ) ≤
      ((536 : ℝ)/512)^2 *
        (∫ x in (((536 : ℝ)/512))..((((536+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_537 :
    (104558 : ℝ) / 1000000000000000000 ≤
      ((537 : ℝ)/512)^2 *
        (∫ x in (((537 : ℝ)/512))..((((537+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_537).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((537 : ℝ)/512)^2 by positivity)
  have hn :
      (104558 : ℝ) / 1000000000000000000 ≤
        ((537 : ℝ)/512)^2 *
          (9504957371/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (537/512 : ℝ) = ((537 : ℝ)/512) := by
    norm_num
  have hright :
      (269/256 : ℝ) = (((( 537+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((537 : ℝ)/512)^2 *
        (9504957371/100000000000000000000000 : ℝ) ≤
      ((537 : ℝ)/512)^2 *
        (∫ x in (((537 : ℝ)/512))..((((537+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_538 :
    (97523 : ℝ) / 1000000000000000000 ≤
      ((538 : ℝ)/512)^2 *
        (∫ x in (((538 : ℝ)/512))..((((538+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_538).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((538 : ℝ)/512)^2 by positivity)
  have hn :
      (97523 : ℝ) / 1000000000000000000 ≤
        ((538 : ℝ)/512)^2 *
          (1766510721/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (269/256 : ℝ) = ((538 : ℝ)/512) := by
    norm_num
  have hright :
      (539/512 : ℝ) = (((( 538+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((538 : ℝ)/512)^2 *
        (1766510721/20000000000000000000000 : ℝ) ≤
      ((538 : ℝ)/512)^2 *
        (∫ x in (((538 : ℝ)/512))..((((538+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_539 :
    (90921 : ℝ) / 1000000000000000000 ≤
      ((539 : ℝ)/512)^2 *
        (∫ x in (((539 : ℝ)/512))..((((539+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_539).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((539 : ℝ)/512)^2 by positivity)
  have hn :
      (90921 : ℝ) / 1000000000000000000 ≤
        ((539 : ℝ)/512)^2 *
          (4102048861/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (539/512 : ℝ) = ((539 : ℝ)/512) := by
    norm_num
  have hright :
      (135/128 : ℝ) = (((( 539+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((539 : ℝ)/512)^2 *
        (4102048861/50000000000000000000000 : ℝ) ≤
      ((539 : ℝ)/512)^2 *
        (∫ x in (((539 : ℝ)/512))..((((539+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_540 :
    (84728 : ℝ) / 1000000000000000000 ≤
      ((540 : ℝ)/512)^2 *
        (∫ x in (((540 : ℝ)/512))..((((540+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_540).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((540 : ℝ)/512)^2 by positivity)
  have hn :
      (84728 : ℝ) / 1000000000000000000 ≤
        ((540 : ℝ)/512)^2 *
          (95212337/1250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (135/128 : ℝ) = ((540 : ℝ)/512) := by
    norm_num
  have hright :
      (541/512 : ℝ) = (((( 540+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((540 : ℝ)/512)^2 *
        (95212337/1250000000000000000000 : ℝ) ≤
      ((540 : ℝ)/512)^2 *
        (∫ x in (((540 : ℝ)/512))..((((540+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_541 :
    (78921 : ℝ) / 1000000000000000000 ≤
      ((541 : ℝ)/512)^2 *
        (∫ x in (((541 : ℝ)/512))..((((541+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_541).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((541 : ℝ)/512)^2 by positivity)
  have hn :
      (78921 : ℝ) / 1000000000000000000 ≤
        ((541 : ℝ)/512)^2 *
          (7068753721/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (541/512 : ℝ) = ((541 : ℝ)/512) := by
    norm_num
  have hright :
      (271/256 : ℝ) = (((( 541+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((541 : ℝ)/512)^2 *
        (7068753721/100000000000000000000000 : ℝ) ≤
      ((541 : ℝ)/512)^2 *
        (∫ x in (((541 : ℝ)/512))..((((541+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_542 :
    (73479 : ℝ) / 1000000000000000000 ≤
      ((542 : ℝ)/512)^2 *
        (∫ x in (((542 : ℝ)/512))..((((542+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_542).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((542 : ℝ)/512)^2 by positivity)
  have hn :
      (73479 : ℝ) / 1000000000000000000 ≤
        ((542 : ℝ)/512)^2 *
          (204908119/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (271/256 : ℝ) = ((542 : ℝ)/512) := by
    norm_num
  have hright :
      (543/512 : ℝ) = (((( 542+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((542 : ℝ)/512)^2 *
        (204908119/3125000000000000000000 : ℝ) ≤
      ((542 : ℝ)/512)^2 *
        (∫ x in (((542 : ℝ)/512))..((((542+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_543 :
    (68381 : ℝ) / 1000000000000000000 ≤
      ((543 : ℝ)/512)^2 *
        (∫ x in (((543 : ℝ)/512))..((((543+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_543).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((543 : ℝ)/512)^2 by positivity)
  have hn :
      (68381 : ℝ) / 1000000000000000000 ≤
        ((543 : ℝ)/512)^2 *
          (6079690837/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (543/512 : ℝ) = ((543 : ℝ)/512) := by
    norm_num
  have hright :
      (17/16 : ℝ) = (((( 543+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((543 : ℝ)/512)^2 *
        (6079690837/100000000000000000000000 : ℝ) ≤
      ((543 : ℝ)/512)^2 *
        (∫ x in (((543 : ℝ)/512))..((((543+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
