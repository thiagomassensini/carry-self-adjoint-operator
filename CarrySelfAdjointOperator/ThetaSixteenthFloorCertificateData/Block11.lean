import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_11
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_352 :
    (54889218 : ℝ) / 1000000000000000000 ≤
      ((352 : ℝ)/512)^2 *
        (∫ x in (((352 : ℝ)/512))..((((352+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_352).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((352 : ℝ)/512)^2 by positivity)
  have hn :
      (54889218 : ℝ) / 1000000000000000000 ≤
        ((352 : ℝ)/512)^2 *
          (464517025181/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (11/16 : ℝ) = ((352 : ℝ)/512) := by
    norm_num
  have hright :
      (353/512 : ℝ) = (((( 352+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((352 : ℝ)/512)^2 *
        (464517025181/4000000000000000000000 : ℝ) ≤
      ((352 : ℝ)/512)^2 *
        (∫ x in (((352 : ℝ)/512))..((((352+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_353 :
    (54756794 : ℝ) / 1000000000000000000 ≤
      ((353 : ℝ)/512)^2 *
        (∫ x in (((353 : ℝ)/512))..((((353+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_353).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((353 : ℝ)/512)^2 by positivity)
  have hn :
      (54756794 : ℝ) / 1000000000000000000 ≤
        ((353 : ℝ)/512)^2 *
          (11519364709023/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (353/512 : ℝ) = ((353 : ℝ)/512) := by
    norm_num
  have hright :
      (177/256 : ℝ) = (((( 353+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((353 : ℝ)/512)^2 *
        (11519364709023/100000000000000000000000 : ℝ) ≤
      ((353 : ℝ)/512)^2 *
        (∫ x in (((353 : ℝ)/512))..((((353+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_354 :
    (54607279 : ℝ) / 1000000000000000000 ≤
      ((354 : ℝ)/512)^2 *
        (∫ x in (((354 : ℝ)/512))..((((354+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_354).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((354 : ℝ)/512)^2 by positivity)
  have hn :
      (54607279 : ℝ) / 1000000000000000000 ≤
        ((354 : ℝ)/512)^2 *
          (1142309887207/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (177/256 : ℝ) = ((354 : ℝ)/512) := by
    norm_num
  have hright :
      (355/512 : ℝ) = (((( 354+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((354 : ℝ)/512)^2 *
        (1142309887207/10000000000000000000000 : ℝ) ≤
      ((354 : ℝ)/512)^2 *
        (∫ x in (((354 : ℝ)/512))..((((354+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_355 :
    (54440812 : ℝ) / 1000000000000000000 ≤
      ((355 : ℝ)/512)^2 *
        (∫ x in (((355 : ℝ)/512))..((((355+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_355).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((355 : ℝ)/512)^2 by positivity)
  have hn :
      (54440812 : ℝ) / 1000000000000000000 ≤
        ((355 : ℝ)/512)^2 *
          (11324207452411/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (355/512 : ℝ) = ((355 : ℝ)/512) := by
    norm_num
  have hright :
      (89/128 : ℝ) = (((( 355+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((355 : ℝ)/512)^2 *
        (11324207452411/100000000000000000000000 : ℝ) ≤
      ((355 : ℝ)/512)^2 *
        (∫ x in (((355 : ℝ)/512))..((((355+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_356 :
    (54257551 : ℝ) / 1000000000000000000 ≤
      ((356 : ℝ)/512)^2 *
        (∫ x in (((356 : ℝ)/512))..((((356+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_356).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((356 : ℝ)/512)^2 by positivity)
  have hn :
      (54257551 : ℝ) / 1000000000000000000 ≤
        ((356 : ℝ)/512)^2 *
          (224455428499/2000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (89/128 : ℝ) = ((356 : ℝ)/512) := by
    norm_num
  have hright :
      (357/512 : ℝ) = (((( 356+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((356 : ℝ)/512)^2 *
        (224455428499/2000000000000000000000 : ℝ) ≤
      ((356 : ℝ)/512)^2 *
        (∫ x in (((356 : ℝ)/512))..((((356+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_357 :
    (54057666 : ℝ) / 1000000000000000000 ≤
      ((357 : ℝ)/512)^2 *
        (∫ x in (((357 : ℝ)/512))..((((357+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_357).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((357 : ℝ)/512)^2 by positivity)
  have hn :
      (54057666 : ℝ) / 1000000000000000000 ≤
        ((357 : ℝ)/512)^2 *
          (2779718324889/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (357/512 : ℝ) = ((357 : ℝ)/512) := by
    norm_num
  have hright :
      (179/256 : ℝ) = (((( 357+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((357 : ℝ)/512)^2 *
        (2779718324889/25000000000000000000000 : ℝ) ≤
      ((357 : ℝ)/512)^2 *
        (∫ x in (((357 : ℝ)/512))..((((357+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_358 :
    (53841342 : ℝ) / 1000000000000000000 ≤
      ((358 : ℝ)/512)^2 *
        (∫ x in (((358 : ℝ)/512))..((((358+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_358).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((358 : ℝ)/512)^2 by positivity)
  have hn :
      (53841342 : ℝ) / 1000000000000000000 ≤
        ((358 : ℝ)/512)^2 *
          (1101259701357/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (179/256 : ℝ) = ((358 : ℝ)/512) := by
    norm_num
  have hright :
      (359/512 : ℝ) = (((( 358+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((358 : ℝ)/512)^2 *
        (1101259701357/10000000000000000000000 : ℝ) ≤
      ((358 : ℝ)/512)^2 *
        (∫ x in (((358 : ℝ)/512))..((((358+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_359 :
    (53608780 : ℝ) / 1000000000000000000 ≤
      ((359 : ℝ)/512)^2 *
        (∫ x in (((359 : ℝ)/512))..((((359+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_359).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((359 : ℝ)/512)^2 by positivity)
  have hn :
      (53608780 : ℝ) / 1000000000000000000 ≤
        ((359 : ℝ)/512)^2 *
          (10904027823183/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (359/512 : ℝ) = ((359 : ℝ)/512) := by
    norm_num
  have hright :
      (45/64 : ℝ) = (((( 359+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((359 : ℝ)/512)^2 *
        (10904027823183/100000000000000000000000 : ℝ) ≤
      ((359 : ℝ)/512)^2 *
        (∫ x in (((359 : ℝ)/512))..((((359+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_360 :
    (53360194 : ℝ) / 1000000000000000000 ≤
      ((360 : ℝ)/512)^2 *
        (∫ x in (((360 : ℝ)/512))..((((360+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_360).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((360 : ℝ)/512)^2 by positivity)
  have hn :
      (53360194 : ℝ) / 1000000000000000000 ≤
        ((360 : ℝ)/512)^2 *
          (337289131059/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (45/64 : ℝ) = ((360 : ℝ)/512) := by
    norm_num
  have hright :
      (361/512 : ℝ) = (((( 360+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((360 : ℝ)/512)^2 *
        (337289131059/3125000000000000000000 : ℝ) ≤
      ((360 : ℝ)/512)^2 *
        (∫ x in (((360 : ℝ)/512))..((((360+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_361 :
    (53095813 : ℝ) / 1000000000000000000 ≤
      ((361 : ℝ)/512)^2 *
        (∫ x in (((361 : ℝ)/512))..((((361+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_361).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((361 : ℝ)/512)^2 by positivity)
  have hn :
      (53095813 : ℝ) / 1000000000000000000 ≤
        ((361 : ℝ)/512)^2 *
          (1068035769019/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (361/512 : ℝ) = ((361 : ℝ)/512) := by
    norm_num
  have hright :
      (181/256 : ℝ) = (((( 361+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((361 : ℝ)/512)^2 *
        (1068035769019/10000000000000000000000 : ℝ) ≤
      ((361 : ℝ)/512)^2 *
        (∫ x in (((361 : ℝ)/512))..((((361+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_362 :
    (52815879 : ℝ) / 1000000000000000000 ≤
      ((362 : ℝ)/512)^2 *
        (∫ x in (((362 : ℝ)/512))..((((362+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_362).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((362 : ℝ)/512)^2 by positivity)
  have hn :
      (52815879 : ℝ) / 1000000000000000000 ≤
        ((362 : ℝ)/512)^2 *
          (2579451383/24414062500000000000 : ℝ) := by
    norm_num
  have hleft :
      (181/256 : ℝ) = ((362 : ℝ)/512) := by
    norm_num
  have hright :
      (363/512 : ℝ) = (((( 362+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((362 : ℝ)/512)^2 *
        (2579451383/24414062500000000000 : ℝ) ≤
      ((362 : ℝ)/512)^2 *
        (∫ x in (((362 : ℝ)/512))..((((362+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_363 :
    (52520646 : ℝ) / 1000000000000000000 ≤
      ((363 : ℝ)/512)^2 *
        (∫ x in (((363 : ℝ)/512))..((((363+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_363).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((363 : ℝ)/512)^2 by positivity)
  have hn :
      (52520646 : ℝ) / 1000000000000000000 ≤
        ((363 : ℝ)/512)^2 *
          (5224283573633/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (363/512 : ℝ) = ((363 : ℝ)/512) := by
    norm_num
  have hright :
      (91/128 : ℝ) = (((( 363+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((363 : ℝ)/512)^2 *
        (5224283573633/50000000000000000000000 : ℝ) ≤
      ((363 : ℝ)/512)^2 *
        (∫ x in (((363 : ℝ)/512))..((((363+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_364 :
    (52210384 : ℝ) / 1000000000000000000 ≤
      ((364 : ℝ)/512)^2 *
        (∫ x in (((364 : ℝ)/512))..((((364+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_364).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((364 : ℝ)/512)^2 by positivity)
  have hn :
      (52210384 : ℝ) / 1000000000000000000 ≤
        ((364 : ℝ)/512)^2 *
          (5164925366459/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (91/128 : ℝ) = ((364 : ℝ)/512) := by
    norm_num
  have hright :
      (365/512 : ℝ) = (((( 364+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((364 : ℝ)/512)^2 *
        (5164925366459/50000000000000000000000 : ℝ) ≤
      ((364 : ℝ)/512)^2 *
        (∫ x in (((364 : ℝ)/512))..((((364+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_365 :
    (51885372 : ℝ) / 1000000000000000000 ≤
      ((365 : ℝ)/512)^2 *
        (∫ x in (((365 : ℝ)/512))..((((365+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_365).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((365 : ℝ)/512)^2 by positivity)
  have hn :
      (51885372 : ℝ) / 1000000000000000000 ≤
        ((365 : ℝ)/512)^2 *
          (5104687235593/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (365/512 : ℝ) = ((365 : ℝ)/512) := by
    norm_num
  have hright :
      (183/256 : ℝ) = (((( 365+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((365 : ℝ)/512)^2 *
        (5104687235593/50000000000000000000000 : ℝ) ≤
      ((365 : ℝ)/512)^2 *
        (∫ x in (((365 : ℝ)/512))..((((365+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_366 :
    (51545904 : ℝ) / 1000000000000000000 ≤
      ((366 : ℝ)/512)^2 *
        (∫ x in (((366 : ℝ)/512))..((((366+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_366).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((366 : ℝ)/512)^2 by positivity)
  have hn :
      (51545904 : ℝ) / 1000000000000000000 ≤
        ((366 : ℝ)/512)^2 *
          (2521807438649/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (183/256 : ℝ) = ((366 : ℝ)/512) := by
    norm_num
  have hright :
      (367/512 : ℝ) = (((( 366+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((366 : ℝ)/512)^2 *
        (2521807438649/25000000000000000000000 : ℝ) ≤
      ((366 : ℝ)/512)^2 *
        (∫ x in (((366 : ℝ)/512))..((((366+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_367 :
    (51192283 : ℝ) / 1000000000000000000 ≤
      ((367 : ℝ)/512)^2 *
        (∫ x in (((367 : ℝ)/512))..((((367+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_367).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((367 : ℝ)/512)^2 by positivity)
  have hn :
      (51192283 : ℝ) / 1000000000000000000 ≤
        ((367 : ℝ)/512)^2 *
          (9963508407949/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (367/512 : ℝ) = ((367 : ℝ)/512) := by
    norm_num
  have hright :
      (23/32 : ℝ) = (((( 367+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((367 : ℝ)/512)^2 *
        (9963508407949/100000000000000000000000 : ℝ) ≤
      ((367 : ℝ)/512)^2 *
        (∫ x in (((367 : ℝ)/512))..((((367+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_368 :
    (50824824 : ℝ) / 1000000000000000000 ≤
      ((368 : ℝ)/512)^2 *
        (∫ x in (((368 : ℝ)/512))..((((368+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_368).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((368 : ℝ)/512)^2 by positivity)
  have hn :
      (50824824 : ℝ) / 1000000000000000000 ≤
        ((368 : ℝ)/512)^2 *
          (1967660515621/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (23/32 : ℝ) = ((368 : ℝ)/512) := by
    norm_num
  have hright :
      (369/512 : ℝ) = (((( 368+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((368 : ℝ)/512)^2 *
        (1967660515621/20000000000000000000000 : ℝ) ≤
      ((368 : ℝ)/512)^2 *
        (∫ x in (((368 : ℝ)/512))..((((368+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_369 :
    (50443855 : ℝ) / 1000000000000000000 ≤
      ((369 : ℝ)/512)^2 *
        (∫ x in (((369 : ℝ)/512))..((((369+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_369).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((369 : ℝ)/512)^2 by positivity)
  have hn :
      (50443855 : ℝ) / 1000000000000000000 ≤
        ((369 : ℝ)/512)^2 *
          (1942340924901/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (369/512 : ℝ) = ((369 : ℝ)/512) := by
    norm_num
  have hright :
      (185/256 : ℝ) = (((( 369+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((369 : ℝ)/512)^2 *
        (1942340924901/20000000000000000000000 : ℝ) ≤
      ((369 : ℝ)/512)^2 *
        (∫ x in (((369 : ℝ)/512))..((((369+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_370 :
    (50049712 : ℝ) / 1000000000000000000 ≤
      ((370 : ℝ)/512)^2 *
        (∫ x in (((370 : ℝ)/512))..((((370+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_370).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((370 : ℝ)/512)^2 by positivity)
  have hn :
      (50049712 : ℝ) / 1000000000000000000 ≤
        ((370 : ℝ)/512)^2 *
          (47919035053/500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (185/256 : ℝ) = ((370 : ℝ)/512) := by
    norm_num
  have hright :
      (371/512 : ℝ) = (((( 370+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((370 : ℝ)/512)^2 *
        (47919035053/500000000000000000000 : ℝ) ≤
      ((370 : ℝ)/512)^2 *
        (∫ x in (((370 : ℝ)/512))..((((370+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_371 :
    (49642740 : ℝ) / 1000000000000000000 ≤
      ((371 : ℝ)/512)^2 *
        (∫ x in (((371 : ℝ)/512))..((((371+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_371).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((371 : ℝ)/512)^2 by positivity)
  have hn :
      (49642740 : ℝ) / 1000000000000000000 ≤
        ((371 : ℝ)/512)^2 *
          (472735109819/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (371/512 : ℝ) = ((371 : ℝ)/512) := by
    norm_num
  have hright :
      (93/128 : ℝ) = (((( 371+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((371 : ℝ)/512)^2 *
        (472735109819/5000000000000000000000 : ℝ) ≤
      ((371 : ℝ)/512)^2 *
        (∫ x in (((371 : ℝ)/512))..((((371+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_372 :
    (49223296 : ℝ) / 1000000000000000000 ≤
      ((372 : ℝ)/512)^2 *
        (∫ x in (((372 : ℝ)/512))..((((372+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_372).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((372 : ℝ)/512)^2 by positivity)
  have hn :
      (49223296 : ℝ) / 1000000000000000000 ≤
        ((372 : ℝ)/512)^2 *
          (1864896506429/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (93/128 : ℝ) = ((372 : ℝ)/512) := by
    norm_num
  have hright :
      (373/512 : ℝ) = (((( 372+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((372 : ℝ)/512)^2 *
        (1864896506429/20000000000000000000000 : ℝ) ≤
      ((372 : ℝ)/512)^2 *
        (∫ x in (((372 : ℝ)/512))..((((372+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_373 :
    (48791744 : ℝ) / 1000000000000000000 ≤
      ((373 : ℝ)/512)^2 *
        (∫ x in (((373 : ℝ)/512))..((((373+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_373).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((373 : ℝ)/512)^2 by positivity)
  have hn :
      (48791744 : ℝ) / 1000000000000000000 ≤
        ((373 : ℝ)/512)^2 *
          (4596620076851/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (373/512 : ℝ) = ((373 : ℝ)/512) := by
    norm_num
  have hright :
      (187/256 : ℝ) = (((( 373+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((373 : ℝ)/512)^2 *
        (4596620076851/50000000000000000000000 : ℝ) ≤
      ((373 : ℝ)/512)^2 *
        (∫ x in (((373 : ℝ)/512))..((((373+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_374 :
    (48348456 : ℝ) / 1000000000000000000 ≤
      ((374 : ℝ)/512)^2 *
        (∫ x in (((374 : ℝ)/512))..((((374+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_374).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((374 : ℝ)/512)^2 by positivity)
  have hn :
      (48348456 : ℝ) / 1000000000000000000 ≤
        ((374 : ℝ)/512)^2 *
          (9061066879131/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (187/256 : ℝ) = ((374 : ℝ)/512) := by
    norm_num
  have hright :
      (375/512 : ℝ) = (((( 374+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((374 : ℝ)/512)^2 *
        (9061066879131/100000000000000000000000 : ℝ) ≤
      ((374 : ℝ)/512)^2 *
        (∫ x in (((374 : ℝ)/512))..((((374+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_375 :
    (47893814 : ℝ) / 1000000000000000000 ≤
      ((375 : ℝ)/512)^2 *
        (∫ x in (((375 : ℝ)/512))..((((375+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_375).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((375 : ℝ)/512)^2 by positivity)
  have hn :
      (47893814 : ℝ) / 1000000000000000000 ≤
        ((375 : ℝ)/512)^2 *
          (1116006763411/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (375/512 : ℝ) = ((375 : ℝ)/512) := by
    norm_num
  have hright :
      (47/64 : ℝ) = (((( 375+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((375 : ℝ)/512)^2 *
        (1116006763411/12500000000000000000000 : ℝ) ≤
      ((375 : ℝ)/512)^2 *
        (∫ x in (((375 : ℝ)/512))..((((375+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_376 :
    (47428204 : ℝ) / 1000000000000000000 ≤
      ((376 : ℝ)/512)^2 *
        (∫ x in (((376 : ℝ)/512))..((((376+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_376).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((376 : ℝ)/512)^2 by positivity)
  have hn :
      (47428204 : ℝ) / 1000000000000000000 ≤
        ((376 : ℝ)/512)^2 *
          (8794292718179/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (47/64 : ℝ) = ((376 : ℝ)/512) := by
    norm_num
  have hright :
      (377/512 : ℝ) = (((( 376+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((376 : ℝ)/512)^2 *
        (8794292718179/100000000000000000000000 : ℝ) ≤
      ((376 : ℝ)/512)^2 *
        (∫ x in (((376 : ℝ)/512))..((((376+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_377 :
    (46952022 : ℝ) / 1000000000000000000 ≤
      ((377 : ℝ)/512)^2 *
        (∫ x in (((377 : ℝ)/512))..((((377+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_377).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((377 : ℝ)/512)^2 by positivity)
  have hn :
      (46952022 : ℝ) / 1000000000000000000 ≤
        ((377 : ℝ)/512)^2 *
          (8659872975361/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (377/512 : ℝ) = ((377 : ℝ)/512) := by
    norm_num
  have hright :
      (189/256 : ℝ) = (((( 377+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((377 : ℝ)/512)^2 *
        (8659872975361/100000000000000000000000 : ℝ) ≤
      ((377 : ℝ)/512)^2 *
        (∫ x in (((377 : ℝ)/512))..((((377+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_378 :
    (46465667 : ℝ) / 1000000000000000000 ≤
      ((378 : ℝ)/512)^2 *
        (∫ x in (((378 : ℝ)/512))..((((378+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_378).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((378 : ℝ)/512)^2 by positivity)
  have hn :
      (46465667 : ℝ) / 1000000000000000000 ≤
        ((378 : ℝ)/512)^2 *
          (8524884430503/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (189/256 : ℝ) = ((378 : ℝ)/512) := by
    norm_num
  have hright :
      (379/512 : ℝ) = (((( 378+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((378 : ℝ)/512)^2 *
        (8524884430503/100000000000000000000000 : ℝ) ≤
      ((378 : ℝ)/512)^2 *
        (∫ x in (((378 : ℝ)/512))..((((378+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_379 :
    (45969546 : ℝ) / 1000000000000000000 ≤
      ((379 : ℝ)/512)^2 *
        (∫ x in (((379 : ℝ)/512))..((((379+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_379).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((379 : ℝ)/512)^2 by positivity)
  have hn :
      (45969546 : ℝ) / 1000000000000000000 ≤
        ((379 : ℝ)/512)^2 *
          (2097353957559/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (379/512 : ℝ) = ((379 : ℝ)/512) := by
    norm_num
  have hright :
      (95/128 : ℝ) = (((( 379+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((379 : ℝ)/512)^2 *
        (2097353957559/25000000000000000000000 : ℝ) ≤
      ((379 : ℝ)/512)^2 *
        (∫ x in (((379 : ℝ)/512))..((((379+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_380 :
    (45464071 : ℝ) / 1000000000000000000 ≤
      ((380 : ℝ)/512)^2 *
        (∫ x in (((380 : ℝ)/512))..((((380+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_380).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((380 : ℝ)/512)^2 by positivity)
  have hn :
      (45464071 : ℝ) / 1000000000000000000 ≤
        ((380 : ℝ)/512)^2 *
          (330142201017/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (95/128 : ℝ) = ((380 : ℝ)/512) := by
    norm_num
  have hright :
      (381/512 : ℝ) = (((( 380+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((380 : ℝ)/512)^2 *
        (330142201017/4000000000000000000000 : ℝ) ≤
      ((380 : ℝ)/512)^2 *
        (∫ x in (((380 : ℝ)/512))..((((380+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_381 :
    (44949656 : ℝ) / 1000000000000000000 ≤
      ((381 : ℝ)/512)^2 *
        (∫ x in (((381 : ℝ)/512))..((((381+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_381).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((381 : ℝ)/512)^2 by positivity)
  have hn :
      (44949656 : ℝ) / 1000000000000000000 ≤
        ((381 : ℝ)/512)^2 *
          (253668402593/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (381/512 : ℝ) = ((381 : ℝ)/512) := by
    norm_num
  have hright :
      (191/256 : ℝ) = (((( 381+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((381 : ℝ)/512)^2 *
        (253668402593/3125000000000000000000 : ℝ) ≤
      ((381 : ℝ)/512)^2 *
        (∫ x in (((381 : ℝ)/512))..((((381+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_382 :
    (44426723 : ℝ) / 1000000000000000000 ≤
      ((382 : ℝ)/512)^2 *
        (∫ x in (((382 : ℝ)/512))..((((382+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_382).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((382 : ℝ)/512)^2 by positivity)
  have hn :
      (44426723 : ℝ) / 1000000000000000000 ≤
        ((382 : ℝ)/512)^2 *
          (997625400037/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (191/256 : ℝ) = ((382 : ℝ)/512) := by
    norm_num
  have hright :
      (383/512 : ℝ) = (((( 382+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((382 : ℝ)/512)^2 *
        (997625400037/12500000000000000000000 : ℝ) ≤
      ((382 : ℝ)/512)^2 *
        (∫ x in (((382 : ℝ)/512))..((((382+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_383 :
    (43895695 : ℝ) / 1000000000000000000 ≤
      ((383 : ℝ)/512)^2 *
        (∫ x in (((383 : ℝ)/512))..((((383+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_383).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((383 : ℝ)/512)^2 by positivity)
  have hn :
      (43895695 : ℝ) / 1000000000000000000 ≤
        ((383 : ℝ)/512)^2 *
          (784448262251/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (383/512 : ℝ) = ((383 : ℝ)/512) := by
    norm_num
  have hright :
      (3/4 : ℝ) = (((( 383+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((383 : ℝ)/512)^2 *
        (784448262251/10000000000000000000000 : ℝ) ≤
      ((383 : ℝ)/512)^2 *
        (∫ x in (((383 : ℝ)/512))..((((383+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
