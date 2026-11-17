import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_14
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_448 :
    (9865366 : ℝ) / 1000000000000000000 ≤
      ((448 : ℝ)/512)^2 *
        (∫ x in (((448 : ℝ)/512))..((((448+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_448).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((448 : ℝ)/512)^2 by positivity)
  have hn :
      (9865366 : ℝ) / 1000000000000000000 ≤
        ((448 : ℝ)/512)^2 *
          (257707543023/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (7/8 : ℝ) = ((448 : ℝ)/512) := by
    norm_num
  have hright :
      (449/512 : ℝ) = (((( 448+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((448 : ℝ)/512)^2 *
        (257707543023/20000000000000000000000 : ℝ) ≤
      ((448 : ℝ)/512)^2 *
        (∫ x in (((448 : ℝ)/512))..((((448+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_449 :
    (9532925 : ℝ) / 1000000000000000000 ≤
      ((449 : ℝ)/512)^2 *
        (∫ x in (((449 : ℝ)/512))..((((449+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_449).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((449 : ℝ)/512)^2 by positivity)
  have hn :
      (9532925 : ℝ) / 1000000000000000000 ≤
        ((449 : ℝ)/512)^2 *
          (619788393681/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (449/512 : ℝ) = ((449 : ℝ)/512) := by
    norm_num
  have hright :
      (225/256 : ℝ) = (((( 449+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((449 : ℝ)/512)^2 *
        (619788393681/50000000000000000000000 : ℝ) ≤
      ((449 : ℝ)/512)^2 *
        (∫ x in (((449 : ℝ)/512))..((((449+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_450 :
    (9208401 : ℝ) / 1000000000000000000 ≤
      ((450 : ℝ)/512)^2 *
        (∫ x in (((450 : ℝ)/512))..((((450+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_450).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((450 : ℝ)/512)^2 by positivity)
  have hn :
      (9208401 : ℝ) / 1000000000000000000 ≤
        ((450 : ℝ)/512)^2 *
          (1192062813663/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (225/256 : ℝ) = ((450 : ℝ)/512) := by
    norm_num
  have hright :
      (451/512 : ℝ) = (((( 450+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((450 : ℝ)/512)^2 *
        (1192062813663/100000000000000000000000 : ℝ) ≤
      ((450 : ℝ)/512)^2 *
        (∫ x in (((450 : ℝ)/512))..((((450+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_451 :
    (8891746 : ℝ) / 1000000000000000000 ≤
      ((451 : ℝ)/512)^2 *
        (∫ x in (((451 : ℝ)/512))..((((451+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_451).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((451 : ℝ)/512)^2 by positivity)
  have hn :
      (8891746 : ℝ) / 1000000000000000000 ≤
        ((451 : ℝ)/512)^2 *
          (71623234579/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (451/512 : ℝ) = ((451 : ℝ)/512) := by
    norm_num
  have hright :
      (113/128 : ℝ) = (((( 451+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((451 : ℝ)/512)^2 *
        (71623234579/6250000000000000000000 : ℝ) ≤
      ((451 : ℝ)/512)^2 *
        (∫ x in (((451 : ℝ)/512))..((((451+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_452 :
    (8582906 : ℝ) / 1000000000000000000 ≤
      ((452 : ℝ)/512)^2 *
        (∫ x in (((452 : ℝ)/512))..((((452+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_452).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((452 : ℝ)/512)^2 by positivity)
  have hn :
      (8582906 : ℝ) / 1000000000000000000 ≤
        ((452 : ℝ)/512)^2 *
          (110127913661/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (113/128 : ℝ) = ((452 : ℝ)/512) := by
    norm_num
  have hright :
      (453/512 : ℝ) = (((( 452+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((452 : ℝ)/512)^2 *
        (110127913661/10000000000000000000000 : ℝ) ≤
      ((452 : ℝ)/512)^2 *
        (∫ x in (((452 : ℝ)/512))..((((452+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_453 :
    (8281819 : ℝ) / 1000000000000000000 ≤
      ((453 : ℝ)/512)^2 *
        (∫ x in (((453 : ℝ)/512))..((((453+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_453).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((453 : ℝ)/512)^2 by positivity)
  have hn :
      (8281819 : ℝ) / 1000000000000000000 ≤
        ((453 : ℝ)/512)^2 *
          (1057960109927/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (453/512 : ℝ) = ((453 : ℝ)/512) := by
    norm_num
  have hright :
      (227/256 : ℝ) = (((( 453+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((453 : ℝ)/512)^2 *
        (1057960109927/100000000000000000000000 : ℝ) ≤
      ((453 : ℝ)/512)^2 *
        (∫ x in (((453 : ℝ)/512))..((((453+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_454 :
    (7988421 : ℝ) / 1000000000000000000 ≤
      ((454 : ℝ)/512)^2 *
        (∫ x in (((454 : ℝ)/512))..((((454+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_454).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((454 : ℝ)/512)^2 by positivity)
  have hn :
      (7988421 : ℝ) / 1000000000000000000 ≤
        ((454 : ℝ)/512)^2 *
          (507994739423/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (227/256 : ℝ) = ((454 : ℝ)/512) := by
    norm_num
  have hright :
      (455/512 : ℝ) = (((( 454+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((454 : ℝ)/512)^2 *
        (507994739423/50000000000000000000000 : ℝ) ≤
      ((454 : ℝ)/512)^2 *
        (∫ x in (((454 : ℝ)/512))..((((454+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_455 :
    (7702641 : ℝ) / 1000000000000000000 ≤
      ((455 : ℝ)/512)^2 *
        (∫ x in (((455 : ℝ)/512))..((((455+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_455).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((455 : ℝ)/512)^2 by positivity)
  have hn :
      (7702641 : ℝ) / 1000000000000000000 ≤
        ((455 : ℝ)/512)^2 *
          (975341750997/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (455/512 : ℝ) = ((455 : ℝ)/512) := by
    norm_num
  have hright :
      (57/64 : ℝ) = (((( 455+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((455 : ℝ)/512)^2 *
        (975341750997/100000000000000000000000 : ℝ) ≤
      ((455 : ℝ)/512)^2 *
        (∫ x in (((455 : ℝ)/512))..((((455+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_456 :
    (7424402 : ℝ) / 1000000000000000000 ≤
      ((456 : ℝ)/512)^2 *
        (∫ x in (((456 : ℝ)/512))..((((456+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_456).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((456 : ℝ)/512)^2 by positivity)
  have hn :
      (7424402 : ℝ) / 1000000000000000000 ≤
        ((456 : ℝ)/512)^2 *
          (935991177553/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (57/64 : ℝ) = ((456 : ℝ)/512) := by
    norm_num
  have hright :
      (457/512 : ℝ) = (((( 456+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((456 : ℝ)/512)^2 *
        (935991177553/100000000000000000000000 : ℝ) ≤
      ((456 : ℝ)/512)^2 *
        (∫ x in (((456 : ℝ)/512))..((((456+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_457 :
    (7153624 : ℝ) / 1000000000000000000 ≤
      ((457 : ℝ)/512)^2 *
        (∫ x in (((457 : ℝ)/512))..((((457+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_457).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((457 : ℝ)/512)^2 by positivity)
  have hn :
      (7153624 : ℝ) / 1000000000000000000 ≤
        ((457 : ℝ)/512)^2 *
          (179582358737/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (457/512 : ℝ) = ((457 : ℝ)/512) := by
    norm_num
  have hright :
      (229/256 : ℝ) = (((( 457+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((457 : ℝ)/512)^2 *
        (179582358737/20000000000000000000000 : ℝ) ≤
      ((457 : ℝ)/512)^2 *
        (∫ x in (((457 : ℝ)/512))..((((457+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_458 :
    (6890222 : ℝ) / 1000000000000000000 ≤
      ((458 : ℝ)/512)^2 *
        (∫ x in (((458 : ℝ)/512))..((((458+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_458).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((458 : ℝ)/512)^2 by positivity)
  have hn :
      (6890222 : ℝ) / 1000000000000000000 ≤
        ((458 : ℝ)/512)^2 *
          (21526936447/2500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (229/256 : ℝ) = ((458 : ℝ)/512) := by
    norm_num
  have hright :
      (459/512 : ℝ) = (((( 458+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((458 : ℝ)/512)^2 *
        (21526936447/2500000000000000000000 : ℝ) ≤
      ((458 : ℝ)/512)^2 *
        (∫ x in (((458 : ℝ)/512))..((((458+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_459 :
    (6634107 : ℝ) / 1000000000000000000 ≤
      ((459 : ℝ)/512)^2 *
        (∫ x in (((459 : ℝ)/512))..((((459+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_459).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((459 : ℝ)/512)^2 by positivity)
  have hn :
      (6634107 : ℝ) / 1000000000000000000 ≤
        ((459 : ℝ)/512)^2 *
          (165092378021/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (459/512 : ℝ) = ((459 : ℝ)/512) := by
    norm_num
  have hright :
      (115/128 : ℝ) = (((( 459+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((459 : ℝ)/512)^2 *
        (165092378021/20000000000000000000000 : ℝ) ≤
      ((459 : ℝ)/512)^2 *
        (∫ x in (((459 : ℝ)/512))..((((459+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_460 :
    (6385184 : ℝ) / 1000000000000000000 ≤
      ((460 : ℝ)/512)^2 *
        (∫ x in (((460 : ℝ)/512))..((((460+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_460).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((460 : ℝ)/512)^2 by positivity)
  have hn :
      (6385184 : ℝ) / 1000000000000000000 ≤
        ((460 : ℝ)/512)^2 *
          (197759677199/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (115/128 : ℝ) = ((460 : ℝ)/512) := by
    norm_num
  have hright :
      (461/512 : ℝ) = (((( 460+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((460 : ℝ)/512)^2 *
        (197759677199/25000000000000000000000 : ℝ) ≤
      ((460 : ℝ)/512)^2 *
        (∫ x in (((460 : ℝ)/512))..((((460+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_461 :
    (6143359 : ℝ) / 1000000000000000000 ≤
      ((461 : ℝ)/512)^2 *
        (∫ x in (((461 : ℝ)/512))..((((461+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_461).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((461 : ℝ)/512)^2 by positivity)
  have hn :
      (6143359 : ℝ) / 1000000000000000000 ≤
        ((461 : ℝ)/512)^2 *
          (37889073331/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (461/512 : ℝ) = ((461 : ℝ)/512) := by
    norm_num
  have hright :
      (231/256 : ℝ) = (((( 461+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((461 : ℝ)/512)^2 *
        (37889073331/5000000000000000000000 : ℝ) ≤
      ((461 : ℝ)/512)^2 *
        (∫ x in (((461 : ℝ)/512))..((((461+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_462 :
    (5908529 : ℝ) / 1000000000000000000 ≤
      ((462 : ℝ)/512)^2 *
        (∫ x in (((462 : ℝ)/512))..((((462+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_462).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((462 : ℝ)/512)^2 by positivity)
  have hn :
      (5908529 : ℝ) / 1000000000000000000 ≤
        ((462 : ℝ)/512)^2 *
          (725663685029/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (231/256 : ℝ) = ((462 : ℝ)/512) := by
    norm_num
  have hright :
      (463/512 : ℝ) = (((( 462+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((462 : ℝ)/512)^2 *
        (725663685029/100000000000000000000000 : ℝ) ≤
      ((462 : ℝ)/512)^2 *
        (∫ x in (((462 : ℝ)/512))..((((462+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_463 :
    (5680592 : ℝ) / 1000000000000000000 ≤
      ((463 : ℝ)/512)^2 *
        (∫ x in (((463 : ℝ)/512))..((((463+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_463).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((463 : ℝ)/512)^2 by positivity)
  have hn :
      (5680592 : ℝ) / 1000000000000000000 ≤
        ((463 : ℝ)/512)^2 *
          (138931777511/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (463/512 : ℝ) = ((463 : ℝ)/512) := by
    norm_num
  have hright :
      (29/32 : ℝ) = (((( 463+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((463 : ℝ)/512)^2 *
        (138931777511/20000000000000000000000 : ℝ) ≤
      ((463 : ℝ)/512)^2 *
        (∫ x in (((463 : ℝ)/512))..((((463+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_464 :
    (5459442 : ℝ) / 1000000000000000000 ≤
      ((464 : ℝ)/512)^2 *
        (∫ x in (((464 : ℝ)/512))..((((464+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_464).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((464 : ℝ)/512)^2 by positivity)
  have hn :
      (5459442 : ℝ) / 1000000000000000000 ≤
        ((464 : ℝ)/512)^2 *
          (332370315927/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (29/32 : ℝ) = ((464 : ℝ)/512) := by
    norm_num
  have hright :
      (465/512 : ℝ) = (((( 464+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((464 : ℝ)/512)^2 *
        (332370315927/50000000000000000000000 : ℝ) ≤
      ((464 : ℝ)/512)^2 *
        (∫ x in (((464 : ℝ)/512))..((((464+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_465 :
    (5244968 : ℝ) / 1000000000000000000 ≤
      ((465 : ℝ)/512)^2 *
        (∫ x in (((465 : ℝ)/512))..((((465+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_465).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((465 : ℝ)/512)^2 by positivity)
  have hn :
      (5244968 : ℝ) / 1000000000000000000 ≤
        ((465 : ℝ)/512)^2 *
          (158970635119/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (465/512 : ℝ) = ((465 : ℝ)/512) := by
    norm_num
  have hright :
      (233/256 : ℝ) = (((( 465+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((465 : ℝ)/512)^2 *
        (158970635119/25000000000000000000000 : ℝ) ≤
      ((465 : ℝ)/512)^2 *
        (∫ x in (((465 : ℝ)/512))..((((465+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_466 :
    (5037060 : ℝ) / 1000000000000000000 ≤
      ((466 : ℝ)/512)^2 *
        (∫ x in (((466 : ℝ)/512))..((((466+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_466).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((466 : ℝ)/512)^2 by positivity)
  have hn :
      (5037060 : ℝ) / 1000000000000000000 ≤
        ((466 : ℝ)/512)^2 *
          (304029165179/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (233/256 : ℝ) = ((466 : ℝ)/512) := by
    norm_num
  have hright :
      (467/512 : ℝ) = (((( 466+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((466 : ℝ)/512)^2 *
        (304029165179/50000000000000000000000 : ℝ) ≤
      ((466 : ℝ)/512)^2 *
        (∫ x in (((466 : ℝ)/512))..((((466+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_467 :
    (4835603 : ℝ) / 1000000000000000000 ≤
      ((467 : ℝ)/512)^2 *
        (∫ x in (((467 : ℝ)/512))..((((467+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_467).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((467 : ℝ)/512)^2 by positivity)
  have hn :
      (4835603 : ℝ) / 1000000000000000000 ≤
        ((467 : ℝ)/512)^2 *
          (581241841041/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (467/512 : ℝ) = ((467 : ℝ)/512) := by
    norm_num
  have hright :
      (117/128 : ℝ) = (((( 467+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((467 : ℝ)/512)^2 *
        (581241841041/100000000000000000000000 : ℝ) ≤
      ((467 : ℝ)/512)^2 *
        (∫ x in (((467 : ℝ)/512))..((((467+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_468 :
    (4640482 : ℝ) / 1000000000000000000 ≤
      ((468 : ℝ)/512)^2 *
        (∫ x in (((468 : ℝ)/512))..((((468+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_468).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((468 : ℝ)/512)^2 by positivity)
  have hn :
      (4640482 : ℝ) / 1000000000000000000 ≤
        ((468 : ℝ)/512)^2 *
          (277703530797/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (117/128 : ℝ) = ((468 : ℝ)/512) := by
    norm_num
  have hright :
      (469/512 : ℝ) = (((( 468+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((468 : ℝ)/512)^2 *
        (277703530797/50000000000000000000000 : ℝ) ≤
      ((468 : ℝ)/512)^2 *
        (∫ x in (((468 : ℝ)/512))..((((468+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_469 :
    (4451580 : ℝ) / 1000000000000000000 ≤
      ((469 : ℝ)/512)^2 *
        (∫ x in (((469 : ℝ)/512))..((((469+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_469).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((469 : ℝ)/512)^2 by positivity)
  have hn :
      (4451580 : ℝ) / 1000000000000000000 ≤
        ((469 : ℝ)/512)^2 *
          (265264078129/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (469/512 : ℝ) = ((469 : ℝ)/512) := by
    norm_num
  have hright :
      (235/256 : ℝ) = (((( 469+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((469 : ℝ)/512)^2 *
        (265264078129/50000000000000000000000 : ℝ) ≤
      ((469 : ℝ)/512)^2 *
        (∫ x in (((469 : ℝ)/512))..((((469+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_470 :
    (4268776 : ℝ) / 1000000000000000000 ≤
      ((470 : ℝ)/512)^2 *
        (∫ x in (((470 : ℝ)/512))..((((470+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_470).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((470 : ℝ)/512)^2 by positivity)
  have hn :
      (4268776 : ℝ) / 1000000000000000000 ≤
        ((470 : ℝ)/512)^2 *
          (101315897763/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (235/256 : ℝ) = ((470 : ℝ)/512) := by
    norm_num
  have hright :
      (471/512 : ℝ) = (((( 470+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((470 : ℝ)/512)^2 *
        (101315897763/20000000000000000000000 : ℝ) ≤
      ((470 : ℝ)/512)^2 *
        (∫ x in (((470 : ℝ)/512))..((((470+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_471 :
    (4091950 : ℝ) / 1000000000000000000 ≤
      ((471 : ℝ)/512)^2 *
        (∫ x in (((471 : ℝ)/512))..((((471+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_471).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((471 : ℝ)/512)^2 by positivity)
  have hn :
      (4091950 : ℝ) / 1000000000000000000 ≤
        ((471 : ℝ)/512)^2 *
          (120883911419/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (471/512 : ℝ) = ((471 : ℝ)/512) := by
    norm_num
  have hright :
      (59/64 : ℝ) = (((( 471+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((471 : ℝ)/512)^2 *
        (120883911419/25000000000000000000000 : ℝ) ≤
      ((471 : ℝ)/512)^2 *
        (∫ x in (((471 : ℝ)/512))..((((471+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_472 :
    (3920981 : ℝ) / 1000000000000000000 ≤
      ((472 : ℝ)/512)^2 *
        (∫ x in (((472 : ℝ)/512))..((((472+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_472).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((472 : ℝ)/512)^2 by positivity)
  have hn :
      (3920981 : ℝ) / 1000000000000000000 ≤
        ((472 : ℝ)/512)^2 *
          (92274291541/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (59/64 : ℝ) = ((472 : ℝ)/512) := by
    norm_num
  have hright :
      (473/512 : ℝ) = (((( 472+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((472 : ℝ)/512)^2 *
        (92274291541/20000000000000000000000 : ℝ) ≤
      ((472 : ℝ)/512)^2 *
        (∫ x in (((472 : ℝ)/512))..((((472+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_473 :
    (3755746 : ℝ) / 1000000000000000000 ≤
      ((473 : ℝ)/512)^2 *
        (∫ x in (((473 : ℝ)/512))..((((473+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_473).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((473 : ℝ)/512)^2 by positivity)
  have hn :
      (3755746 : ℝ) / 1000000000000000000 ≤
        ((473 : ℝ)/512)^2 *
          (44006202079/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (473/512 : ℝ) = ((473 : ℝ)/512) := by
    norm_num
  have hright :
      (237/256 : ℝ) = (((( 473+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((473 : ℝ)/512)^2 *
        (44006202079/10000000000000000000000 : ℝ) ≤
      ((473 : ℝ)/512)^2 *
        (∫ x in (((473 : ℝ)/512))..((((473+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_474 :
    (3596121 : ℝ) / 1000000000000000000 ≤
      ((474 : ℝ)/512)^2 *
        (∫ x in (((474 : ℝ)/512))..((((474+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_474).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((474 : ℝ)/512)^2 by positivity)
  have hn :
      (3596121 : ℝ) / 1000000000000000000 ≤
        ((474 : ℝ)/512)^2 *
          (419582715169/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (237/256 : ℝ) = ((474 : ℝ)/512) := by
    norm_num
  have hright :
      (475/512 : ℝ) = (((( 474+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((474 : ℝ)/512)^2 *
        (419582715169/100000000000000000000000 : ℝ) ≤
      ((474 : ℝ)/512)^2 *
        (∫ x in (((474 : ℝ)/512))..((((474+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_475 :
    (3441982 : ℝ) / 1000000000000000000 ≤
      ((475 : ℝ)/512)^2 *
        (∫ x in (((475 : ℝ)/512))..((((475+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_475).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((475 : ℝ)/512)^2 by positivity)
  have hn :
      (3441982 : ℝ) / 1000000000000000000 ≤
        ((475 : ℝ)/512)^2 *
          (39990922353/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (475/512 : ℝ) = ((475 : ℝ)/512) := by
    norm_num
  have hright :
      (119/128 : ℝ) = (((( 475+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((475 : ℝ)/512)^2 *
        (39990922353/10000000000000000000000 : ℝ) ≤
      ((475 : ℝ)/512)^2 *
        (∫ x in (((475 : ℝ)/512))..((((475+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_476 :
    (3293206 : ℝ) / 1000000000000000000 ≤
      ((476 : ℝ)/512)^2 *
        (∫ x in (((476 : ℝ)/512))..((((476+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_476).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((476 : ℝ)/512)^2 by positivity)
  have hn :
      (3293206 : ℝ) / 1000000000000000000 ≤
        ((476 : ℝ)/512)^2 *
          (3810175479/1000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (119/128 : ℝ) = ((476 : ℝ)/512) := by
    norm_num
  have hright :
      (477/512 : ℝ) = (((( 476+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((476 : ℝ)/512)^2 *
        (3810175479/1000000000000000000000 : ℝ) ≤
      ((476 : ℝ)/512)^2 *
        (∫ x in (((476 : ℝ)/512))..((((476+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_477 :
    (3149667 : ℝ) / 1000000000000000000 ≤
      ((477 : ℝ)/512)^2 *
        (∫ x in (((477 : ℝ)/512))..((((477+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_477).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((477 : ℝ)/512)^2 by positivity)
  have hn :
      (3149667 : ℝ) / 1000000000000000000 ≤
        ((477 : ℝ)/512)^2 *
          (362884025339/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (477/512 : ℝ) = ((477 : ℝ)/512) := by
    norm_num
  have hright :
      (239/256 : ℝ) = (((( 477+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((477 : ℝ)/512)^2 *
        (362884025339/100000000000000000000000 : ℝ) ≤
      ((477 : ℝ)/512)^2 *
        (∫ x in (((477 : ℝ)/512))..((((477+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_478 :
    (3011240 : ℝ) / 1000000000000000000 ≤
      ((478 : ℝ)/512)^2 *
        (∫ x in (((478 : ℝ)/512))..((((478+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_478).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((478 : ℝ)/512)^2 by positivity)
  have hn :
      (3011240 : ℝ) / 1000000000000000000 ≤
        ((478 : ℝ)/512)^2 *
          (86371335617/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (239/256 : ℝ) = ((478 : ℝ)/512) := by
    norm_num
  have hright :
      (479/512 : ℝ) = (((( 478+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((478 : ℝ)/512)^2 *
        (86371335617/25000000000000000000000 : ℝ) ≤
      ((478 : ℝ)/512)^2 *
        (∫ x in (((478 : ℝ)/512))..((((478+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_479 :
    (2877802 : ℝ) / 1000000000000000000 ≤
      ((479 : ℝ)/512)^2 *
        (∫ x in (((479 : ℝ)/512))..((((479+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_479).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((479 : ℝ)/512)^2 by positivity)
  have hn :
      (2877802 : ℝ) / 1000000000000000000 ≤
        ((479 : ℝ)/512)^2 *
          (82199637211/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (479/512 : ℝ) = ((479 : ℝ)/512) := by
    norm_num
  have hright :
      (15/16 : ℝ) = (((( 479+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((479 : ℝ)/512)^2 *
        (82199637211/25000000000000000000000 : ℝ) ≤
      ((479 : ℝ)/512)^2 *
        (∫ x in (((479 : ℝ)/512))..((((479+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
