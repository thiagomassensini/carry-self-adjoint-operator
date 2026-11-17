import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_17
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_544 :
    (63608 : ℝ) / 1000000000000000000 ≤
      ((544 : ℝ)/512)^2 *
        (∫ x in (((544 : ℝ)/512))..((((544+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_544).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((544 : ℝ)/512)^2 by positivity)
  have hn :
      (63608 : ℝ) / 1000000000000000000 ≤
        ((544 : ℝ)/512)^2 *
          (5634550807/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (17/16 : ℝ) = ((544 : ℝ)/512) := by
    norm_num
  have hright :
      (545/512 : ℝ) = (((( 544+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((544 : ℝ)/512)^2 *
        (5634550807/100000000000000000000000 : ℝ) ≤
      ((544 : ℝ)/512)^2 *
        (∫ x in (((544 : ℝ)/512))..((((544+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_545 :
    (59141 : ℝ) / 1000000000000000000 ≤
      ((545 : ℝ)/512)^2 *
        (∫ x in (((545 : ℝ)/512))..((((545+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_545).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((545 : ℝ)/512)^2 by positivity)
  have hn :
      (59141 : ℝ) / 1000000000000000000 ≤
        ((545 : ℝ)/512)^2 *
          (5219656843/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (545/512 : ℝ) = ((545 : ℝ)/512) := by
    norm_num
  have hright :
      (273/256 : ℝ) = (((( 545+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((545 : ℝ)/512)^2 *
        (5219656843/100000000000000000000000 : ℝ) ≤
      ((545 : ℝ)/512)^2 *
        (∫ x in (((545 : ℝ)/512))..((((545+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_546 :
    (54963 : ℝ) / 1000000000000000000 ≤
      ((546 : ℝ)/512)^2 *
        (∫ x in (((546 : ℝ)/512))..((((546+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_546).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((546 : ℝ)/512)^2 by positivity)
  have hn :
      (54963 : ℝ) / 1000000000000000000 ≤
        ((546 : ℝ)/512)^2 *
          (2416567049/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (273/256 : ℝ) = ((546 : ℝ)/512) := by
    norm_num
  have hright :
      (547/512 : ℝ) = (((( 546+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((546 : ℝ)/512)^2 *
        (2416567049/50000000000000000000000 : ℝ) ≤
      ((546 : ℝ)/512)^2 *
        (∫ x in (((546 : ℝ)/512))..((((546+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_547 :
    (51056 : ℝ) / 1000000000000000000 ≤
      ((547 : ℝ)/512)^2 *
        (∫ x in (((547 : ℝ)/512))..((((547+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_547).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((547 : ℝ)/512)^2 by positivity)
  have hn :
      (51056 : ℝ) / 1000000000000000000 ≤
        ((547 : ℝ)/512)^2 *
          (223660541/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (547/512 : ℝ) = ((547 : ℝ)/512) := by
    norm_num
  have hright :
      (137/128 : ℝ) = (((( 547+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((547 : ℝ)/512)^2 *
        (223660541/5000000000000000000000 : ℝ) ≤
      ((547 : ℝ)/512)^2 *
        (∫ x in (((547 : ℝ)/512))..((((547+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_548 :
    (47406 : ℝ) / 1000000000000000000 ≤
      ((548 : ℝ)/512)^2 *
        (∫ x in (((548 : ℝ)/512))..((((548+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_548).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((548 : ℝ)/512)^2 by positivity)
  have hn :
      (47406 : ℝ) / 1000000000000000000 ≤
        ((548 : ℝ)/512)^2 *
          (4138213591/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (137/128 : ℝ) = ((548 : ℝ)/512) := by
    norm_num
  have hright :
      (549/512 : ℝ) = (((( 548+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((548 : ℝ)/512)^2 *
        (4138213591/100000000000000000000000 : ℝ) ≤
      ((548 : ℝ)/512)^2 *
        (∫ x in (((548 : ℝ)/512))..((((548+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_549 :
    (43996 : ℝ) / 1000000000000000000 ≤
      ((549 : ℝ)/512)^2 *
        (∫ x in (((549 : ℝ)/512))..((((549+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_549).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((549 : ℝ)/512)^2 by positivity)
  have hn :
      (43996 : ℝ) / 1000000000000000000 ≤
        ((549 : ℝ)/512)^2 *
          (478320339/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (549/512 : ℝ) = ((549 : ℝ)/512) := by
    norm_num
  have hright :
      (275/256 : ℝ) = (((( 549+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((549 : ℝ)/512)^2 *
        (478320339/12500000000000000000000 : ℝ) ≤
      ((549 : ℝ)/512)^2 *
        (∫ x in (((549 : ℝ)/512))..((((549+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_550 :
    (40812 : ℝ) / 1000000000000000000 ≤
      ((550 : ℝ)/512)^2 *
        (∫ x in (((550 : ℝ)/512))..((((550+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_550).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((550 : ℝ)/512)^2 by positivity)
  have hn :
      (40812 : ℝ) / 1000000000000000000 ≤
        ((550 : ℝ)/512)^2 *
          (884191941/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (275/256 : ℝ) = ((550 : ℝ)/512) := by
    norm_num
  have hright :
      (551/512 : ℝ) = (((( 550+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((550 : ℝ)/512)^2 *
        (884191941/25000000000000000000000 : ℝ) ≤
      ((550 : ℝ)/512)^2 *
        (∫ x in (((550 : ℝ)/512))..((((550+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_551 :
    (37841 : ℝ) / 1000000000000000000 ≤
      ((551 : ℝ)/512)^2 *
        (∫ x in (((551 : ℝ)/512))..((((551+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_551).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((551 : ℝ)/512)^2 by positivity)
  have hn :
      (37841 : ℝ) / 1000000000000000000 ≤
        ((551 : ℝ)/512)^2 *
          (653484663/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (551/512 : ℝ) = ((551 : ℝ)/512) := by
    norm_num
  have hright :
      (69/64 : ℝ) = (((( 551+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((551 : ℝ)/512)^2 *
        (653484663/20000000000000000000000 : ℝ) ≤
      ((551 : ℝ)/512)^2 *
        (∫ x in (((551 : ℝ)/512))..((((551+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_552 :
    (35070 : ℝ) / 1000000000000000000 ≤
      ((552 : ℝ)/512)^2 *
        (∫ x in (((552 : ℝ)/512))..((((552+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_552).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((552 : ℝ)/512)^2 by positivity)
  have hn :
      (35070 : ℝ) / 1000000000000000000 ≤
        ((552 : ℝ)/512)^2 *
          (377150599/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (69/64 : ℝ) = ((552 : ℝ)/512) := by
    norm_num
  have hright :
      (553/512 : ℝ) = (((( 552+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((552 : ℝ)/512)^2 *
        (377150599/12500000000000000000000 : ℝ) ≤
      ((552 : ℝ)/512)^2 *
        (∫ x in (((552 : ℝ)/512))..((((552+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_553 :
    (32487 : ℝ) / 1000000000000000000 ≤
      ((553 : ℝ)/512)^2 *
        (∫ x in (((553 : ℝ)/512))..((((553+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_553).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((553 : ℝ)/512)^2 by positivity)
  have hn :
      (32487 : ℝ) / 1000000000000000000 ≤
        ((553 : ℝ)/512)^2 *
          (2784864497/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (553/512 : ℝ) = ((553 : ℝ)/512) := by
    norm_num
  have hright :
      (277/256 : ℝ) = (((( 553+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((553 : ℝ)/512)^2 *
        (2784864497/100000000000000000000000 : ℝ) ≤
      ((553 : ℝ)/512)^2 *
        (∫ x in (((553 : ℝ)/512))..((((553+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_554 :
    (30080 : ℝ) / 1000000000000000000 ≤
      ((554 : ℝ)/512)^2 *
        (∫ x in (((554 : ℝ)/512))..((((554+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_554).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((554 : ℝ)/512)^2 by positivity)
  have hn :
      (30080 : ℝ) / 1000000000000000000 ≤
        ((554 : ℝ)/512)^2 *
          (2569227783/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (277/256 : ℝ) = ((554 : ℝ)/512) := by
    norm_num
  have hright :
      (555/512 : ℝ) = (((( 554+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((554 : ℝ)/512)^2 *
        (2569227783/100000000000000000000000 : ℝ) ≤
      ((554 : ℝ)/512)^2 *
        (∫ x in (((554 : ℝ)/512))..((((554+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_555 :
    (27838 : ℝ) / 1000000000000000000 ≤
      ((555 : ℝ)/512)^2 *
        (∫ x in (((555 : ℝ)/512))..((((555+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_555).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((555 : ℝ)/512)^2 by positivity)
  have hn :
      (27838 : ℝ) / 1000000000000000000 ≤
        ((555 : ℝ)/512)^2 *
          (2369189373/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (555/512 : ℝ) = ((555 : ℝ)/512) := by
    norm_num
  have hright :
      (139/128 : ℝ) = (((( 555+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((555 : ℝ)/512)^2 *
        (2369189373/100000000000000000000000 : ℝ) ≤
      ((555 : ℝ)/512)^2 *
        (∫ x in (((555 : ℝ)/512))..((((555+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_556 :
    (25751 : ℝ) / 1000000000000000000 ≤
      ((556 : ℝ)/512)^2 *
        (∫ x in (((556 : ℝ)/512))..((((556+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_556).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((556 : ℝ)/512)^2 by positivity)
  have hn :
      (25751 : ℝ) / 1000000000000000000 ≤
        ((556 : ℝ)/512)^2 *
          (2183709823/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (139/128 : ℝ) = ((556 : ℝ)/512) := by
    norm_num
  have hright :
      (557/512 : ℝ) = (((( 556+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((556 : ℝ)/512)^2 *
        (2183709823/100000000000000000000000 : ℝ) ≤
      ((556 : ℝ)/512)^2 *
        (∫ x in (((556 : ℝ)/512))..((((556+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_557 :
    (23809 : ℝ) / 1000000000000000000 ≤
      ((557 : ℝ)/512)^2 *
        (∫ x in (((557 : ℝ)/512))..((((557+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_557).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((557 : ℝ)/512)^2 by positivity)
  have hn :
      (23809 : ℝ) / 1000000000000000000 ≤
        ((557 : ℝ)/512)^2 *
          (62869129/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (557/512 : ℝ) = ((557 : ℝ)/512) := by
    norm_num
  have hright :
      (279/256 : ℝ) = (((( 557+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((557 : ℝ)/512)^2 *
        (62869129/3125000000000000000000 : ℝ) ≤
      ((557 : ℝ)/512)^2 *
        (∫ x in (((557 : ℝ)/512))..((((557+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_558 :
    (22004 : ℝ) / 1000000000000000000 ≤
      ((558 : ℝ)/512)^2 *
        (∫ x in (((558 : ℝ)/512))..((((558+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_558).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((558 : ℝ)/512)^2 by positivity)
  have hn :
      (22004 : ℝ) / 1000000000000000000 ≤
        ((558 : ℝ)/512)^2 *
          (231572309/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (279/256 : ℝ) = ((558 : ℝ)/512) := by
    norm_num
  have hright :
      (559/512 : ℝ) = (((( 558+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((558 : ℝ)/512)^2 *
        (231572309/12500000000000000000000 : ℝ) ≤
      ((558 : ℝ)/512)^2 *
        (∫ x in (((558 : ℝ)/512))..((((558+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_559 :
    (20325 : ℝ) / 1000000000000000000 ≤
      ((559 : ℝ)/512)^2 *
        (∫ x in (((559 : ℝ)/512))..((((559+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_559).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((559 : ℝ)/512)^2 by positivity)
  have hn :
      (20325 : ℝ) / 1000000000000000000 ≤
        ((559 : ℝ)/512)^2 *
          (53285847/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (559/512 : ℝ) = ((559 : ℝ)/512) := by
    norm_num
  have hright :
      (35/32 : ℝ) = (((( 559+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((559 : ℝ)/512)^2 *
        (53285847/3125000000000000000000 : ℝ) ≤
      ((559 : ℝ)/512)^2 *
        (∫ x in (((559 : ℝ)/512))..((((559+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_560 :
    (18766 : ℝ) / 1000000000000000000 ≤
      ((560 : ℝ)/512)^2 *
        (∫ x in (((560 : ℝ)/512))..((((560+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_560).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((560 : ℝ)/512)^2 by positivity)
  have hn :
      (18766 : ℝ) / 1000000000000000000 ≤
        ((560 : ℝ)/512)^2 *
          (196088669/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (35/32 : ℝ) = ((560 : ℝ)/512) := by
    norm_num
  have hright :
      (561/512 : ℝ) = (((( 560+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((560 : ℝ)/512)^2 *
        (196088669/12500000000000000000000 : ℝ) ≤
      ((560 : ℝ)/512)^2 *
        (∫ x in (((560 : ℝ)/512))..((((560+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_561 :
    (17318 : ℝ) / 1000000000000000000 ≤
      ((561 : ℝ)/512)^2 *
        (∫ x in (((561 : ℝ)/512))..((((561+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_561).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((561 : ℝ)/512)^2 by positivity)
  have hn :
      (17318 : ℝ) / 1000000000000000000 ≤
        ((561 : ℝ)/512)^2 *
          (90156673/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (561/512 : ℝ) = ((561 : ℝ)/512) := by
    norm_num
  have hright :
      (281/256 : ℝ) = (((( 561+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((561 : ℝ)/512)^2 *
        (90156673/6250000000000000000000 : ℝ) ≤
      ((561 : ℝ)/512)^2 *
        (∫ x in (((561 : ℝ)/512))..((((561+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_562 :
    (15974 : ℝ) / 1000000000000000000 ≤
      ((562 : ℝ)/512)^2 *
        (∫ x in (((562 : ℝ)/512))..((((562+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_562).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((562 : ℝ)/512)^2 by positivity)
  have hn :
      (15974 : ℝ) / 1000000000000000000 ≤
        ((562 : ℝ)/512)^2 *
          (1325828391/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (281/256 : ℝ) = ((562 : ℝ)/512) := by
    norm_num
  have hright :
      (563/512 : ℝ) = (((( 562+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((562 : ℝ)/512)^2 *
        (1325828391/100000000000000000000000 : ℝ) ≤
      ((562 : ℝ)/512)^2 *
        (∫ x in (((562 : ℝ)/512))..((((562+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_563 :
    (14727 : ℝ) / 1000000000000000000 ≤
      ((563 : ℝ)/512)^2 *
        (∫ x in (((563 : ℝ)/512))..((((563+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_563).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((563 : ℝ)/512)^2 by positivity)
  have hn :
      (14727 : ℝ) / 1000000000000000000 ≤
        ((563 : ℝ)/512)^2 *
          (609004067/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (563/512 : ℝ) = ((563 : ℝ)/512) := by
    norm_num
  have hright :
      (141/128 : ℝ) = (((( 563+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((563 : ℝ)/512)^2 *
        (609004067/50000000000000000000000 : ℝ) ≤
      ((563 : ℝ)/512)^2 *
        (∫ x in (((563 : ℝ)/512))..((((563+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_564 :
    (13571 : ℝ) / 1000000000000000000 ≤
      ((564 : ℝ)/512)^2 *
        (∫ x in (((564 : ℝ)/512))..((((564+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_564).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((564 : ℝ)/512)^2 by positivity)
  have hn :
      (13571 : ℝ) / 1000000000000000000 ≤
        ((564 : ℝ)/512)^2 *
          (559211149/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (141/128 : ℝ) = ((564 : ℝ)/512) := by
    norm_num
  have hright :
      (565/512 : ℝ) = (((( 564+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((564 : ℝ)/512)^2 *
        (559211149/50000000000000000000000 : ℝ) ≤
      ((564 : ℝ)/512)^2 *
        (∫ x in (((564 : ℝ)/512))..((((564+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_565 :
    (12500 : ℝ) / 1000000000000000000 ≤
      ((565 : ℝ)/512)^2 *
        (∫ x in (((565 : ℝ)/512))..((((565+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_565).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((565 : ℝ)/512)^2 by positivity)
  have hn :
      (12500 : ℝ) / 1000000000000000000 ≤
        ((565 : ℝ)/512)^2 *
          (1026487183/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (565/512 : ℝ) = ((565 : ℝ)/512) := by
    norm_num
  have hright :
      (283/256 : ℝ) = (((( 565+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((565 : ℝ)/512)^2 *
        (1026487183/100000000000000000000000 : ℝ) ≤
      ((565 : ℝ)/512)^2 *
        (∫ x in (((565 : ℝ)/512))..((((565+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_566 :
    (11507 : ℝ) / 1000000000000000000 ≤
      ((566 : ℝ)/512)^2 *
        (∫ x in (((566 : ℝ)/512))..((((566+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_566).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((566 : ℝ)/512)^2 by positivity)
  have hn :
      (11507 : ℝ) / 1000000000000000000 ≤
        ((566 : ℝ)/512)^2 *
          (470828413/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (283/256 : ℝ) = ((566 : ℝ)/512) := by
    norm_num
  have hright :
      (567/512 : ℝ) = (((( 566+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((566 : ℝ)/512)^2 *
        (470828413/50000000000000000000000 : ℝ) ≤
      ((566 : ℝ)/512)^2 *
        (∫ x in (((566 : ℝ)/512))..((((566+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_567 :
    (10588 : ℝ) / 1000000000000000000 ≤
      ((567 : ℝ)/512)^2 *
        (∫ x in (((567 : ℝ)/512))..((((567+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_567).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((567 : ℝ)/512)^2 by positivity)
  have hn :
      (10588 : ℝ) / 1000000000000000000 ≤
        ((567 : ℝ)/512)^2 *
          (863420839/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (567/512 : ℝ) = ((567 : ℝ)/512) := by
    norm_num
  have hright :
      (71/64 : ℝ) = (((( 567+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((567 : ℝ)/512)^2 *
        (863420839/100000000000000000000000 : ℝ) ≤
      ((567 : ℝ)/512)^2 *
        (∫ x in (((567 : ℝ)/512))..((((567+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_568 :
    (9738 : ℝ) / 1000000000000000000 ≤
      ((568 : ℝ)/512)^2 *
        (∫ x in (((568 : ℝ)/512))..((((568+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_568).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((568 : ℝ)/512)^2 by positivity)
  have hn :
      (9738 : ℝ) / 1000000000000000000 ≤
        ((568 : ℝ)/512)^2 *
          (791302349/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (71/64 : ℝ) = ((568 : ℝ)/512) := by
    norm_num
  have hright :
      (569/512 : ℝ) = (((( 568+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((568 : ℝ)/512)^2 *
        (791302349/100000000000000000000000 : ℝ) ≤
      ((568 : ℝ)/512)^2 *
        (∫ x in (((568 : ℝ)/512))..((((568+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_569 :
    (8952 : ℝ) / 1000000000000000000 ≤
      ((569 : ℝ)/512)^2 *
        (∫ x in (((569 : ℝ)/512))..((((569+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_569).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((569 : ℝ)/512)^2 by positivity)
  have hn :
      (8952 : ℝ) / 1000000000000000000 ≤
        ((569 : ℝ)/512)^2 *
          (724856041/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (569/512 : ℝ) = ((569 : ℝ)/512) := by
    norm_num
  have hright :
      (285/256 : ℝ) = (((( 569+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((569 : ℝ)/512)^2 *
        (724856041/100000000000000000000000 : ℝ) ≤
      ((569 : ℝ)/512)^2 *
        (∫ x in (((569 : ℝ)/512))..((((569+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_570 :
    (8225 : ℝ) / 1000000000000000000 ≤
      ((570 : ℝ)/512)^2 *
        (∫ x in (((570 : ℝ)/512))..((((570+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_570).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((570 : ℝ)/512)^2 by positivity)
  have hn :
      (8225 : ℝ) / 1000000000000000000 ≤
        ((570 : ℝ)/512)^2 *
          (663666301/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (285/256 : ℝ) = ((570 : ℝ)/512) := by
    norm_num
  have hright :
      (571/512 : ℝ) = (((( 570+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((570 : ℝ)/512)^2 *
        (663666301/100000000000000000000000 : ℝ) ≤
      ((570 : ℝ)/512)^2 *
        (∫ x in (((570 : ℝ)/512))..((((570+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_571 :
    (7553 : ℝ) / 1000000000000000000 ≤
      ((571 : ℝ)/512)^2 *
        (∫ x in (((571 : ℝ)/512))..((((571+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_571).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((571 : ℝ)/512)^2 by positivity)
  have hn :
      (7553 : ℝ) / 1000000000000000000 ≤
        ((571 : ℝ)/512)^2 *
          (303672721/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (571/512 : ℝ) = ((571 : ℝ)/512) := by
    norm_num
  have hright :
      (143/128 : ℝ) = (((( 571+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((571 : ℝ)/512)^2 *
        (303672721/50000000000000000000000 : ℝ) ≤
      ((571 : ℝ)/512)^2 *
        (∫ x in (((571 : ℝ)/512))..((((571+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_572 :
    (6933 : ℝ) / 1000000000000000000 ≤
      ((572 : ℝ)/512)^2 *
        (∫ x in (((572 : ℝ)/512))..((((572+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_572).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((572 : ℝ)/512)^2 by positivity)
  have hn :
      (6933 : ℝ) / 1000000000000000000 ≤
        ((572 : ℝ)/512)^2 *
          (138883007/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (143/128 : ℝ) = ((572 : ℝ)/512) := by
    norm_num
  have hright :
      (573/512 : ℝ) = (((( 572+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((572 : ℝ)/512)^2 *
        (138883007/25000000000000000000000 : ℝ) ≤
      ((572 : ℝ)/512)^2 *
        (∫ x in (((572 : ℝ)/512))..((((572+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_573 :
    (6361 : ℝ) / 1000000000000000000 ≤
      ((573 : ℝ)/512)^2 *
        (∫ x in (((573 : ℝ)/512))..((((573+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_573).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((573 : ℝ)/512)^2 by positivity)
  have hn :
      (6361 : ℝ) / 1000000000000000000 ≤
        ((573 : ℝ)/512)^2 *
          (101577857/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (573/512 : ℝ) = ((573 : ℝ)/512) := by
    norm_num
  have hright :
      (287/256 : ℝ) = (((( 573+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((573 : ℝ)/512)^2 *
        (101577857/20000000000000000000000 : ℝ) ≤
      ((573 : ℝ)/512)^2 *
        (∫ x in (((573 : ℝ)/512))..((((573+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_574 :
    (5833 : ℝ) / 1000000000000000000 ≤
      ((574 : ℝ)/512)^2 *
        (∫ x in (((574 : ℝ)/512))..((((574+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_574).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((574 : ℝ)/512)^2 by positivity)
  have hn :
      (5833 : ℝ) / 1000000000000000000 ≤
        ((574 : ℝ)/512)^2 *
          (464103583/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (287/256 : ℝ) = ((574 : ℝ)/512) := by
    norm_num
  have hright :
      (575/512 : ℝ) = (((( 574+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((574 : ℝ)/512)^2 *
        (464103583/100000000000000000000000 : ℝ) ≤
      ((574 : ℝ)/512)^2 *
        (∫ x in (((574 : ℝ)/512))..((((574+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_575 :
    (5346 : ℝ) / 1000000000000000000 ≤
      ((575 : ℝ)/512)^2 *
        (∫ x in (((575 : ℝ)/512))..((((575+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_575).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((575 : ℝ)/512)^2 by positivity)
  have hn :
      (5346 : ℝ) / 1000000000000000000 ≤
        ((575 : ℝ)/512)^2 *
          (84776603/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (575/512 : ℝ) = ((575 : ℝ)/512) := by
    norm_num
  have hright :
      (9/8 : ℝ) = (((( 575+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((575 : ℝ)/512)^2 *
        (84776603/20000000000000000000000 : ℝ) ≤
      ((575 : ℝ)/512)^2 *
        (∫ x in (((575 : ℝ)/512))..((((575+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
