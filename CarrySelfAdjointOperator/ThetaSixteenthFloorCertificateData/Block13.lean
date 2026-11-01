import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_13
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_416 :
    (24573575 : ℝ) / 1000000000000000000 ≤
      ((416 : ℝ)/512)^2 *
        (∫ x in (((416 : ℝ)/512))..((((416+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_416).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((416 : ℝ)/512)^2 by positivity)
  have hn :
      (24573575 : ℝ) / 1000000000000000000 ≤
        ((416 : ℝ)/512)^2 *
          (3722387736063/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (13/16 : ℝ) = ((416 : ℝ)/512) := by
    norm_num
  have hright :
      (417/512 : ℝ) = (((( 416+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((416 : ℝ)/512)^2 *
        (3722387736063/100000000000000000000000 : ℝ) ≤
      ((416 : ℝ)/512)^2 *
        (∫ x in (((416 : ℝ)/512))..((((416+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_417 :
    (24009714 : ℝ) / 1000000000000000000 ≤
      ((417 : ℝ)/512)^2 *
        (∫ x in (((417 : ℝ)/512))..((((417+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_417).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((417 : ℝ)/512)^2 by positivity)
  have hn :
      (24009714 : ℝ) / 1000000000000000000 ≤
        ((417 : ℝ)/512)^2 *
          (3619551892617/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (417/512 : ℝ) = ((417 : ℝ)/512) := by
    norm_num
  have hright :
      (209/256 : ℝ) = (((( 417+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((417 : ℝ)/512)^2 *
        (3619551892617/100000000000000000000000 : ℝ) ≤
      ((417 : ℝ)/512)^2 *
        (∫ x in (((417 : ℝ)/512))..((((417+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_418 :
    (23450895 : ℝ) / 1000000000000000000 ≤
      ((418 : ℝ)/512)^2 *
        (∫ x in (((418 : ℝ)/512))..((((418+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_418).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((418 : ℝ)/512)^2 by positivity)
  have hn :
      (23450895 : ℝ) / 1000000000000000000 ≤
        ((418 : ℝ)/512)^2 *
          (1759206354149/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (209/256 : ℝ) = ((418 : ℝ)/512) := by
    norm_num
  have hright :
      (419/512 : ℝ) = (((( 418+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((418 : ℝ)/512)^2 *
        (1759206354149/50000000000000000000000 : ℝ) ≤
      ((418 : ℝ)/512)^2 *
        (∫ x in (((418 : ℝ)/512))..((((418+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_419 :
    (22897359 : ℝ) / 1000000000000000000 ≤
      ((419 : ℝ)/512)^2 *
        (∫ x in (((419 : ℝ)/512))..((((419+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_419).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((419 : ℝ)/512)^2 by positivity)
  have hn :
      (22897359 : ℝ) / 1000000000000000000 ≤
        ((419 : ℝ)/512)^2 *
          (1709492828259/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (419/512 : ℝ) = ((419 : ℝ)/512) := by
    norm_num
  have hright :
      (105/128 : ℝ) = (((( 419+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((419 : ℝ)/512)^2 *
        (1709492828259/50000000000000000000000 : ℝ) ≤
      ((419 : ℝ)/512)^2 *
        (∫ x in (((419 : ℝ)/512))..((((419+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_420 :
    (22349340 : ℝ) / 1000000000000000000 ≤
      ((420 : ℝ)/512)^2 *
        (∫ x in (((420 : ℝ)/512))..((((420+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_420).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((420 : ℝ)/512)^2 by positivity)
  have hn :
      (22349340 : ℝ) / 1000000000000000000 ≤
        ((420 : ℝ)/512)^2 *
          (103790133611/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (105/128 : ℝ) = ((420 : ℝ)/512) := by
    norm_num
  have hright :
      (421/512 : ℝ) = (((( 420+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((420 : ℝ)/512)^2 *
        (103790133611/3125000000000000000000 : ℝ) ≤
      ((420 : ℝ)/512)^2 *
        (∫ x in (((420 : ℝ)/512))..((((420+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_421 :
    (21807059 : ℝ) / 1000000000000000000 ≤
      ((421 : ℝ)/512)^2 *
        (∫ x in (((421 : ℝ)/512))..((((421+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_421).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((421 : ℝ)/512)^2 by positivity)
  have hn :
      (21807059 : ℝ) / 1000000000000000000 ≤
        ((421 : ℝ)/512)^2 *
          (3225320202479/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (421/512 : ℝ) = ((421 : ℝ)/512) := by
    norm_num
  have hright :
      (211/256 : ℝ) = (((( 421+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((421 : ℝ)/512)^2 *
        (3225320202479/100000000000000000000000 : ℝ) ≤
      ((421 : ℝ)/512)^2 *
        (∫ x in (((421 : ℝ)/512))..((((421+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_422 :
    (21270728 : ℝ) / 1000000000000000000 ≤
      ((422 : ℝ)/512)^2 *
        (∫ x in (((422 : ℝ)/512))..((((422+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_422).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((422 : ℝ)/512)^2 by positivity)
  have hn :
      (21270728 : ℝ) / 1000000000000000000 ≤
        ((422 : ℝ)/512)^2 *
          (1565551604521/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (211/256 : ℝ) = ((422 : ℝ)/512) := by
    norm_num
  have hright :
      (423/512 : ℝ) = (((( 422+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((422 : ℝ)/512)^2 *
        (1565551604521/50000000000000000000000 : ℝ) ≤
      ((422 : ℝ)/512)^2 *
        (∫ x in (((422 : ℝ)/512))..((((422+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_423 :
    (20740548 : ℝ) / 1000000000000000000 ≤
      ((423 : ℝ)/512)^2 *
        (∫ x in (((423 : ℝ)/512))..((((423+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_423).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((423 : ℝ)/512)^2 by positivity)
  have hn :
      (20740548 : ℝ) / 1000000000000000000 ≤
        ((423 : ℝ)/512)^2 *
          (1519320619643/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (423/512 : ℝ) = ((423 : ℝ)/512) := by
    norm_num
  have hright :
      (53/64 : ℝ) = (((( 423+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((423 : ℝ)/512)^2 *
        (1519320619643/50000000000000000000000 : ℝ) ≤
      ((423 : ℝ)/512)^2 *
        (∫ x in (((423 : ℝ)/512))..((((423+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_424 :
    (20216710 : ℝ) / 1000000000000000000 ≤
      ((424 : ℝ)/512)^2 *
        (∫ x in (((424 : ℝ)/512))..((((424+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_424).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((424 : ℝ)/512)^2 by positivity)
  have hn :
      (20216710 : ℝ) / 1000000000000000000 ≤
        ((424 : ℝ)/512)^2 *
          (1473970224449/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (53/64 : ℝ) = ((424 : ℝ)/512) := by
    norm_num
  have hright :
      (425/512 : ℝ) = (((( 424+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((424 : ℝ)/512)^2 *
        (1473970224449/50000000000000000000000 : ℝ) ≤
      ((424 : ℝ)/512)^2 *
        (∫ x in (((424 : ℝ)/512))..((((424+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_425 :
    (19699395 : ℝ) / 1000000000000000000 ≤
      ((425 : ℝ)/512)^2 *
        (∫ x in (((425 : ℝ)/512))..((((425+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_425).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((425 : ℝ)/512)^2 by positivity)
  have hn :
      (19699395 : ℝ) / 1000000000000000000 ≤
        ((425 : ℝ)/512)^2 *
          (2859005246111/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (425/512 : ℝ) = ((425 : ℝ)/512) := by
    norm_num
  have hright :
      (213/256 : ℝ) = (((( 425+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((425 : ℝ)/512)^2 *
        (2859005246111/100000000000000000000000 : ℝ) ≤
      ((425 : ℝ)/512)^2 *
        (∫ x in (((425 : ℝ)/512))..((((425+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_426 :
    (19188771 : ℝ) / 1000000000000000000 ≤
      ((426 : ℝ)/512)^2 *
        (∫ x in (((426 : ℝ)/512))..((((426+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_426).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((426 : ℝ)/512)^2 by positivity)
  have hn :
      (19188771 : ℝ) / 1000000000000000000 ≤
        ((426 : ℝ)/512)^2 *
          (2771838334077/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (213/256 : ℝ) = ((426 : ℝ)/512) := by
    norm_num
  have hright :
      (427/512 : ℝ) = (((( 426+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((426 : ℝ)/512)^2 *
        (2771838334077/100000000000000000000000 : ℝ) ≤
      ((426 : ℝ)/512)^2 *
        (∫ x in (((426 : ℝ)/512))..((((426+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_427 :
    (18684999 : ℝ) / 1000000000000000000 ≤
      ((427 : ℝ)/512)^2 *
        (∫ x in (((427 : ℝ)/512))..((((427+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_427).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((427 : ℝ)/512)^2 by positivity)
  have hn :
      (18684999 : ℝ) / 1000000000000000000 ≤
        ((427 : ℝ)/512)^2 *
          (13432203773/500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (427/512 : ℝ) = ((427 : ℝ)/512) := by
    norm_num
  have hright :
      (107/128 : ℝ) = (((( 427+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((427 : ℝ)/512)^2 *
        (13432203773/500000000000000000000 : ℝ) ≤
      ((427 : ℝ)/512)^2 *
        (∫ x in (((427 : ℝ)/512))..((((427+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_428 :
    (18188228 : ℝ) / 1000000000000000000 ≤
      ((428 : ℝ)/512)^2 *
        (∫ x in (((428 : ℝ)/512))..((((428+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_428).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((428 : ℝ)/512)^2 by positivity)
  have hn :
      (18188228 : ℝ) / 1000000000000000000 ≤
        ((428 : ℝ)/512)^2 *
          (2602811933103/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (107/128 : ℝ) = ((428 : ℝ)/512) := by
    norm_num
  have hright :
      (429/512 : ℝ) = (((( 428+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((428 : ℝ)/512)^2 *
        (2602811933103/100000000000000000000000 : ℝ) ≤
      ((428 : ℝ)/512)^2 *
        (∫ x in (((428 : ℝ)/512))..((((428+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_429 :
    (17698597 : ℝ) / 1000000000000000000 ≤
      ((429 : ℝ)/512)^2 *
        (∫ x in (((429 : ℝ)/512))..((((429+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_429).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((429 : ℝ)/512)^2 by positivity)
  have hn :
      (17698597 : ℝ) / 1000000000000000000 ≤
        ((429 : ℝ)/512)^2 *
          (126047486237/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (429/512 : ℝ) = ((429 : ℝ)/512) := by
    norm_num
  have hright :
      (215/256 : ℝ) = (((( 429+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((429 : ℝ)/512)^2 *
        (126047486237/5000000000000000000000 : ℝ) ≤
      ((429 : ℝ)/512)^2 *
        (∫ x in (((429 : ℝ)/512))..((((429+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_430 :
    (17216234 : ℝ) / 1000000000000000000 ≤
      ((430 : ℝ)/512)^2 *
        (∫ x in (((430 : ℝ)/512))..((((430+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_430).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((430 : ℝ)/512)^2 by positivity)
  have hn :
      (17216234 : ℝ) / 1000000000000000000 ≤
        ((430 : ℝ)/512)^2 *
          (30510630769/1250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (215/256 : ℝ) = ((430 : ℝ)/512) := by
    norm_num
  have hright :
      (431/512 : ℝ) = (((( 430+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((430 : ℝ)/512)^2 *
        (30510630769/1250000000000000000000 : ℝ) ≤
      ((430 : ℝ)/512)^2 *
        (∫ x in (((430 : ℝ)/512))..((((430+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_431 :
    (16741258 : ℝ) / 1000000000000000000 ≤
      ((431 : ℝ)/512)^2 *
        (∫ x in (((431 : ℝ)/512))..((((431+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_431).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((431 : ℝ)/512)^2 by positivity)
  have hn :
      (16741258 : ℝ) / 1000000000000000000 ≤
        ((431 : ℝ)/512)^2 *
          (2362509000363/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (431/512 : ℝ) = ((431 : ℝ)/512) := by
    norm_num
  have hright :
      (27/32 : ℝ) = (((( 431+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((431 : ℝ)/512)^2 *
        (2362509000363/100000000000000000000000 : ℝ) ≤
      ((431 : ℝ)/512)^2 *
        (∫ x in (((431 : ℝ)/512))..((((431+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_432 :
    (16273777 : ℝ) / 1000000000000000000 ≤
      ((432 : ℝ)/512)^2 *
        (∫ x in (((432 : ℝ)/512))..((((432+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_432).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((432 : ℝ)/512)^2 by positivity)
  have hn :
      (16273777 : ℝ) / 1000000000000000000 ≤
        ((432 : ℝ)/512)^2 *
          (457183754389/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (27/32 : ℝ) = ((432 : ℝ)/512) := by
    norm_num
  have hright :
      (433/512 : ℝ) = (((( 432+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((432 : ℝ)/512)^2 *
        (457183754389/20000000000000000000000 : ℝ) ≤
      ((432 : ℝ)/512)^2 *
        (∫ x in (((432 : ℝ)/512))..((((432+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_433 :
    (15813890 : ℝ) / 1000000000000000000 ≤
      ((433 : ℝ)/512)^2 *
        (∫ x in (((433 : ℝ)/512))..((((433+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_433).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((433 : ℝ)/512)^2 by positivity)
  have hn :
      (15813890 : ℝ) / 1000000000000000000 ≤
        ((433 : ℝ)/512)^2 *
          (110553591513/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (433/512 : ℝ) = ((433 : ℝ)/512) := by
    norm_num
  have hright :
      (217/256 : ℝ) = (((( 433+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((433 : ℝ)/512)^2 *
        (110553591513/5000000000000000000000 : ℝ) ≤
      ((433 : ℝ)/512)^2 *
        (∫ x in (((433 : ℝ)/512))..((((433+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_434 :
    (15361686 : ℝ) / 1000000000000000000 ≤
      ((434 : ℝ)/512)^2 *
        (∫ x in (((434 : ℝ)/512))..((((434+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_434).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((434 : ℝ)/512)^2 by positivity)
  have hn :
      (15361686 : ℝ) / 1000000000000000000 ≤
        ((434 : ℝ)/512)^2 *
          (427591780553/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (217/256 : ℝ) = ((434 : ℝ)/512) := by
    norm_num
  have hright :
      (435/512 : ℝ) = (((( 434+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((434 : ℝ)/512)^2 *
        (427591780553/20000000000000000000000 : ℝ) ≤
      ((434 : ℝ)/512)^2 *
        (∫ x in (((434 : ℝ)/512))..((((434+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_435 :
    (14917244 : ℝ) / 1000000000000000000 ≤
      ((435 : ℝ)/512)^2 *
        (∫ x in (((435 : ℝ)/512))..((((435+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_435).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((435 : ℝ)/512)^2 by positivity)
  have hn :
      (14917244 : ℝ) / 1000000000000000000 ≤
        ((435 : ℝ)/512)^2 *
          (206656944103/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (435/512 : ℝ) = ((435 : ℝ)/512) := by
    norm_num
  have hright :
      (109/128 : ℝ) = (((( 435+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((435 : ℝ)/512)^2 *
        (206656944103/10000000000000000000000 : ℝ) ≤
      ((435 : ℝ)/512)^2 *
        (∫ x in (((435 : ℝ)/512))..((((435+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_436 :
    (14480633 : ℝ) / 1000000000000000000 ≤
      ((436 : ℝ)/512)^2 *
        (∫ x in (((436 : ℝ)/512))..((((436+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_436).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((436 : ℝ)/512)^2 by positivity)
  have hn :
      (14480633 : ℝ) / 1000000000000000000 ≤
        ((436 : ℝ)/512)^2 *
          (1996891671763/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (109/128 : ℝ) = ((436 : ℝ)/512) := by
    norm_num
  have hright :
      (437/512 : ℝ) = (((( 436+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((436 : ℝ)/512)^2 *
        (1996891671763/100000000000000000000000 : ℝ) ≤
      ((436 : ℝ)/512)^2 *
        (∫ x in (((436 : ℝ)/512))..((((436+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_437 :
    (14051914 : ℝ) / 1000000000000000000 ≤
      ((437 : ℝ)/512)^2 *
        (∫ x in (((437 : ℝ)/512))..((((437+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_437).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((437 : ℝ)/512)^2 by positivity)
  have hn :
      (14051914 : ℝ) / 1000000000000000000 ≤
        ((437 : ℝ)/512)^2 *
          (96445632407/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (437/512 : ℝ) = ((437 : ℝ)/512) := by
    norm_num
  have hright :
      (219/256 : ℝ) = (((( 437+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((437 : ℝ)/512)^2 *
        (96445632407/5000000000000000000000 : ℝ) ≤
      ((437 : ℝ)/512)^2 *
        (∫ x in (((437 : ℝ)/512))..((((437+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_438 :
    (13631139 : ℝ) / 1000000000000000000 ≤
      ((438 : ℝ)/512)^2 *
        (∫ x in (((438 : ℝ)/512))..((((438+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_438).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((438 : ℝ)/512)^2 by positivity)
  have hn :
      (13631139 : ℝ) / 1000000000000000000 ≤
        ((438 : ℝ)/512)^2 *
          (1862618301319/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (219/256 : ℝ) = ((438 : ℝ)/512) := by
    norm_num
  have hright :
      (439/512 : ℝ) = (((( 438+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((438 : ℝ)/512)^2 *
        (1862618301319/100000000000000000000000 : ℝ) ≤
      ((438 : ℝ)/512)^2 *
        (∫ x in (((438 : ℝ)/512))..((((438+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_439 :
    (13218349 : ℝ) / 1000000000000000000 ≤
      ((439 : ℝ)/512)^2 *
        (∫ x in (((439 : ℝ)/512))..((((439+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_439).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((439 : ℝ)/512)^2 by positivity)
  have hn :
      (13218349 : ℝ) / 1000000000000000000 ≤
        ((439 : ℝ)/512)^2 *
          (224749186507/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (439/512 : ℝ) = ((439 : ℝ)/512) := by
    norm_num
  have hright :
      (55/64 : ℝ) = (((( 439+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((439 : ℝ)/512)^2 *
        (224749186507/12500000000000000000000 : ℝ) ≤
      ((439 : ℝ)/512)^2 *
        (∫ x in (((439 : ℝ)/512))..((((439+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_440 :
    (12813578 : ℝ) / 1000000000000000000 ≤
      ((440 : ℝ)/512)^2 *
        (∫ x in (((440 : ℝ)/512))..((((440+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_440).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((440 : ℝ)/512)^2 by positivity)
  have hn :
      (12813578 : ℝ) / 1000000000000000000 ≤
        ((440 : ℝ)/512)^2 *
          (21687775779/1250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (55/64 : ℝ) = ((440 : ℝ)/512) := by
    norm_num
  have hright :
      (441/512 : ℝ) = (((( 440+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((440 : ℝ)/512)^2 *
        (21687775779/1250000000000000000000 : ℝ) ≤
      ((440 : ℝ)/512)^2 *
        (∫ x in (((440 : ℝ)/512))..((((440+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_441 :
    (12416851 : ℝ) / 1000000000000000000 ≤
      ((441 : ℝ)/512)^2 *
        (∫ x in (((441 : ℝ)/512))..((((441+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_441).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((441 : ℝ)/512)^2 by positivity)
  have hn :
      (12416851 : ℝ) / 1000000000000000000 ≤
        ((441 : ℝ)/512)^2 *
          (104605430427/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (441/512 : ℝ) = ((441 : ℝ)/512) := by
    norm_num
  have hright :
      (221/256 : ℝ) = (((( 441+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((441 : ℝ)/512)^2 *
        (104605430427/6250000000000000000000 : ℝ) ≤
      ((441 : ℝ)/512)^2 *
        (∫ x in (((441 : ℝ)/512))..((((441+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_442 :
    (12028183 : ℝ) / 1000000000000000000 ≤
      ((442 : ℝ)/512)^2 *
        (∫ x in (((442 : ℝ)/512))..((((442+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_442).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((442 : ℝ)/512)^2 by positivity)
  have hn :
      (12028183 : ℝ) / 1000000000000000000 ≤
        ((442 : ℝ)/512)^2 *
          (64558796977/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (221/256 : ℝ) = ((442 : ℝ)/512) := by
    norm_num
  have hright :
      (443/512 : ℝ) = (((( 442+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((442 : ℝ)/512)^2 *
        (64558796977/4000000000000000000000 : ℝ) ≤
      ((442 : ℝ)/512)^2 *
        (∫ x in (((442 : ℝ)/512))..((((442+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_443 :
    (11647584 : ℝ) / 1000000000000000000 ≤
      ((443 : ℝ)/512)^2 *
        (∫ x in (((443 : ℝ)/512))..((((443+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_443).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((443 : ℝ)/512)^2 by positivity)
  have hn :
      (11647584 : ℝ) / 1000000000000000000 ≤
        ((443 : ℝ)/512)^2 *
          (194481533643/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (443/512 : ℝ) = ((443 : ℝ)/512) := by
    norm_num
  have hright :
      (111/128 : ℝ) = (((( 443+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((443 : ℝ)/512)^2 *
        (194481533643/12500000000000000000000 : ℝ) ≤
      ((443 : ℝ)/512)^2 *
        (∫ x in (((443 : ℝ)/512))..((((443+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_444 :
    (11275055 : ℝ) / 1000000000000000000 ≤
      ((444 : ℝ)/512)^2 *
        (∫ x in (((444 : ℝ)/512))..((((444+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_444).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((444 : ℝ)/512)^2 by positivity)
  have hn :
      (11275055 : ℝ) / 1000000000000000000 ≤
        ((444 : ℝ)/512)^2 *
          (749657100509/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (111/128 : ℝ) = ((444 : ℝ)/512) := by
    norm_num
  have hright :
      (445/512 : ℝ) = (((( 444+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((444 : ℝ)/512)^2 *
        (749657100509/50000000000000000000000 : ℝ) ≤
      ((444 : ℝ)/512)^2 *
        (∫ x in (((444 : ℝ)/512))..((((444+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_445 :
    (10910586 : ℝ) / 1000000000000000000 ≤
      ((445 : ℝ)/512)^2 *
        (∫ x in (((445 : ℝ)/512))..((((445+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_445).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((445 : ℝ)/512)^2 by positivity)
  have hn :
      (10910586 : ℝ) / 1000000000000000000 ≤
        ((445 : ℝ)/512)^2 *
          (361083809101/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (445/512 : ℝ) = ((445 : ℝ)/512) := by
    norm_num
  have hright :
      (223/256 : ℝ) = (((( 445+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((445 : ℝ)/512)^2 *
        (361083809101/25000000000000000000000 : ℝ) ≤
      ((445 : ℝ)/512)^2 *
        (∫ x in (((445 : ℝ)/512))..((((445+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_446 :
    (10554165 : ℝ) / 1000000000000000000 ≤
      ((446 : ℝ)/512)^2 *
        (∫ x in (((446 : ℝ)/512))..((((446+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_446).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((446 : ℝ)/512)^2 by positivity)
  have hn :
      (10554165 : ℝ) / 1000000000000000000 ≤
        ((446 : ℝ)/512)^2 *
          (278178835569/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (223/256 : ℝ) = ((446 : ℝ)/512) := by
    norm_num
  have hright :
      (447/512 : ℝ) = (((( 446+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((446 : ℝ)/512)^2 *
        (278178835569/20000000000000000000000 : ℝ) ≤
      ((446 : ℝ)/512)^2 *
        (∫ x in (((446 : ℝ)/512))..((((446+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_447 :
    (10205768 : ℝ) / 1000000000000000000 ≤
      ((447 : ℝ)/512)^2 *
        (∫ x in (((447 : ℝ)/512))..((((447+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_447).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((447 : ℝ)/512)^2 by positivity)
  have hn :
      (10205768 : ℝ) / 1000000000000000000 ≤
        ((447 : ℝ)/512)^2 *
          (669484581681/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (447/512 : ℝ) = ((447 : ℝ)/512) := by
    norm_num
  have hright :
      (7/8 : ℝ) = (((( 447+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((447 : ℝ)/512)^2 *
        (669484581681/50000000000000000000000 : ℝ) ≤
      ((447 : ℝ)/512)^2 *
        (∫ x in (((447 : ℝ)/512))..((((447+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
