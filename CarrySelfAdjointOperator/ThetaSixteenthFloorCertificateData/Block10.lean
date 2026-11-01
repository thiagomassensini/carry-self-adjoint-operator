import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_10
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_320 :
    (50096235 : ℝ) / 1000000000000000000 ≤
      ((320 : ℝ)/512)^2 *
        (∫ x in (((320 : ℝ)/512))..((((320+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_320).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((320 : ℝ)/512)^2 by positivity)
  have hn :
      (50096235 : ℝ) / 1000000000000000000 ≤
        ((320 : ℝ)/512)^2 *
          (12824636226481/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (5/8 : ℝ) = ((320 : ℝ)/512) := by
    norm_num
  have hright :
      (321/512 : ℝ) = (((( 320+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((320 : ℝ)/512)^2 *
        (12824636226481/100000000000000000000000 : ℝ) ≤
      ((320 : ℝ)/512)^2 *
        (∫ x in (((320 : ℝ)/512))..((((320+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_321 :
    (50490023 : ℝ) / 1000000000000000000 ≤
      ((321 : ℝ)/512)^2 *
        (∫ x in (((321 : ℝ)/512))..((((321+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_321).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((321 : ℝ)/512)^2 by positivity)
  have hn :
      (50490023 : ℝ) / 1000000000000000000 ≤
        ((321 : ℝ)/512)^2 *
          (12845039076109/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (321/512 : ℝ) = ((321 : ℝ)/512) := by
    norm_num
  have hright :
      (161/256 : ℝ) = (((( 321+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((321 : ℝ)/512)^2 *
        (12845039076109/100000000000000000000000 : ℝ) ≤
      ((321 : ℝ)/512)^2 *
        (∫ x in (((321 : ℝ)/512))..((((321+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_322 :
    (50870465 : ℝ) / 1000000000000000000 ≤
      ((322 : ℝ)/512)^2 *
        (∫ x in (((322 : ℝ)/512))..((((322+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_322).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((322 : ℝ)/512)^2 by positivity)
  have hn :
      (50870465 : ℝ) / 1000000000000000000 ≤
        ((322 : ℝ)/512)^2 *
          (6430783615497/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (161/256 : ℝ) = ((322 : ℝ)/512) := by
    norm_num
  have hright :
      (323/512 : ℝ) = (((( 322+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((322 : ℝ)/512)^2 *
        (6430783615497/50000000000000000000000 : ℝ) ≤
      ((322 : ℝ)/512)^2 *
        (∫ x in (((322 : ℝ)/512))..((((322+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_323 :
    (51237230 : ℝ) / 1000000000000000000 ≤
      ((323 : ℝ)/512)^2 *
        (∫ x in (((323 : ℝ)/512))..((((323+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_323).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((323 : ℝ)/512)^2 by positivity)
  have hn :
      (51237230 : ℝ) / 1000000000000000000 ≤
        ((323 : ℝ)/512)^2 *
          (160927599711/1250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (323/512 : ℝ) = ((323 : ℝ)/512) := by
    norm_num
  have hright :
      (81/128 : ℝ) = (((( 323+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((323 : ℝ)/512)^2 *
        (160927599711/1250000000000000000000 : ℝ) ≤
      ((323 : ℝ)/512)^2 *
        (∫ x in (((323 : ℝ)/512))..((((323+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_324 :
    (51589995 : ℝ) / 1000000000000000000 ≤
      ((324 : ℝ)/512)^2 *
        (∫ x in (((324 : ℝ)/512))..((((324+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_324).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((324 : ℝ)/512)^2 by positivity)
  have hn :
      (51589995 : ℝ) / 1000000000000000000 ≤
        ((324 : ℝ)/512)^2 *
          (515318080051/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (81/128 : ℝ) = ((324 : ℝ)/512) := by
    norm_num
  have hright :
      (325/512 : ℝ) = (((( 324+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((324 : ℝ)/512)^2 *
        (515318080051/4000000000000000000000 : ℝ) ≤
      ((324 : ℝ)/512)^2 *
        (∫ x in (((324 : ℝ)/512))..((((324+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_325 :
    (51928450 : ℝ) / 1000000000000000000 ≤
      ((325 : ℝ)/512)^2 *
        (∫ x in (((325 : ℝ)/512))..((((325+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_325).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((325 : ℝ)/512)^2 by positivity)
  have hn :
      (51928450 : ℝ) / 1000000000000000000 ≤
        ((325 : ℝ)/512)^2 *
          (12887793404713/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (325/512 : ℝ) = ((325 : ℝ)/512) := by
    norm_num
  have hright :
      (163/256 : ℝ) = (((( 325+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((325 : ℝ)/512)^2 *
        (12887793404713/100000000000000000000000 : ℝ) ≤
      ((325 : ℝ)/512)^2 *
        (∫ x in (((325 : ℝ)/512))..((((325+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_326 :
    (52252297 : ℝ) / 1000000000000000000 ≤
      ((326 : ℝ)/512)^2 *
        (∫ x in (((326 : ℝ)/512))..((((326+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_326).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((326 : ℝ)/512)^2 by positivity)
  have hn :
      (52252297 : ℝ) / 1000000000000000000 ≤
        ((326 : ℝ)/512)^2 *
          (1288872970723/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (163/256 : ℝ) = ((326 : ℝ)/512) := by
    norm_num
  have hright :
      (327/512 : ℝ) = (((( 326+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((326 : ℝ)/512)^2 *
        (1288872970723/10000000000000000000000 : ℝ) ≤
      ((326 : ℝ)/512)^2 *
        (∫ x in (((326 : ℝ)/512))..((((326+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_327 :
    (52561249 : ℝ) / 1000000000000000000 ≤
      ((327 : ℝ)/512)^2 *
        (∫ x in (((327 : ℝ)/512))..((((327+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_327).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((327 : ℝ)/512)^2 by positivity)
  have hn :
      (52561249 : ℝ) / 1000000000000000000 ≤
        ((327 : ℝ)/512)^2 *
          (515430474001/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (327/512 : ℝ) = ((327 : ℝ)/512) := by
    norm_num
  have hright :
      (41/64 : ℝ) = (((( 327+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((327 : ℝ)/512)^2 *
        (515430474001/4000000000000000000000 : ℝ) ≤
      ((327 : ℝ)/512)^2 *
        (∫ x in (((327 : ℝ)/512))..((((327+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_328 :
    (52855032 : ℝ) / 1000000000000000000 ≤
      ((328 : ℝ)/512)^2 *
        (∫ x in (((328 : ℝ)/512))..((((328+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_328).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((328 : ℝ)/512)^2 by positivity)
  have hn :
      (52855032 : ℝ) / 1000000000000000000 ≤
        ((328 : ℝ)/512)^2 *
          (40246544351/312500000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (41/64 : ℝ) = ((328 : ℝ)/512) := by
    norm_num
  have hright :
      (329/512 : ℝ) = (((( 328+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((328 : ℝ)/512)^2 *
        (40246544351/312500000000000000000 : ℝ) ≤
      ((328 : ℝ)/512)^2 *
        (∫ x in (((328 : ℝ)/512))..((((328+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_329 :
    (53133382 : ℝ) / 1000000000000000000 ≤
      ((329 : ℝ)/512)^2 *
        (∫ x in (((329 : ℝ)/512))..((((329+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_329).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((329 : ℝ)/512)^2 by positivity)
  have hn :
      (53133382 : ℝ) / 1000000000000000000 ≤
        ((329 : ℝ)/512)^2 *
          (12868134503413/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (329/512 : ℝ) = ((329 : ℝ)/512) := by
    norm_num
  have hright :
      (165/256 : ℝ) = (((( 329+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((329 : ℝ)/512)^2 *
        (12868134503413/100000000000000000000000 : ℝ) ≤
      ((329 : ℝ)/512)^2 *
        (∫ x in (((329 : ℝ)/512))..((((329+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_330 :
    (53396052 : ℝ) / 1000000000000000000 ≤
      ((330 : ℝ)/512)^2 *
        (∫ x in (((330 : ℝ)/512))..((((330+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_330).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((330 : ℝ)/512)^2 by positivity)
  have hn :
      (53396052 : ℝ) / 1000000000000000000 ≤
        ((330 : ℝ)/512)^2 *
          (3213373487489/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (165/256 : ℝ) = ((330 : ℝ)/512) := by
    norm_num
  have hright :
      (331/512 : ℝ) = (((( 330+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((330 : ℝ)/512)^2 *
        (3213373487489/25000000000000000000000 : ℝ) ≤
      ((330 : ℝ)/512)^2 *
        (∫ x in (((330 : ℝ)/512))..((((330+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_331 :
    (53642807 : ℝ) / 1000000000000000000 ≤
      ((331 : ℝ)/512)^2 *
        (∫ x in (((331 : ℝ)/512))..((((331+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_331).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((331 : ℝ)/512)^2 by positivity)
  have hn :
      (53642807 : ℝ) / 1000000000000000000 ≤
        ((331 : ℝ)/512)^2 *
          (200546673101/1562500000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (331/512 : ℝ) = ((331 : ℝ)/512) := by
    norm_num
  have hright :
      (83/128 : ℝ) = (((( 331+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((331 : ℝ)/512)^2 *
        (200546673101/1562500000000000000000 : ℝ) ≤
      ((331 : ℝ)/512)^2 *
        (∫ x in (((331 : ℝ)/512))..((((331+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_332 :
    (53873425 : ℝ) / 1000000000000000000 ≤
      ((332 : ℝ)/512)^2 *
        (∫ x in (((332 : ℝ)/512))..((((332+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_332).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((332 : ℝ)/512)^2 by positivity)
  have hn :
      (53873425 : ℝ) / 1000000000000000000 ≤
        ((332 : ℝ)/512)^2 *
          (2562526358623/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (83/128 : ℝ) = ((332 : ℝ)/512) := by
    norm_num
  have hright :
      (333/512 : ℝ) = (((( 332+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((332 : ℝ)/512)^2 *
        (2562526358623/20000000000000000000000 : ℝ) ≤
      ((332 : ℝ)/512)^2 *
        (∫ x in (((332 : ℝ)/512))..((((332+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_333 :
    (54087699 : ℝ) / 1000000000000000000 ≤
      ((333 : ℝ)/512)^2 *
        (∫ x in (((333 : ℝ)/512))..((((333+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_333).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((333 : ℝ)/512)^2 by positivity)
  have hn :
      (54087699 : ℝ) / 1000000000000000000 ≤
        ((333 : ℝ)/512)^2 *
          (639322466443/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (333/512 : ℝ) = ((333 : ℝ)/512) := by
    norm_num
  have hright :
      (167/256 : ℝ) = (((( 333+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((333 : ℝ)/512)^2 *
        (639322466443/5000000000000000000000 : ℝ) ≤
      ((333 : ℝ)/512)^2 *
        (∫ x in (((333 : ℝ)/512))..((((333+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_334 :
    (54285435 : ℝ) / 1000000000000000000 ≤
      ((334 : ℝ)/512)^2 *
        (∫ x in (((334 : ℝ)/512))..((((334+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_334).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((334 : ℝ)/512)^2 by positivity)
  have hn :
      (54285435 : ℝ) / 1000000000000000000 ≤
        ((334 : ℝ)/512)^2 *
          (12756464219917/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (167/256 : ℝ) = ((334 : ℝ)/512) := by
    norm_num
  have hright :
      (335/512 : ℝ) = (((( 334+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((334 : ℝ)/512)^2 *
        (12756464219917/100000000000000000000000 : ℝ) ≤
      ((334 : ℝ)/512)^2 *
        (∫ x in (((334 : ℝ)/512))..((((334+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_335 :
    (54466456 : ℝ) / 1000000000000000000 ≤
      ((335 : ℝ)/512)^2 *
        (∫ x in (((335 : ℝ)/512))..((((335+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_335).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((335 : ℝ)/512)^2 by positivity)
  have hn :
      (54466456 : ℝ) / 1000000000000000000 ≤
        ((335 : ℝ)/512)^2 *
          (6361352131847/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (335/512 : ℝ) = ((335 : ℝ)/512) := by
    norm_num
  have hright :
      (21/32 : ℝ) = (((( 335+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((335 : ℝ)/512)^2 *
        (6361352131847/50000000000000000000000 : ℝ) ≤
      ((335 : ℝ)/512)^2 *
        (∫ x in (((335 : ℝ)/512))..((((335+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_336 :
    (54630599 : ℝ) / 1000000000000000000 ≤
      ((336 : ℝ)/512)^2 *
        (∫ x in (((336 : ℝ)/512))..((((336+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_336).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((336 : ℝ)/512)^2 by positivity)
  have hn :
      (54630599 : ℝ) / 1000000000000000000 ≤
        ((336 : ℝ)/512)^2 *
          (6342600240109/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (21/32 : ℝ) = ((336 : ℝ)/512) := by
    norm_num
  have hright :
      (337/512 : ℝ) = (((( 336+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((336 : ℝ)/512)^2 *
        (6342600240109/50000000000000000000000 : ℝ) ≤
      ((336 : ℝ)/512)^2 *
        (∫ x in (((336 : ℝ)/512))..((((336+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_337 :
    (54777716 : ℝ) / 1000000000000000000 ≤
      ((337 : ℝ)/512)^2 *
        (∫ x in (((337 : ℝ)/512))..((((337+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_337).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((337 : ℝ)/512)^2 by positivity)
  have hn :
      (54777716 : ℝ) / 1000000000000000000 ≤
        ((337 : ℝ)/512)^2 *
          (790249191697/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (337/512 : ℝ) = ((337 : ℝ)/512) := by
    norm_num
  have hright :
      (169/256 : ℝ) = (((( 337+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((337 : ℝ)/512)^2 *
        (790249191697/6250000000000000000000 : ℝ) ≤
      ((337 : ℝ)/512)^2 *
        (∫ x in (((337 : ℝ)/512))..((((337+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_338 :
    (54907674 : ℝ) / 1000000000000000000 ≤
      ((338 : ℝ)/512)^2 *
        (∫ x in (((338 : ℝ)/512))..((((338+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_338).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((338 : ℝ)/512)^2 by positivity)
  have hn :
      (54907674 : ℝ) / 1000000000000000000 ≤
        ((338 : ℝ)/512)^2 *
          (157488766881/1250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (169/256 : ℝ) = ((338 : ℝ)/512) := by
    norm_num
  have hright :
      (339/512 : ℝ) = (((( 338+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((338 : ℝ)/512)^2 *
        (157488766881/1250000000000000000000 : ℝ) ≤
      ((338 : ℝ)/512)^2 *
        (∫ x in (((338 : ℝ)/512))..((((338+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_339 :
    (55020356 : ℝ) / 1000000000000000000 ≤
      ((339 : ℝ)/512)^2 *
        (∫ x in (((339 : ℝ)/512))..((((339+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_339).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((339 : ℝ)/512)^2 by positivity)
  have hn :
      (55020356 : ℝ) / 1000000000000000000 ≤
        ((339 : ℝ)/512)^2 *
          (1568822966369/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (339/512 : ℝ) = ((339 : ℝ)/512) := by
    norm_num
  have hright :
      (85/128 : ℝ) = (((( 339+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((339 : ℝ)/512)^2 *
        (1568822966369/12500000000000000000000 : ℝ) ≤
      ((339 : ℝ)/512)^2 *
        (∫ x in (((339 : ℝ)/512))..((((339+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_340 :
    (55115662 : ℝ) / 1000000000000000000 ≤
      ((340 : ℝ)/512)^2 *
        (∫ x in (((340 : ℝ)/512))..((((340+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_340).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((340 : ℝ)/512)^2 by positivity)
  have hn :
      (55115662 : ℝ) / 1000000000000000000 ≤
        ((340 : ℝ)/512)^2 *
          (2499695525281/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (85/128 : ℝ) = ((340 : ℝ)/512) := by
    norm_num
  have hright :
      (341/512 : ℝ) = (((( 340+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((340 : ℝ)/512)^2 *
        (2499695525281/20000000000000000000000 : ℝ) ≤
      ((340 : ℝ)/512)^2 *
        (∫ x in (((340 : ℝ)/512))..((((340+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_341 :
    (55193506 : ℝ) / 1000000000000000000 ≤
      ((341 : ℝ)/512)^2 *
        (∫ x in (((341 : ℝ)/512))..((((341+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_341).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((341 : ℝ)/512)^2 by positivity)
  have hn :
      (55193506 : ℝ) / 1000000000000000000 ≤
        ((341 : ℝ)/512)^2 *
          (12442829410051/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (341/512 : ℝ) = ((341 : ℝ)/512) := by
    norm_num
  have hright :
      (171/256 : ℝ) = (((( 341+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((341 : ℝ)/512)^2 *
        (12442829410051/100000000000000000000000 : ℝ) ≤
      ((341 : ℝ)/512)^2 *
        (∫ x in (((341 : ℝ)/512))..((((341+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_342 :
    (55253819 : ℝ) / 1000000000000000000 ≤
      ((342 : ℝ)/512)^2 *
        (∫ x in (((342 : ℝ)/512))..((((342+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_342).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((342 : ℝ)/512)^2 by positivity)
  have hn :
      (55253819 : ℝ) / 1000000000000000000 ≤
        ((342 : ℝ)/512)^2 *
          (2476737668973/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (171/256 : ℝ) = ((342 : ℝ)/512) := by
    norm_num
  have hright :
      (343/512 : ℝ) = (((( 342+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((342 : ℝ)/512)^2 *
        (2476737668973/20000000000000000000000 : ℝ) ≤
      ((342 : ℝ)/512)^2 *
        (∫ x in (((342 : ℝ)/512))..((((342+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_343 :
    (55296549 : ℝ) / 1000000000000000000 ≤
      ((343 : ℝ)/512)^2 *
        (∫ x in (((343 : ℝ)/512))..((((343+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_343).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((343 : ℝ)/512)^2 by positivity)
  have hn :
      (55296549 : ℝ) / 1000000000000000000 ≤
        ((343 : ℝ)/512)^2 *
          (12321106514187/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (343/512 : ℝ) = ((343 : ℝ)/512) := by
    norm_num
  have hright :
      (43/64 : ℝ) = (((( 343+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((343 : ℝ)/512)^2 *
        (12321106514187/100000000000000000000000 : ℝ) ≤
      ((343 : ℝ)/512)^2 *
        (∫ x in (((343 : ℝ)/512))..((((343+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_344 :
    (55321659 : ℝ) / 1000000000000000000 ≤
      ((344 : ℝ)/512)^2 *
        (∫ x in (((344 : ℝ)/512))..((((344+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_344).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((344 : ℝ)/512)^2 by positivity)
  have hn :
      (55321659 : ℝ) / 1000000000000000000 ≤
        ((344 : ℝ)/512)^2 *
          (6127569374337/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (43/64 : ℝ) = ((344 : ℝ)/512) := by
    norm_num
  have hright :
      (345/512 : ℝ) = (((( 344+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((344 : ℝ)/512)^2 *
        (6127569374337/50000000000000000000000 : ℝ) ≤
      ((344 : ℝ)/512)^2 *
        (∫ x in (((344 : ℝ)/512))..((((344+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_345 :
    (55329128 : ℝ) / 1000000000000000000 ≤
      ((345 : ℝ)/512)^2 *
        (∫ x in (((345 : ℝ)/512))..((((345+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_345).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((345 : ℝ)/512)^2 by positivity)
  have hn :
      (55329128 : ℝ) / 1000000000000000000 ≤
        ((345 : ℝ)/512)^2 *
          (6092921274867/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (345/512 : ℝ) = ((345 : ℝ)/512) := by
    norm_num
  have hright :
      (173/256 : ℝ) = (((( 345+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((345 : ℝ)/512)^2 *
        (6092921274867/50000000000000000000000 : ℝ) ≤
      ((345 : ℝ)/512)^2 *
        (∫ x in (((345 : ℝ)/512))..((((345+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_346 :
    (55318954 : ℝ) / 1000000000000000000 ≤
      ((346 : ℝ)/512)^2 *
        (∫ x in (((346 : ℝ)/512))..((((346+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_346).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((346 : ℝ)/512)^2 by positivity)
  have hn :
      (55318954 : ℝ) / 1000000000000000000 ≤
        ((346 : ℝ)/512)^2 *
          (12113278009589/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (173/256 : ℝ) = ((346 : ℝ)/512) := by
    norm_num
  have hright :
      (347/512 : ℝ) = (((( 346+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((346 : ℝ)/512)^2 *
        (12113278009589/100000000000000000000000 : ℝ) ≤
      ((346 : ℝ)/512)^2 *
        (∫ x in (((346 : ℝ)/512))..((((346+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_347 :
    (55291147 : ℝ) / 1000000000000000000 ≤
      ((347 : ℝ)/512)^2 *
        (∫ x in (((347 : ℝ)/512))..((((347+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_347).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((347 : ℝ)/512)^2 by positivity)
  have hn :
      (55291147 : ℝ) / 1000000000000000000 ≤
        ((347 : ℝ)/512)^2 *
          (300937693203/2500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (347/512 : ℝ) = ((347 : ℝ)/512) := by
    norm_num
  have hright :
      (87/128 : ℝ) = (((( 347+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((347 : ℝ)/512)^2 *
        (300937693203/2500000000000000000000 : ℝ) ≤
      ((347 : ℝ)/512)^2 *
        (∫ x in (((347 : ℝ)/512))..((((347+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_348 :
    (55245738 : ℝ) / 1000000000000000000 ≤
      ((348 : ℝ)/512)^2 *
        (∫ x in (((348 : ℝ)/512))..((((348+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_348).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((348 : ℝ)/512)^2 by positivity)
  have hn :
      (55245738 : ℝ) / 1000000000000000000 ≤
        ((348 : ℝ)/512)^2 *
          (5979298363317/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (87/128 : ℝ) = ((348 : ℝ)/512) := by
    norm_num
  have hright :
      (349/512 : ℝ) = (((( 348+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((348 : ℝ)/512)^2 *
        (5979298363317/50000000000000000000000 : ℝ) ≤
      ((348 : ℝ)/512)^2 *
        (∫ x in (((348 : ℝ)/512))..((((348+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_349 :
    (55182772 : ℝ) / 1000000000000000000 ≤
      ((349 : ℝ)/512)^2 *
        (∫ x in (((349 : ℝ)/512))..((((349+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_349).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((349 : ℝ)/512)^2 by positivity)
  have hn :
      (55182772 : ℝ) / 1000000000000000000 ≤
        ((349 : ℝ)/512)^2 *
          (11876612358733/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (349/512 : ℝ) = ((349 : ℝ)/512) := by
    norm_num
  have hright :
      (175/256 : ℝ) = (((( 349+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((349 : ℝ)/512)^2 *
        (11876612358733/100000000000000000000000 : ℝ) ≤
      ((349 : ℝ)/512)^2 *
        (∫ x in (((349 : ℝ)/512))..((((349+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_350 :
    (55102308 : ℝ) / 1000000000000000000 ≤
      ((350 : ℝ)/512)^2 *
        (∫ x in (((350 : ℝ)/512))..((((350+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_350).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((350 : ℝ)/512)^2 by positivity)
  have hn :
      (55102308 : ℝ) / 1000000000000000000 ≤
        ((350 : ℝ)/512)^2 *
          (5895812109213/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (175/256 : ℝ) = ((350 : ℝ)/512) := by
    norm_num
  have hright :
      (351/512 : ℝ) = (((( 350+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((350 : ℝ)/512)^2 *
        (5895812109213/50000000000000000000000 : ℝ) ≤
      ((350 : ℝ)/512)^2 *
        (∫ x in (((350 : ℝ)/512))..((((350+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_351 :
    (55004426 : ℝ) / 1000000000000000000 ≤
      ((351 : ℝ)/512)^2 *
        (∫ x in (((351 : ℝ)/512))..((((351+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_351).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((351 : ℝ)/512)^2 by positivity)
  have hn :
      (55004426 : ℝ) / 1000000000000000000 ≤
        ((351 : ℝ)/512)^2 *
          (5851852022837/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (351/512 : ℝ) = ((351 : ℝ)/512) := by
    norm_num
  have hright :
      (11/16 : ℝ) = (((( 351+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((351 : ℝ)/512)^2 *
        (5851852022837/50000000000000000000000 : ℝ) ≤
      ((351 : ℝ)/512)^2 *
        (∫ x in (((351 : ℝ)/512))..((((351+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
