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
        (∫ x in (5/8:ℝ)..(321/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_320).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((320 : ℝ)/512)^2 by positivity)
  have hn :
      (50096235 : ℝ) / 1000000000000000000 ≤
        ((320 : ℝ)/512)^2 *
          (12824636226481/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((320 : ℝ)/512)^2 *
        (12824636226481/100000000000000000000000 : ℝ) ≤
      ((320 : ℝ)/512)^2 *
        (∫ x in (5/8:ℝ)..(321/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_321 :
    (50490023 : ℝ) / 1000000000000000000 ≤
      ((321 : ℝ)/512)^2 *
        (∫ x in (321/512:ℝ)..(161/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_321).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((321 : ℝ)/512)^2 by positivity)
  have hn :
      (50490023 : ℝ) / 1000000000000000000 ≤
        ((321 : ℝ)/512)^2 *
          (12845039076109/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((321 : ℝ)/512)^2 *
        (12845039076109/100000000000000000000000 : ℝ) ≤
      ((321 : ℝ)/512)^2 *
        (∫ x in (321/512:ℝ)..(161/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_322 :
    (50870465 : ℝ) / 1000000000000000000 ≤
      ((322 : ℝ)/512)^2 *
        (∫ x in (161/256:ℝ)..(323/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_322).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((322 : ℝ)/512)^2 by positivity)
  have hn :
      (50870465 : ℝ) / 1000000000000000000 ≤
        ((322 : ℝ)/512)^2 *
          (6430783615497/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((322 : ℝ)/512)^2 *
        (6430783615497/50000000000000000000000 : ℝ) ≤
      ((322 : ℝ)/512)^2 *
        (∫ x in (161/256:ℝ)..(323/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_323 :
    (51237230 : ℝ) / 1000000000000000000 ≤
      ((323 : ℝ)/512)^2 *
        (∫ x in (323/512:ℝ)..(81/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_323).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((323 : ℝ)/512)^2 by positivity)
  have hn :
      (51237230 : ℝ) / 1000000000000000000 ≤
        ((323 : ℝ)/512)^2 *
          (160927599711/1250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((323 : ℝ)/512)^2 *
        (160927599711/1250000000000000000000 : ℝ) ≤
      ((323 : ℝ)/512)^2 *
        (∫ x in (323/512:ℝ)..(81/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_324 :
    (51589995 : ℝ) / 1000000000000000000 ≤
      ((324 : ℝ)/512)^2 *
        (∫ x in (81/128:ℝ)..(325/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_324).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((324 : ℝ)/512)^2 by positivity)
  have hn :
      (51589995 : ℝ) / 1000000000000000000 ≤
        ((324 : ℝ)/512)^2 *
          (515318080051/4000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((324 : ℝ)/512)^2 *
        (515318080051/4000000000000000000000 : ℝ) ≤
      ((324 : ℝ)/512)^2 *
        (∫ x in (81/128:ℝ)..(325/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_325 :
    (51928450 : ℝ) / 1000000000000000000 ≤
      ((325 : ℝ)/512)^2 *
        (∫ x in (325/512:ℝ)..(163/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_325).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((325 : ℝ)/512)^2 by positivity)
  have hn :
      (51928450 : ℝ) / 1000000000000000000 ≤
        ((325 : ℝ)/512)^2 *
          (12887793404713/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((325 : ℝ)/512)^2 *
        (12887793404713/100000000000000000000000 : ℝ) ≤
      ((325 : ℝ)/512)^2 *
        (∫ x in (325/512:ℝ)..(163/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_326 :
    (52252297 : ℝ) / 1000000000000000000 ≤
      ((326 : ℝ)/512)^2 *
        (∫ x in (163/256:ℝ)..(327/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_326).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((326 : ℝ)/512)^2 by positivity)
  have hn :
      (52252297 : ℝ) / 1000000000000000000 ≤
        ((326 : ℝ)/512)^2 *
          (1288872970723/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((326 : ℝ)/512)^2 *
        (1288872970723/10000000000000000000000 : ℝ) ≤
      ((326 : ℝ)/512)^2 *
        (∫ x in (163/256:ℝ)..(327/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_327 :
    (52561249 : ℝ) / 1000000000000000000 ≤
      ((327 : ℝ)/512)^2 *
        (∫ x in (327/512:ℝ)..(41/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_327).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((327 : ℝ)/512)^2 by positivity)
  have hn :
      (52561249 : ℝ) / 1000000000000000000 ≤
        ((327 : ℝ)/512)^2 *
          (515430474001/4000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((327 : ℝ)/512)^2 *
        (515430474001/4000000000000000000000 : ℝ) ≤
      ((327 : ℝ)/512)^2 *
        (∫ x in (327/512:ℝ)..(41/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_328 :
    (52855032 : ℝ) / 1000000000000000000 ≤
      ((328 : ℝ)/512)^2 *
        (∫ x in (41/64:ℝ)..(329/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_328).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((328 : ℝ)/512)^2 by positivity)
  have hn :
      (52855032 : ℝ) / 1000000000000000000 ≤
        ((328 : ℝ)/512)^2 *
          (40246544351/312500000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((328 : ℝ)/512)^2 *
        (40246544351/312500000000000000000 : ℝ) ≤
      ((328 : ℝ)/512)^2 *
        (∫ x in (41/64:ℝ)..(329/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_329 :
    (53133382 : ℝ) / 1000000000000000000 ≤
      ((329 : ℝ)/512)^2 *
        (∫ x in (329/512:ℝ)..(165/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_329).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((329 : ℝ)/512)^2 by positivity)
  have hn :
      (53133382 : ℝ) / 1000000000000000000 ≤
        ((329 : ℝ)/512)^2 *
          (12868134503413/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((329 : ℝ)/512)^2 *
        (12868134503413/100000000000000000000000 : ℝ) ≤
      ((329 : ℝ)/512)^2 *
        (∫ x in (329/512:ℝ)..(165/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_330 :
    (53396052 : ℝ) / 1000000000000000000 ≤
      ((330 : ℝ)/512)^2 *
        (∫ x in (165/256:ℝ)..(331/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_330).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((330 : ℝ)/512)^2 by positivity)
  have hn :
      (53396052 : ℝ) / 1000000000000000000 ≤
        ((330 : ℝ)/512)^2 *
          (3213373487489/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((330 : ℝ)/512)^2 *
        (3213373487489/25000000000000000000000 : ℝ) ≤
      ((330 : ℝ)/512)^2 *
        (∫ x in (165/256:ℝ)..(331/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_331 :
    (53642807 : ℝ) / 1000000000000000000 ≤
      ((331 : ℝ)/512)^2 *
        (∫ x in (331/512:ℝ)..(83/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_331).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((331 : ℝ)/512)^2 by positivity)
  have hn :
      (53642807 : ℝ) / 1000000000000000000 ≤
        ((331 : ℝ)/512)^2 *
          (200546673101/1562500000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((331 : ℝ)/512)^2 *
        (200546673101/1562500000000000000000 : ℝ) ≤
      ((331 : ℝ)/512)^2 *
        (∫ x in (331/512:ℝ)..(83/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_332 :
    (53873425 : ℝ) / 1000000000000000000 ≤
      ((332 : ℝ)/512)^2 *
        (∫ x in (83/128:ℝ)..(333/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_332).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((332 : ℝ)/512)^2 by positivity)
  have hn :
      (53873425 : ℝ) / 1000000000000000000 ≤
        ((332 : ℝ)/512)^2 *
          (2562526358623/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((332 : ℝ)/512)^2 *
        (2562526358623/20000000000000000000000 : ℝ) ≤
      ((332 : ℝ)/512)^2 *
        (∫ x in (83/128:ℝ)..(333/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_333 :
    (54087699 : ℝ) / 1000000000000000000 ≤
      ((333 : ℝ)/512)^2 *
        (∫ x in (333/512:ℝ)..(167/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_333).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((333 : ℝ)/512)^2 by positivity)
  have hn :
      (54087699 : ℝ) / 1000000000000000000 ≤
        ((333 : ℝ)/512)^2 *
          (639322466443/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((333 : ℝ)/512)^2 *
        (639322466443/5000000000000000000000 : ℝ) ≤
      ((333 : ℝ)/512)^2 *
        (∫ x in (333/512:ℝ)..(167/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_334 :
    (54285435 : ℝ) / 1000000000000000000 ≤
      ((334 : ℝ)/512)^2 *
        (∫ x in (167/256:ℝ)..(335/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_334).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((334 : ℝ)/512)^2 by positivity)
  have hn :
      (54285435 : ℝ) / 1000000000000000000 ≤
        ((334 : ℝ)/512)^2 *
          (12756464219917/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((334 : ℝ)/512)^2 *
        (12756464219917/100000000000000000000000 : ℝ) ≤
      ((334 : ℝ)/512)^2 *
        (∫ x in (167/256:ℝ)..(335/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_335 :
    (54466456 : ℝ) / 1000000000000000000 ≤
      ((335 : ℝ)/512)^2 *
        (∫ x in (335/512:ℝ)..(21/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_335).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((335 : ℝ)/512)^2 by positivity)
  have hn :
      (54466456 : ℝ) / 1000000000000000000 ≤
        ((335 : ℝ)/512)^2 *
          (6361352131847/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((335 : ℝ)/512)^2 *
        (6361352131847/50000000000000000000000 : ℝ) ≤
      ((335 : ℝ)/512)^2 *
        (∫ x in (335/512:ℝ)..(21/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_336 :
    (54630599 : ℝ) / 1000000000000000000 ≤
      ((336 : ℝ)/512)^2 *
        (∫ x in (21/32:ℝ)..(337/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_336).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((336 : ℝ)/512)^2 by positivity)
  have hn :
      (54630599 : ℝ) / 1000000000000000000 ≤
        ((336 : ℝ)/512)^2 *
          (6342600240109/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((336 : ℝ)/512)^2 *
        (6342600240109/50000000000000000000000 : ℝ) ≤
      ((336 : ℝ)/512)^2 *
        (∫ x in (21/32:ℝ)..(337/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_337 :
    (54777716 : ℝ) / 1000000000000000000 ≤
      ((337 : ℝ)/512)^2 *
        (∫ x in (337/512:ℝ)..(169/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_337).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((337 : ℝ)/512)^2 by positivity)
  have hn :
      (54777716 : ℝ) / 1000000000000000000 ≤
        ((337 : ℝ)/512)^2 *
          (790249191697/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((337 : ℝ)/512)^2 *
        (790249191697/6250000000000000000000 : ℝ) ≤
      ((337 : ℝ)/512)^2 *
        (∫ x in (337/512:ℝ)..(169/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_338 :
    (54907674 : ℝ) / 1000000000000000000 ≤
      ((338 : ℝ)/512)^2 *
        (∫ x in (169/256:ℝ)..(339/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_338).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((338 : ℝ)/512)^2 by positivity)
  have hn :
      (54907674 : ℝ) / 1000000000000000000 ≤
        ((338 : ℝ)/512)^2 *
          (157488766881/1250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((338 : ℝ)/512)^2 *
        (157488766881/1250000000000000000000 : ℝ) ≤
      ((338 : ℝ)/512)^2 *
        (∫ x in (169/256:ℝ)..(339/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_339 :
    (55020356 : ℝ) / 1000000000000000000 ≤
      ((339 : ℝ)/512)^2 *
        (∫ x in (339/512:ℝ)..(85/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_339).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((339 : ℝ)/512)^2 by positivity)
  have hn :
      (55020356 : ℝ) / 1000000000000000000 ≤
        ((339 : ℝ)/512)^2 *
          (1568822966369/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((339 : ℝ)/512)^2 *
        (1568822966369/12500000000000000000000 : ℝ) ≤
      ((339 : ℝ)/512)^2 *
        (∫ x in (339/512:ℝ)..(85/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_340 :
    (55115662 : ℝ) / 1000000000000000000 ≤
      ((340 : ℝ)/512)^2 *
        (∫ x in (85/128:ℝ)..(341/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_340).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((340 : ℝ)/512)^2 by positivity)
  have hn :
      (55115662 : ℝ) / 1000000000000000000 ≤
        ((340 : ℝ)/512)^2 *
          (2499695525281/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((340 : ℝ)/512)^2 *
        (2499695525281/20000000000000000000000 : ℝ) ≤
      ((340 : ℝ)/512)^2 *
        (∫ x in (85/128:ℝ)..(341/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_341 :
    (55193506 : ℝ) / 1000000000000000000 ≤
      ((341 : ℝ)/512)^2 *
        (∫ x in (341/512:ℝ)..(171/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_341).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((341 : ℝ)/512)^2 by positivity)
  have hn :
      (55193506 : ℝ) / 1000000000000000000 ≤
        ((341 : ℝ)/512)^2 *
          (12442829410051/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((341 : ℝ)/512)^2 *
        (12442829410051/100000000000000000000000 : ℝ) ≤
      ((341 : ℝ)/512)^2 *
        (∫ x in (341/512:ℝ)..(171/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_342 :
    (55253819 : ℝ) / 1000000000000000000 ≤
      ((342 : ℝ)/512)^2 *
        (∫ x in (171/256:ℝ)..(343/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_342).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((342 : ℝ)/512)^2 by positivity)
  have hn :
      (55253819 : ℝ) / 1000000000000000000 ≤
        ((342 : ℝ)/512)^2 *
          (2476737668973/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((342 : ℝ)/512)^2 *
        (2476737668973/20000000000000000000000 : ℝ) ≤
      ((342 : ℝ)/512)^2 *
        (∫ x in (171/256:ℝ)..(343/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_343 :
    (55296549 : ℝ) / 1000000000000000000 ≤
      ((343 : ℝ)/512)^2 *
        (∫ x in (343/512:ℝ)..(43/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_343).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((343 : ℝ)/512)^2 by positivity)
  have hn :
      (55296549 : ℝ) / 1000000000000000000 ≤
        ((343 : ℝ)/512)^2 *
          (12321106514187/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((343 : ℝ)/512)^2 *
        (12321106514187/100000000000000000000000 : ℝ) ≤
      ((343 : ℝ)/512)^2 *
        (∫ x in (343/512:ℝ)..(43/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_344 :
    (55321659 : ℝ) / 1000000000000000000 ≤
      ((344 : ℝ)/512)^2 *
        (∫ x in (43/64:ℝ)..(345/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_344).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((344 : ℝ)/512)^2 by positivity)
  have hn :
      (55321659 : ℝ) / 1000000000000000000 ≤
        ((344 : ℝ)/512)^2 *
          (6127569374337/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((344 : ℝ)/512)^2 *
        (6127569374337/50000000000000000000000 : ℝ) ≤
      ((344 : ℝ)/512)^2 *
        (∫ x in (43/64:ℝ)..(345/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_345 :
    (55329128 : ℝ) / 1000000000000000000 ≤
      ((345 : ℝ)/512)^2 *
        (∫ x in (345/512:ℝ)..(173/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_345).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((345 : ℝ)/512)^2 by positivity)
  have hn :
      (55329128 : ℝ) / 1000000000000000000 ≤
        ((345 : ℝ)/512)^2 *
          (6092921274867/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((345 : ℝ)/512)^2 *
        (6092921274867/50000000000000000000000 : ℝ) ≤
      ((345 : ℝ)/512)^2 *
        (∫ x in (345/512:ℝ)..(173/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_346 :
    (55318954 : ℝ) / 1000000000000000000 ≤
      ((346 : ℝ)/512)^2 *
        (∫ x in (173/256:ℝ)..(347/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_346).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((346 : ℝ)/512)^2 by positivity)
  have hn :
      (55318954 : ℝ) / 1000000000000000000 ≤
        ((346 : ℝ)/512)^2 *
          (12113278009589/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((346 : ℝ)/512)^2 *
        (12113278009589/100000000000000000000000 : ℝ) ≤
      ((346 : ℝ)/512)^2 *
        (∫ x in (173/256:ℝ)..(347/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_347 :
    (55291147 : ℝ) / 1000000000000000000 ≤
      ((347 : ℝ)/512)^2 *
        (∫ x in (347/512:ℝ)..(87/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_347).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((347 : ℝ)/512)^2 by positivity)
  have hn :
      (55291147 : ℝ) / 1000000000000000000 ≤
        ((347 : ℝ)/512)^2 *
          (300937693203/2500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((347 : ℝ)/512)^2 *
        (300937693203/2500000000000000000000 : ℝ) ≤
      ((347 : ℝ)/512)^2 *
        (∫ x in (347/512:ℝ)..(87/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_348 :
    (55245738 : ℝ) / 1000000000000000000 ≤
      ((348 : ℝ)/512)^2 *
        (∫ x in (87/128:ℝ)..(349/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_348).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((348 : ℝ)/512)^2 by positivity)
  have hn :
      (55245738 : ℝ) / 1000000000000000000 ≤
        ((348 : ℝ)/512)^2 *
          (5979298363317/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((348 : ℝ)/512)^2 *
        (5979298363317/50000000000000000000000 : ℝ) ≤
      ((348 : ℝ)/512)^2 *
        (∫ x in (87/128:ℝ)..(349/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_349 :
    (55182772 : ℝ) / 1000000000000000000 ≤
      ((349 : ℝ)/512)^2 *
        (∫ x in (349/512:ℝ)..(175/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_349).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((349 : ℝ)/512)^2 by positivity)
  have hn :
      (55182772 : ℝ) / 1000000000000000000 ≤
        ((349 : ℝ)/512)^2 *
          (11876612358733/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((349 : ℝ)/512)^2 *
        (11876612358733/100000000000000000000000 : ℝ) ≤
      ((349 : ℝ)/512)^2 *
        (∫ x in (349/512:ℝ)..(175/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_350 :
    (55102308 : ℝ) / 1000000000000000000 ≤
      ((350 : ℝ)/512)^2 *
        (∫ x in (175/256:ℝ)..(351/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_350).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((350 : ℝ)/512)^2 by positivity)
  have hn :
      (55102308 : ℝ) / 1000000000000000000 ≤
        ((350 : ℝ)/512)^2 *
          (5895812109213/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((350 : ℝ)/512)^2 *
        (5895812109213/50000000000000000000000 : ℝ) ≤
      ((350 : ℝ)/512)^2 *
        (∫ x in (175/256:ℝ)..(351/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_351 :
    (55004426 : ℝ) / 1000000000000000000 ≤
      ((351 : ℝ)/512)^2 *
        (∫ x in (351/512:ℝ)..(11/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_351).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((351 : ℝ)/512)^2 by positivity)
  have hn :
      (55004426 : ℝ) / 1000000000000000000 ≤
        ((351 : ℝ)/512)^2 *
          (5851852022837/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((351 : ℝ)/512)^2 *
        (5851852022837/50000000000000000000000 : ℝ) ≤
      ((351 : ℝ)/512)^2 *
        (∫ x in (351/512:ℝ)..(11/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
