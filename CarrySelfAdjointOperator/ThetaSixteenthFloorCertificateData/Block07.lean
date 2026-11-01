import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_07
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_224 :
    (4751443 : ℝ) / 1000000000000000000 ≤
      ((224 : ℝ)/512)^2 *
        (∫ x in (7/16:ℝ)..(225/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_224).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((224 : ℝ)/512)^2 by positivity)
  have hn :
      (4751443 : ℝ) / 1000000000000000000 ≤
        ((224 : ℝ)/512)^2 *
          (2482386996789/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((224 : ℝ)/512)^2 *
        (2482386996789/100000000000000000000000 : ℝ) ≤
      ((224 : ℝ)/512)^2 *
        (∫ x in (7/16:ℝ)..(225/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_225 :
    (4957994 : ℝ) / 1000000000000000000 ≤
      ((225 : ℝ)/512)^2 *
        (∫ x in (225/512:ℝ)..(113/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_225).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((225 : ℝ)/512)^2 by positivity)
  have hn :
      (4957994 : ℝ) / 1000000000000000000 ≤
        ((225 : ℝ)/512)^2 *
          (256732525397/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((225 : ℝ)/512)^2 *
        (256732525397/10000000000000000000000 : ℝ) ≤
      ((225 : ℝ)/512)^2 *
        (∫ x in (225/512:ℝ)..(113/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_226 :
    (5171296 : ℝ) / 1000000000000000000 ≤
      ((226 : ℝ)/512)^2 *
        (∫ x in (113/256:ℝ)..(227/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_226).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((226 : ℝ)/512)^2 by positivity)
  have hn :
      (5171296 : ℝ) / 1000000000000000000 ≤
        ((226 : ℝ)/512)^2 *
          (132706594417/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((226 : ℝ)/512)^2 *
        (132706594417/5000000000000000000000 : ℝ) ≤
      ((226 : ℝ)/512)^2 *
        (∫ x in (113/256:ℝ)..(227/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_227 :
    (5391467 : ℝ) / 1000000000000000000 ≤
      ((227 : ℝ)/512)^2 *
        (∫ x in (227/512:ℝ)..(57/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_227).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((227 : ℝ)/512)^2 by positivity)
  have hn :
      (5391467 : ℝ) / 1000000000000000000 ≤
        ((227 : ℝ)/512)^2 *
          (1371403236043/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((227 : ℝ)/512)^2 *
        (1371403236043/50000000000000000000000 : ℝ) ≤
      ((227 : ℝ)/512)^2 *
        (∫ x in (227/512:ℝ)..(57/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_228 :
    (5618617 : ℝ) / 1000000000000000000 ≤
      ((228 : ℝ)/512)^2 *
        (∫ x in (57/128:ℝ)..(229/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_228).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((228 : ℝ)/512)^2 by positivity)
  have hn :
      (5618617 : ℝ) / 1000000000000000000 ≤
        ((228 : ℝ)/512)^2 *
          (2833346779519/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((228 : ℝ)/512)^2 *
        (2833346779519/100000000000000000000000 : ℝ) ≤
      ((228 : ℝ)/512)^2 *
        (∫ x in (57/128:ℝ)..(229/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_229 :
    (5852859 : ℝ) / 1000000000000000000 ≤
      ((229 : ℝ)/512)^2 *
        (∫ x in (229/512:ℝ)..(115/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_229).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((229 : ℝ)/512)^2 by positivity)
  have hn :
      (5852859 : ℝ) / 1000000000000000000 ≤
        ((229 : ℝ)/512)^2 *
          (1462874371027/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((229 : ℝ)/512)^2 *
        (1462874371027/50000000000000000000000 : ℝ) ≤
      ((229 : ℝ)/512)^2 *
        (∫ x in (229/512:ℝ)..(115/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_230 :
    (6094296 : ℝ) / 1000000000000000000 ≤
      ((230 : ℝ)/512)^2 *
        (∫ x in (115/256:ℝ)..(231/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_230).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((230 : ℝ)/512)^2 by positivity)
  have hn :
      (6094296 : ℝ) / 1000000000000000000 ≤
        ((230 : ℝ)/512)^2 *
          (151000320243/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((230 : ℝ)/512)^2 *
        (151000320243/5000000000000000000000 : ℝ) ≤
      ((230 : ℝ)/512)^2 *
        (∫ x in (115/256:ℝ)..(231/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_231 :
    (6343034 : ℝ) / 1000000000000000000 ≤
      ((231 : ℝ)/512)^2 *
        (∫ x in (231/512:ℝ)..(29/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_231).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((231 : ℝ)/512)^2 by positivity)
  have hn :
      (6343034 : ℝ) / 1000000000000000000 ≤
        ((231 : ℝ)/512)^2 *
          (3116111885269/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((231 : ℝ)/512)^2 *
        (3116111885269/100000000000000000000000 : ℝ) ≤
      ((231 : ℝ)/512)^2 *
        (∫ x in (231/512:ℝ)..(29/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_232 :
    (6599171 : ℝ) / 1000000000000000000 ≤
      ((232 : ℝ)/512)^2 *
        (∫ x in (29/64:ℝ)..(233/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_232).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((232 : ℝ)/512)^2 by positivity)
  have hn :
      (6599171 : ℝ) / 1000000000000000000 ≤
        ((232 : ℝ)/512)^2 *
          (3214055333071/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((232 : ℝ)/512)^2 *
        (3214055333071/100000000000000000000000 : ℝ) ≤
      ((232 : ℝ)/512)^2 *
        (∫ x in (29/64:ℝ)..(233/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_233 :
    (6862802 : ℝ) / 1000000000000000000 ≤
      ((233 : ℝ)/512)^2 *
        (∫ x in (233/512:ℝ)..(117/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_233).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((233 : ℝ)/512)^2 by positivity)
  have hn :
      (6862802 : ℝ) / 1000000000000000000 ≤
        ((233 : ℝ)/512)^2 *
          (3313824892809/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((233 : ℝ)/512)^2 *
        (3313824892809/100000000000000000000000 : ℝ) ≤
      ((233 : ℝ)/512)^2 *
        (∫ x in (233/512:ℝ)..(117/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_234 :
    (7134018 : ℝ) / 1000000000000000000 ≤
      ((234 : ℝ)/512)^2 *
        (∫ x in (117/256:ℝ)..(235/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_234).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((234 : ℝ)/512)^2 by positivity)
  have hn :
      (7134018 : ℝ) / 1000000000000000000 ≤
        ((234 : ℝ)/512)^2 *
          (3415406668169/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((234 : ℝ)/512)^2 *
        (3415406668169/100000000000000000000000 : ℝ) ≤
      ((234 : ℝ)/512)^2 *
        (∫ x in (117/256:ℝ)..(235/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_235 :
    (7412906 : ℝ) / 1000000000000000000 ≤
      ((235 : ℝ)/512)^2 *
        (∫ x in (235/512:ℝ)..(59/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_235).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((235 : ℝ)/512)^2 by positivity)
  have hn :
      (7412906 : ℝ) / 1000000000000000000 ≤
        ((235 : ℝ)/512)^2 *
          (3518784688597/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((235 : ℝ)/512)^2 *
        (3518784688597/100000000000000000000000 : ℝ) ≤
      ((235 : ℝ)/512)^2 *
        (∫ x in (235/512:ℝ)..(59/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_236 :
    (7699547 : ℝ) / 1000000000000000000 ≤
      ((236 : ℝ)/512)^2 *
        (∫ x in (59/128:ℝ)..(237/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_236).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((236 : ℝ)/512)^2 by positivity)
  have hn :
      (7699547 : ℝ) / 1000000000000000000 ≤
        ((236 : ℝ)/512)^2 *
          (1811970439117/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((236 : ℝ)/512)^2 *
        (1811970439117/50000000000000000000000 : ℝ) ≤
      ((236 : ℝ)/512)^2 *
        (∫ x in (59/128:ℝ)..(237/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_237 :
    (7994018 : ℝ) / 1000000000000000000 ≤
      ((237 : ℝ)/512)^2 *
        (∫ x in (237/512:ℝ)..(119/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_237).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((237 : ℝ)/512)^2 by positivity)
  have hn :
      (7994018 : ℝ) / 1000000000000000000 ≤
        ((237 : ℝ)/512)^2 *
          (1865427513637/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((237 : ℝ)/512)^2 *
        (1865427513637/50000000000000000000000 : ℝ) ≤
      ((237 : ℝ)/512)^2 *
        (∫ x in (237/512:ℝ)..(119/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_238 :
    (8296390 : ℝ) / 1000000000000000000 ≤
      ((238 : ℝ)/512)^2 *
        (∫ x in (119/256:ℝ)..(239/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_238).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((238 : ℝ)/512)^2 by positivity)
  have hn :
      (8296390 : ℝ) / 1000000000000000000 ≤
        ((238 : ℝ)/512)^2 *
          (191975238293/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((238 : ℝ)/512)^2 *
        (191975238293/5000000000000000000000 : ℝ) ≤
      ((238 : ℝ)/512)^2 *
        (∫ x in (119/256:ℝ)..(239/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_239 :
    (8606730 : ℝ) / 1000000000000000000 ≤
      ((239 : ℝ)/512)^2 *
        (∫ x in (239/512:ℝ)..(15/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_239).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((239 : ℝ)/512)^2 by positivity)
  have hn :
      (8606730 : ℝ) / 1000000000000000000 ≤
        ((239 : ℝ)/512)^2 *
          (3949865540601/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((239 : ℝ)/512)^2 *
        (3949865540601/100000000000000000000000 : ℝ) ≤
      ((239 : ℝ)/512)^2 *
        (∫ x in (239/512:ℝ)..(15/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_240 :
    (8925096 : ℝ) / 1000000000000000000 ≤
      ((240 : ℝ)/512)^2 *
        (∫ x in (15/32:ℝ)..(241/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_240).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((240 : ℝ)/512)^2 by positivity)
  have hn :
      (8925096 : ℝ) / 1000000000000000000 ≤
        ((240 : ℝ)/512)^2 *
          (4061910593817/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((240 : ℝ)/512)^2 *
        (4061910593817/100000000000000000000000 : ℝ) ≤
      ((240 : ℝ)/512)^2 *
        (∫ x in (15/32:ℝ)..(241/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_241 :
    (9251543 : ℝ) / 1000000000000000000 ≤
      ((241 : ℝ)/512)^2 *
        (∫ x in (241/512:ℝ)..(121/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_241).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((241 : ℝ)/512)^2 by positivity)
  have hn :
      (9251543 : ℝ) / 1000000000000000000 ≤
        ((241 : ℝ)/512)^2 *
          (4175610945599/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((241 : ℝ)/512)^2 *
        (4175610945599/100000000000000000000000 : ℝ) ≤
      ((241 : ℝ)/512)^2 *
        (∫ x in (241/512:ℝ)..(121/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_242 :
    (9586118 : ℝ) / 1000000000000000000 ≤
      ((242 : ℝ)/512)^2 *
        (∫ x in (121/256:ℝ)..(243/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_242).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((242 : ℝ)/512)^2 by positivity)
  have hn :
      (9586118 : ℝ) / 1000000000000000000 ≤
        ((242 : ℝ)/512)^2 *
          (2145467689389/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((242 : ℝ)/512)^2 *
        (2145467689389/50000000000000000000000 : ℝ) ≤
      ((242 : ℝ)/512)^2 *
        (∫ x in (121/256:ℝ)..(243/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_243 :
    (9928861 : ℝ) / 1000000000000000000 ≤
      ((243 : ℝ)/512)^2 *
        (∫ x in (243/512:ℝ)..(61/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_243).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((243 : ℝ)/512)^2 by positivity)
  have hn :
      (9928861 : ℝ) / 1000000000000000000 ≤
        ((243 : ℝ)/512)^2 *
          (4407850426877/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((243 : ℝ)/512)^2 *
        (4407850426877/100000000000000000000000 : ℝ) ≤
      ((243 : ℝ)/512)^2 *
        (∫ x in (243/512:ℝ)..(61/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_244 :
    (10279808 : ℝ) / 1000000000000000000 ≤
      ((244 : ℝ)/512)^2 *
        (∫ x in (61/128:ℝ)..(245/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_244).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((244 : ℝ)/512)^2 by positivity)
  have hn :
      (10279808 : ℝ) / 1000000000000000000 ≤
        ((244 : ℝ)/512)^2 *
          (2263160182573/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((244 : ℝ)/512)^2 *
        (2263160182573/50000000000000000000000 : ℝ) ≤
      ((244 : ℝ)/512)^2 *
        (∫ x in (61/128:ℝ)..(245/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_245 :
    (10638984 : ℝ) / 1000000000000000000 ≤
      ((245 : ℝ)/512)^2 *
        (∫ x in (245/512:ℝ)..(123/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_245).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((245 : ℝ)/512)^2 by positivity)
  have hn :
      (10638984 : ℝ) / 1000000000000000000 ≤
        ((245 : ℝ)/512)^2 *
          (464630720473/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((245 : ℝ)/512)^2 *
        (464630720473/10000000000000000000000 : ℝ) ≤
      ((245 : ℝ)/512)^2 *
        (∫ x in (245/512:ℝ)..(123/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_246 :
    (11006409 : ℝ) / 1000000000000000000 ≤
      ((246 : ℝ)/512)^2 *
        (∫ x in (123/256:ℝ)..(247/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_246).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((246 : ℝ)/512)^2 by positivity)
  have hn :
      (11006409 : ℝ) / 1000000000000000000 ≤
        ((246 : ℝ)/512)^2 *
          (953554138013/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((246 : ℝ)/512)^2 *
        (953554138013/20000000000000000000000 : ℝ) ≤
      ((246 : ℝ)/512)^2 *
        (∫ x in (123/256:ℝ)..(247/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_247 :
    (11382094 : ℝ) / 1000000000000000000 ≤
      ((247 : ℝ)/512)^2 *
        (∫ x in (247/512:ℝ)..(31/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_247).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((247 : ℝ)/512)^2 by positivity)
  have hn :
      (11382094 : ℝ) / 1000000000000000000 ≤
        ((247 : ℝ)/512)^2 *
          (4890668299553/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((247 : ℝ)/512)^2 *
        (4890668299553/100000000000000000000000 : ℝ) ≤
      ((247 : ℝ)/512)^2 *
        (∫ x in (247/512:ℝ)..(31/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_248 :
    (11766044 : ℝ) / 1000000000000000000 ≤
      ((248 : ℝ)/512)^2 *
        (∫ x in (31/64:ℝ)..(249/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_248).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((248 : ℝ)/512)^2 by positivity)
  have hn :
      (11766044 : ℝ) / 1000000000000000000 ≤
        ((248 : ℝ)/512)^2 *
          (5014955249589/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((248 : ℝ)/512)^2 *
        (5014955249589/100000000000000000000000 : ℝ) ≤
      ((248 : ℝ)/512)^2 *
        (∫ x in (31/64:ℝ)..(249/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_249 :
    (12158255 : ℝ) / 1000000000000000000 ≤
      ((249 : ℝ)/512)^2 *
        (∫ x in (249/512:ℝ)..(125/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_249).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((249 : ℝ)/512)^2 by positivity)
  have hn :
      (12158255 : ℝ) / 1000000000000000000 ≤
        ((249 : ℝ)/512)^2 *
          (2570292250989/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((249 : ℝ)/512)^2 *
        (2570292250989/50000000000000000000000 : ℝ) ≤
      ((249 : ℝ)/512)^2 *
        (∫ x in (249/512:ℝ)..(125/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_250 :
    (12558714 : ℝ) / 1000000000000000000 ≤
      ((250 : ℝ)/512)^2 *
        (∫ x in (125/256:ℝ)..(251/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_250).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((250 : ℝ)/512)^2 by positivity)
  have hn :
      (12558714 : ℝ) / 1000000000000000000 ≤
        ((250 : ℝ)/512)^2 *
          (2633753387409/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((250 : ℝ)/512)^2 *
        (2633753387409/50000000000000000000000 : ℝ) ≤
      ((250 : ℝ)/512)^2 *
        (∫ x in (125/256:ℝ)..(251/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_251 :
    (12967401 : ℝ) / 1000000000000000000 ≤
      ((251 : ℝ)/512)^2 *
        (∫ x in (251/512:ℝ)..(63/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_251).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((251 : ℝ)/512)^2 by positivity)
  have hn :
      (12967401 : ℝ) / 1000000000000000000 ≤
        ((251 : ℝ)/512)^2 *
          (2697835278431/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((251 : ℝ)/512)^2 *
        (2697835278431/50000000000000000000000 : ℝ) ≤
      ((251 : ℝ)/512)^2 *
        (∫ x in (251/512:ℝ)..(63/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_252 :
    (13384285 : ℝ) / 1000000000000000000 ≤
      ((252 : ℝ)/512)^2 *
        (∫ x in (63/128:ℝ)..(253/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_252).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((252 : ℝ)/512)^2 by positivity)
  have hn :
      (13384285 : ℝ) / 1000000000000000000 ≤
        ((252 : ℝ)/512)^2 *
          (2762511062713/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((252 : ℝ)/512)^2 *
        (2762511062713/50000000000000000000000 : ℝ) ≤
      ((252 : ℝ)/512)^2 *
        (∫ x in (63/128:ℝ)..(253/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_253 :
    (13809328 : ℝ) / 1000000000000000000 ≤
      ((253 : ℝ)/512)^2 *
        (∫ x in (253/512:ℝ)..(127/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_253).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((253 : ℝ)/512)^2 by positivity)
  have hn :
      (13809328 : ℝ) / 1000000000000000000 ≤
        ((253 : ℝ)/512)^2 *
          (2827752783929/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((253 : ℝ)/512)^2 *
        (2827752783929/50000000000000000000000 : ℝ) ≤
      ((253 : ℝ)/512)^2 *
        (∫ x in (253/512:ℝ)..(127/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_254 :
    (14242482 : ℝ) / 1000000000000000000 ≤
      ((254 : ℝ)/512)^2 *
        (∫ x in (127/256:ℝ)..(255/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_254).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((254 : ℝ)/512)^2 by positivity)
  have hn :
      (14242482 : ℝ) / 1000000000000000000 ≤
        ((254 : ℝ)/512)^2 *
          (5787062806593/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((254 : ℝ)/512)^2 *
        (5787062806593/100000000000000000000000 : ℝ) ≤
      ((254 : ℝ)/512)^2 *
        (∫ x in (127/256:ℝ)..(255/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_255 :
    (14683692 : ℝ) / 1000000000000000000 ≤
      ((255 : ℝ)/512)^2 *
        (∫ x in (255/512:ℝ)..(1/2:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_255).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((255 : ℝ)/512)^2 by positivity)
  have hn :
      (14683692 : ℝ) / 1000000000000000000 ≤
        ((255 : ℝ)/512)^2 *
          (2959816813913/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((255 : ℝ)/512)^2 *
        (2959816813913/50000000000000000000000 : ℝ) ≤
      ((255 : ℝ)/512)^2 *
        (∫ x in (255/512:ℝ)..(1/2:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
