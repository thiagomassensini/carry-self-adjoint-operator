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
        (∫ x in (((224 : ℝ)/512))..((((224+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_224).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((224 : ℝ)/512)^2 by positivity)
  have hn :
      (4751443 : ℝ) / 1000000000000000000 ≤
        ((224 : ℝ)/512)^2 *
          (2482386996789/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (7/16 : ℝ) = ((224 : ℝ)/512) := by
    norm_num
  have hright :
      (225/512 : ℝ) = (((( 224+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((224 : ℝ)/512)^2 *
        (2482386996789/100000000000000000000000 : ℝ) ≤
      ((224 : ℝ)/512)^2 *
        (∫ x in (((224 : ℝ)/512))..((((224+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_225 :
    (4957994 : ℝ) / 1000000000000000000 ≤
      ((225 : ℝ)/512)^2 *
        (∫ x in (((225 : ℝ)/512))..((((225+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_225).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((225 : ℝ)/512)^2 by positivity)
  have hn :
      (4957994 : ℝ) / 1000000000000000000 ≤
        ((225 : ℝ)/512)^2 *
          (256732525397/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (225/512 : ℝ) = ((225 : ℝ)/512) := by
    norm_num
  have hright :
      (113/256 : ℝ) = (((( 225+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((225 : ℝ)/512)^2 *
        (256732525397/10000000000000000000000 : ℝ) ≤
      ((225 : ℝ)/512)^2 *
        (∫ x in (((225 : ℝ)/512))..((((225+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_226 :
    (5171296 : ℝ) / 1000000000000000000 ≤
      ((226 : ℝ)/512)^2 *
        (∫ x in (((226 : ℝ)/512))..((((226+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_226).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((226 : ℝ)/512)^2 by positivity)
  have hn :
      (5171296 : ℝ) / 1000000000000000000 ≤
        ((226 : ℝ)/512)^2 *
          (132706594417/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (113/256 : ℝ) = ((226 : ℝ)/512) := by
    norm_num
  have hright :
      (227/512 : ℝ) = (((( 226+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((226 : ℝ)/512)^2 *
        (132706594417/5000000000000000000000 : ℝ) ≤
      ((226 : ℝ)/512)^2 *
        (∫ x in (((226 : ℝ)/512))..((((226+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_227 :
    (5391467 : ℝ) / 1000000000000000000 ≤
      ((227 : ℝ)/512)^2 *
        (∫ x in (((227 : ℝ)/512))..((((227+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_227).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((227 : ℝ)/512)^2 by positivity)
  have hn :
      (5391467 : ℝ) / 1000000000000000000 ≤
        ((227 : ℝ)/512)^2 *
          (1371403236043/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (227/512 : ℝ) = ((227 : ℝ)/512) := by
    norm_num
  have hright :
      (57/128 : ℝ) = (((( 227+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((227 : ℝ)/512)^2 *
        (1371403236043/50000000000000000000000 : ℝ) ≤
      ((227 : ℝ)/512)^2 *
        (∫ x in (((227 : ℝ)/512))..((((227+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_228 :
    (5618617 : ℝ) / 1000000000000000000 ≤
      ((228 : ℝ)/512)^2 *
        (∫ x in (((228 : ℝ)/512))..((((228+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_228).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((228 : ℝ)/512)^2 by positivity)
  have hn :
      (5618617 : ℝ) / 1000000000000000000 ≤
        ((228 : ℝ)/512)^2 *
          (2833346779519/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (57/128 : ℝ) = ((228 : ℝ)/512) := by
    norm_num
  have hright :
      (229/512 : ℝ) = (((( 228+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((228 : ℝ)/512)^2 *
        (2833346779519/100000000000000000000000 : ℝ) ≤
      ((228 : ℝ)/512)^2 *
        (∫ x in (((228 : ℝ)/512))..((((228+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_229 :
    (5852859 : ℝ) / 1000000000000000000 ≤
      ((229 : ℝ)/512)^2 *
        (∫ x in (((229 : ℝ)/512))..((((229+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_229).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((229 : ℝ)/512)^2 by positivity)
  have hn :
      (5852859 : ℝ) / 1000000000000000000 ≤
        ((229 : ℝ)/512)^2 *
          (1462874371027/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (229/512 : ℝ) = ((229 : ℝ)/512) := by
    norm_num
  have hright :
      (115/256 : ℝ) = (((( 229+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((229 : ℝ)/512)^2 *
        (1462874371027/50000000000000000000000 : ℝ) ≤
      ((229 : ℝ)/512)^2 *
        (∫ x in (((229 : ℝ)/512))..((((229+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_230 :
    (6094296 : ℝ) / 1000000000000000000 ≤
      ((230 : ℝ)/512)^2 *
        (∫ x in (((230 : ℝ)/512))..((((230+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_230).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((230 : ℝ)/512)^2 by positivity)
  have hn :
      (6094296 : ℝ) / 1000000000000000000 ≤
        ((230 : ℝ)/512)^2 *
          (151000320243/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (115/256 : ℝ) = ((230 : ℝ)/512) := by
    norm_num
  have hright :
      (231/512 : ℝ) = (((( 230+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((230 : ℝ)/512)^2 *
        (151000320243/5000000000000000000000 : ℝ) ≤
      ((230 : ℝ)/512)^2 *
        (∫ x in (((230 : ℝ)/512))..((((230+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_231 :
    (6343034 : ℝ) / 1000000000000000000 ≤
      ((231 : ℝ)/512)^2 *
        (∫ x in (((231 : ℝ)/512))..((((231+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_231).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((231 : ℝ)/512)^2 by positivity)
  have hn :
      (6343034 : ℝ) / 1000000000000000000 ≤
        ((231 : ℝ)/512)^2 *
          (3116111885269/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (231/512 : ℝ) = ((231 : ℝ)/512) := by
    norm_num
  have hright :
      (29/64 : ℝ) = (((( 231+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((231 : ℝ)/512)^2 *
        (3116111885269/100000000000000000000000 : ℝ) ≤
      ((231 : ℝ)/512)^2 *
        (∫ x in (((231 : ℝ)/512))..((((231+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_232 :
    (6599171 : ℝ) / 1000000000000000000 ≤
      ((232 : ℝ)/512)^2 *
        (∫ x in (((232 : ℝ)/512))..((((232+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_232).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((232 : ℝ)/512)^2 by positivity)
  have hn :
      (6599171 : ℝ) / 1000000000000000000 ≤
        ((232 : ℝ)/512)^2 *
          (3214055333071/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (29/64 : ℝ) = ((232 : ℝ)/512) := by
    norm_num
  have hright :
      (233/512 : ℝ) = (((( 232+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((232 : ℝ)/512)^2 *
        (3214055333071/100000000000000000000000 : ℝ) ≤
      ((232 : ℝ)/512)^2 *
        (∫ x in (((232 : ℝ)/512))..((((232+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_233 :
    (6862802 : ℝ) / 1000000000000000000 ≤
      ((233 : ℝ)/512)^2 *
        (∫ x in (((233 : ℝ)/512))..((((233+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_233).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((233 : ℝ)/512)^2 by positivity)
  have hn :
      (6862802 : ℝ) / 1000000000000000000 ≤
        ((233 : ℝ)/512)^2 *
          (3313824892809/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (233/512 : ℝ) = ((233 : ℝ)/512) := by
    norm_num
  have hright :
      (117/256 : ℝ) = (((( 233+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((233 : ℝ)/512)^2 *
        (3313824892809/100000000000000000000000 : ℝ) ≤
      ((233 : ℝ)/512)^2 *
        (∫ x in (((233 : ℝ)/512))..((((233+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_234 :
    (7134018 : ℝ) / 1000000000000000000 ≤
      ((234 : ℝ)/512)^2 *
        (∫ x in (((234 : ℝ)/512))..((((234+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_234).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((234 : ℝ)/512)^2 by positivity)
  have hn :
      (7134018 : ℝ) / 1000000000000000000 ≤
        ((234 : ℝ)/512)^2 *
          (3415406668169/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (117/256 : ℝ) = ((234 : ℝ)/512) := by
    norm_num
  have hright :
      (235/512 : ℝ) = (((( 234+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((234 : ℝ)/512)^2 *
        (3415406668169/100000000000000000000000 : ℝ) ≤
      ((234 : ℝ)/512)^2 *
        (∫ x in (((234 : ℝ)/512))..((((234+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_235 :
    (7412906 : ℝ) / 1000000000000000000 ≤
      ((235 : ℝ)/512)^2 *
        (∫ x in (((235 : ℝ)/512))..((((235+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_235).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((235 : ℝ)/512)^2 by positivity)
  have hn :
      (7412906 : ℝ) / 1000000000000000000 ≤
        ((235 : ℝ)/512)^2 *
          (3518784688597/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (235/512 : ℝ) = ((235 : ℝ)/512) := by
    norm_num
  have hright :
      (59/128 : ℝ) = (((( 235+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((235 : ℝ)/512)^2 *
        (3518784688597/100000000000000000000000 : ℝ) ≤
      ((235 : ℝ)/512)^2 *
        (∫ x in (((235 : ℝ)/512))..((((235+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_236 :
    (7699547 : ℝ) / 1000000000000000000 ≤
      ((236 : ℝ)/512)^2 *
        (∫ x in (((236 : ℝ)/512))..((((236+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_236).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((236 : ℝ)/512)^2 by positivity)
  have hn :
      (7699547 : ℝ) / 1000000000000000000 ≤
        ((236 : ℝ)/512)^2 *
          (1811970439117/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (59/128 : ℝ) = ((236 : ℝ)/512) := by
    norm_num
  have hright :
      (237/512 : ℝ) = (((( 236+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((236 : ℝ)/512)^2 *
        (1811970439117/50000000000000000000000 : ℝ) ≤
      ((236 : ℝ)/512)^2 *
        (∫ x in (((236 : ℝ)/512))..((((236+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_237 :
    (7994018 : ℝ) / 1000000000000000000 ≤
      ((237 : ℝ)/512)^2 *
        (∫ x in (((237 : ℝ)/512))..((((237+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_237).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((237 : ℝ)/512)^2 by positivity)
  have hn :
      (7994018 : ℝ) / 1000000000000000000 ≤
        ((237 : ℝ)/512)^2 *
          (1865427513637/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (237/512 : ℝ) = ((237 : ℝ)/512) := by
    norm_num
  have hright :
      (119/256 : ℝ) = (((( 237+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((237 : ℝ)/512)^2 *
        (1865427513637/50000000000000000000000 : ℝ) ≤
      ((237 : ℝ)/512)^2 *
        (∫ x in (((237 : ℝ)/512))..((((237+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_238 :
    (8296390 : ℝ) / 1000000000000000000 ≤
      ((238 : ℝ)/512)^2 *
        (∫ x in (((238 : ℝ)/512))..((((238+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_238).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((238 : ℝ)/512)^2 by positivity)
  have hn :
      (8296390 : ℝ) / 1000000000000000000 ≤
        ((238 : ℝ)/512)^2 *
          (191975238293/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (119/256 : ℝ) = ((238 : ℝ)/512) := by
    norm_num
  have hright :
      (239/512 : ℝ) = (((( 238+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((238 : ℝ)/512)^2 *
        (191975238293/5000000000000000000000 : ℝ) ≤
      ((238 : ℝ)/512)^2 *
        (∫ x in (((238 : ℝ)/512))..((((238+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_239 :
    (8606730 : ℝ) / 1000000000000000000 ≤
      ((239 : ℝ)/512)^2 *
        (∫ x in (((239 : ℝ)/512))..((((239+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_239).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((239 : ℝ)/512)^2 by positivity)
  have hn :
      (8606730 : ℝ) / 1000000000000000000 ≤
        ((239 : ℝ)/512)^2 *
          (3949865540601/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (239/512 : ℝ) = ((239 : ℝ)/512) := by
    norm_num
  have hright :
      (15/32 : ℝ) = (((( 239+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((239 : ℝ)/512)^2 *
        (3949865540601/100000000000000000000000 : ℝ) ≤
      ((239 : ℝ)/512)^2 *
        (∫ x in (((239 : ℝ)/512))..((((239+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_240 :
    (8925096 : ℝ) / 1000000000000000000 ≤
      ((240 : ℝ)/512)^2 *
        (∫ x in (((240 : ℝ)/512))..((((240+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_240).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((240 : ℝ)/512)^2 by positivity)
  have hn :
      (8925096 : ℝ) / 1000000000000000000 ≤
        ((240 : ℝ)/512)^2 *
          (4061910593817/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (15/32 : ℝ) = ((240 : ℝ)/512) := by
    norm_num
  have hright :
      (241/512 : ℝ) = (((( 240+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((240 : ℝ)/512)^2 *
        (4061910593817/100000000000000000000000 : ℝ) ≤
      ((240 : ℝ)/512)^2 *
        (∫ x in (((240 : ℝ)/512))..((((240+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_241 :
    (9251543 : ℝ) / 1000000000000000000 ≤
      ((241 : ℝ)/512)^2 *
        (∫ x in (((241 : ℝ)/512))..((((241+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_241).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((241 : ℝ)/512)^2 by positivity)
  have hn :
      (9251543 : ℝ) / 1000000000000000000 ≤
        ((241 : ℝ)/512)^2 *
          (4175610945599/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (241/512 : ℝ) = ((241 : ℝ)/512) := by
    norm_num
  have hright :
      (121/256 : ℝ) = (((( 241+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((241 : ℝ)/512)^2 *
        (4175610945599/100000000000000000000000 : ℝ) ≤
      ((241 : ℝ)/512)^2 *
        (∫ x in (((241 : ℝ)/512))..((((241+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_242 :
    (9586118 : ℝ) / 1000000000000000000 ≤
      ((242 : ℝ)/512)^2 *
        (∫ x in (((242 : ℝ)/512))..((((242+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_242).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((242 : ℝ)/512)^2 by positivity)
  have hn :
      (9586118 : ℝ) / 1000000000000000000 ≤
        ((242 : ℝ)/512)^2 *
          (2145467689389/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (121/256 : ℝ) = ((242 : ℝ)/512) := by
    norm_num
  have hright :
      (243/512 : ℝ) = (((( 242+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((242 : ℝ)/512)^2 *
        (2145467689389/50000000000000000000000 : ℝ) ≤
      ((242 : ℝ)/512)^2 *
        (∫ x in (((242 : ℝ)/512))..((((242+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_243 :
    (9928861 : ℝ) / 1000000000000000000 ≤
      ((243 : ℝ)/512)^2 *
        (∫ x in (((243 : ℝ)/512))..((((243+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_243).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((243 : ℝ)/512)^2 by positivity)
  have hn :
      (9928861 : ℝ) / 1000000000000000000 ≤
        ((243 : ℝ)/512)^2 *
          (4407850426877/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (243/512 : ℝ) = ((243 : ℝ)/512) := by
    norm_num
  have hright :
      (61/128 : ℝ) = (((( 243+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((243 : ℝ)/512)^2 *
        (4407850426877/100000000000000000000000 : ℝ) ≤
      ((243 : ℝ)/512)^2 *
        (∫ x in (((243 : ℝ)/512))..((((243+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_244 :
    (10279808 : ℝ) / 1000000000000000000 ≤
      ((244 : ℝ)/512)^2 *
        (∫ x in (((244 : ℝ)/512))..((((244+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_244).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((244 : ℝ)/512)^2 by positivity)
  have hn :
      (10279808 : ℝ) / 1000000000000000000 ≤
        ((244 : ℝ)/512)^2 *
          (2263160182573/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (61/128 : ℝ) = ((244 : ℝ)/512) := by
    norm_num
  have hright :
      (245/512 : ℝ) = (((( 244+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((244 : ℝ)/512)^2 *
        (2263160182573/50000000000000000000000 : ℝ) ≤
      ((244 : ℝ)/512)^2 *
        (∫ x in (((244 : ℝ)/512))..((((244+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_245 :
    (10638984 : ℝ) / 1000000000000000000 ≤
      ((245 : ℝ)/512)^2 *
        (∫ x in (((245 : ℝ)/512))..((((245+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_245).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((245 : ℝ)/512)^2 by positivity)
  have hn :
      (10638984 : ℝ) / 1000000000000000000 ≤
        ((245 : ℝ)/512)^2 *
          (464630720473/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (245/512 : ℝ) = ((245 : ℝ)/512) := by
    norm_num
  have hright :
      (123/256 : ℝ) = (((( 245+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((245 : ℝ)/512)^2 *
        (464630720473/10000000000000000000000 : ℝ) ≤
      ((245 : ℝ)/512)^2 *
        (∫ x in (((245 : ℝ)/512))..((((245+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_246 :
    (11006409 : ℝ) / 1000000000000000000 ≤
      ((246 : ℝ)/512)^2 *
        (∫ x in (((246 : ℝ)/512))..((((246+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_246).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((246 : ℝ)/512)^2 by positivity)
  have hn :
      (11006409 : ℝ) / 1000000000000000000 ≤
        ((246 : ℝ)/512)^2 *
          (953554138013/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (123/256 : ℝ) = ((246 : ℝ)/512) := by
    norm_num
  have hright :
      (247/512 : ℝ) = (((( 246+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((246 : ℝ)/512)^2 *
        (953554138013/20000000000000000000000 : ℝ) ≤
      ((246 : ℝ)/512)^2 *
        (∫ x in (((246 : ℝ)/512))..((((246+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_247 :
    (11382094 : ℝ) / 1000000000000000000 ≤
      ((247 : ℝ)/512)^2 *
        (∫ x in (((247 : ℝ)/512))..((((247+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_247).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((247 : ℝ)/512)^2 by positivity)
  have hn :
      (11382094 : ℝ) / 1000000000000000000 ≤
        ((247 : ℝ)/512)^2 *
          (4890668299553/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (247/512 : ℝ) = ((247 : ℝ)/512) := by
    norm_num
  have hright :
      (31/64 : ℝ) = (((( 247+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((247 : ℝ)/512)^2 *
        (4890668299553/100000000000000000000000 : ℝ) ≤
      ((247 : ℝ)/512)^2 *
        (∫ x in (((247 : ℝ)/512))..((((247+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_248 :
    (11766044 : ℝ) / 1000000000000000000 ≤
      ((248 : ℝ)/512)^2 *
        (∫ x in (((248 : ℝ)/512))..((((248+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_248).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((248 : ℝ)/512)^2 by positivity)
  have hn :
      (11766044 : ℝ) / 1000000000000000000 ≤
        ((248 : ℝ)/512)^2 *
          (5014955249589/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (31/64 : ℝ) = ((248 : ℝ)/512) := by
    norm_num
  have hright :
      (249/512 : ℝ) = (((( 248+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((248 : ℝ)/512)^2 *
        (5014955249589/100000000000000000000000 : ℝ) ≤
      ((248 : ℝ)/512)^2 *
        (∫ x in (((248 : ℝ)/512))..((((248+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_249 :
    (12158255 : ℝ) / 1000000000000000000 ≤
      ((249 : ℝ)/512)^2 *
        (∫ x in (((249 : ℝ)/512))..((((249+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_249).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((249 : ℝ)/512)^2 by positivity)
  have hn :
      (12158255 : ℝ) / 1000000000000000000 ≤
        ((249 : ℝ)/512)^2 *
          (2570292250989/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (249/512 : ℝ) = ((249 : ℝ)/512) := by
    norm_num
  have hright :
      (125/256 : ℝ) = (((( 249+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((249 : ℝ)/512)^2 *
        (2570292250989/50000000000000000000000 : ℝ) ≤
      ((249 : ℝ)/512)^2 *
        (∫ x in (((249 : ℝ)/512))..((((249+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_250 :
    (12558714 : ℝ) / 1000000000000000000 ≤
      ((250 : ℝ)/512)^2 *
        (∫ x in (((250 : ℝ)/512))..((((250+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_250).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((250 : ℝ)/512)^2 by positivity)
  have hn :
      (12558714 : ℝ) / 1000000000000000000 ≤
        ((250 : ℝ)/512)^2 *
          (2633753387409/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (125/256 : ℝ) = ((250 : ℝ)/512) := by
    norm_num
  have hright :
      (251/512 : ℝ) = (((( 250+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((250 : ℝ)/512)^2 *
        (2633753387409/50000000000000000000000 : ℝ) ≤
      ((250 : ℝ)/512)^2 *
        (∫ x in (((250 : ℝ)/512))..((((250+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_251 :
    (12967401 : ℝ) / 1000000000000000000 ≤
      ((251 : ℝ)/512)^2 *
        (∫ x in (((251 : ℝ)/512))..((((251+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_251).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((251 : ℝ)/512)^2 by positivity)
  have hn :
      (12967401 : ℝ) / 1000000000000000000 ≤
        ((251 : ℝ)/512)^2 *
          (2697835278431/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (251/512 : ℝ) = ((251 : ℝ)/512) := by
    norm_num
  have hright :
      (63/128 : ℝ) = (((( 251+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((251 : ℝ)/512)^2 *
        (2697835278431/50000000000000000000000 : ℝ) ≤
      ((251 : ℝ)/512)^2 *
        (∫ x in (((251 : ℝ)/512))..((((251+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_252 :
    (13384285 : ℝ) / 1000000000000000000 ≤
      ((252 : ℝ)/512)^2 *
        (∫ x in (((252 : ℝ)/512))..((((252+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_252).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((252 : ℝ)/512)^2 by positivity)
  have hn :
      (13384285 : ℝ) / 1000000000000000000 ≤
        ((252 : ℝ)/512)^2 *
          (2762511062713/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (63/128 : ℝ) = ((252 : ℝ)/512) := by
    norm_num
  have hright :
      (253/512 : ℝ) = (((( 252+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((252 : ℝ)/512)^2 *
        (2762511062713/50000000000000000000000 : ℝ) ≤
      ((252 : ℝ)/512)^2 *
        (∫ x in (((252 : ℝ)/512))..((((252+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_253 :
    (13809328 : ℝ) / 1000000000000000000 ≤
      ((253 : ℝ)/512)^2 *
        (∫ x in (((253 : ℝ)/512))..((((253+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_253).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((253 : ℝ)/512)^2 by positivity)
  have hn :
      (13809328 : ℝ) / 1000000000000000000 ≤
        ((253 : ℝ)/512)^2 *
          (2827752783929/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (253/512 : ℝ) = ((253 : ℝ)/512) := by
    norm_num
  have hright :
      (127/256 : ℝ) = (((( 253+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((253 : ℝ)/512)^2 *
        (2827752783929/50000000000000000000000 : ℝ) ≤
      ((253 : ℝ)/512)^2 *
        (∫ x in (((253 : ℝ)/512))..((((253+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_254 :
    (14242482 : ℝ) / 1000000000000000000 ≤
      ((254 : ℝ)/512)^2 *
        (∫ x in (((254 : ℝ)/512))..((((254+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_254).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((254 : ℝ)/512)^2 by positivity)
  have hn :
      (14242482 : ℝ) / 1000000000000000000 ≤
        ((254 : ℝ)/512)^2 *
          (5787062806593/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (127/256 : ℝ) = ((254 : ℝ)/512) := by
    norm_num
  have hright :
      (255/512 : ℝ) = (((( 254+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((254 : ℝ)/512)^2 *
        (5787062806593/100000000000000000000000 : ℝ) ≤
      ((254 : ℝ)/512)^2 *
        (∫ x in (((254 : ℝ)/512))..((((254+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_255 :
    (14683692 : ℝ) / 1000000000000000000 ≤
      ((255 : ℝ)/512)^2 *
        (∫ x in (((255 : ℝ)/512))..((((255+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_255).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((255 : ℝ)/512)^2 by positivity)
  have hn :
      (14683692 : ℝ) / 1000000000000000000 ≤
        ((255 : ℝ)/512)^2 *
          (2959816813913/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (255/512 : ℝ) = ((255 : ℝ)/512) := by
    norm_num
  have hright :
      (1/2 : ℝ) = (((( 255+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((255 : ℝ)/512)^2 *
        (2959816813913/50000000000000000000000 : ℝ) ≤
      ((255 : ℝ)/512)^2 *
        (∫ x in (((255 : ℝ)/512))..((((255+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
