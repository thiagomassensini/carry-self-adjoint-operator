import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_12
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_384 :
    (43356996 : ℝ) / 1000000000000000000 ≤
      ((384 : ℝ)/512)^2 *
        (∫ x in (((384 : ℝ)/512))..((((384+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_384).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((384 : ℝ)/512)^2 by positivity)
  have hn :
      (43356996 : ℝ) / 1000000000000000000 ≤
        ((384 : ℝ)/512)^2 *
          (7707910562537/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (3/4 : ℝ) = ((384 : ℝ)/512) := by
    norm_num
  have hright :
      (385/512 : ℝ) = (((( 384+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((384 : ℝ)/512)^2 *
        (7707910562537/100000000000000000000000 : ℝ) ≤
      ((384 : ℝ)/512)^2 *
        (∫ x in (((384 : ℝ)/512))..((((384+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_385 :
    (42811057 : ℝ) / 1000000000000000000 ≤
      ((385 : ℝ)/512)^2 *
        (∫ x in (((385 : ℝ)/512))..((((385+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_385).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((385 : ℝ)/512)^2 by positivity)
  have hn :
      (42811057 : ℝ) / 1000000000000000000 ≤
        ((385 : ℝ)/512)^2 *
          (1892842281029/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (385/512 : ℝ) = ((385 : ℝ)/512) := by
    norm_num
  have hright :
      (193/256 : ℝ) = (((( 385+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((385 : ℝ)/512)^2 *
        (1892842281029/25000000000000000000000 : ℝ) ≤
      ((385 : ℝ)/512)^2 *
        (∫ x in (((385 : ℝ)/512))..((((385+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_386 :
    (42258307 : ℝ) / 1000000000000000000 ≤
      ((386 : ℝ)/512)^2 *
        (∫ x in (((386 : ℝ)/512))..((((386+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_386).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((386 : ℝ)/512)^2 by positivity)
  have hn :
      (42258307 : ℝ) / 1000000000000000000 ≤
        ((386 : ℝ)/512)^2 *
          (7434939027873/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (193/256 : ℝ) = ((386 : ℝ)/512) := by
    norm_num
  have hright :
      (387/512 : ℝ) = (((( 386+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((386 : ℝ)/512)^2 *
        (7434939027873/100000000000000000000000 : ℝ) ≤
      ((386 : ℝ)/512)^2 *
        (∫ x in (((386 : ℝ)/512))..((((386+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_387 :
    (41699177 : ℝ) / 1000000000000000000 ≤
      ((387 : ℝ)/512)^2 *
        (∫ x in (((387 : ℝ)/512))..((((387+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_387).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((387 : ℝ)/512)^2 by positivity)
  have hn :
      (41699177 : ℝ) / 1000000000000000000 ≤
        ((387 : ℝ)/512)^2 *
          (7298699540501/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (387/512 : ℝ) = ((387 : ℝ)/512) := by
    norm_num
  have hright :
      (97/128 : ℝ) = (((( 387+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((387 : ℝ)/512)^2 *
        (7298699540501/100000000000000000000000 : ℝ) ≤
      ((387 : ℝ)/512)^2 *
        (∫ x in (((387 : ℝ)/512))..((((387+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_388 :
    (41134101 : ℝ) / 1000000000000000000 ≤
      ((388 : ℝ)/512)^2 *
        (∫ x in (((388 : ℝ)/512))..((((388+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_388).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((388 : ℝ)/512)^2 by positivity)
  have hn :
      (41134101 : ℝ) / 1000000000000000000 ≤
        ((388 : ℝ)/512)^2 *
          (895341050891/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (97/128 : ℝ) = ((388 : ℝ)/512) := by
    norm_num
  have hright :
      (389/512 : ℝ) = (((( 388+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((388 : ℝ)/512)^2 *
        (895341050891/12500000000000000000000 : ℝ) ≤
      ((388 : ℝ)/512)^2 *
        (∫ x in (((388 : ℝ)/512))..((((388+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_389 :
    (40563509 : ℝ) / 1000000000000000000 ≤
      ((389 : ℝ)/512)^2 *
        (∫ x in (((389 : ℝ)/512))..((((389+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_389).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((389 : ℝ)/512)^2 by positivity)
  have hn :
      (40563509 : ℝ) / 1000000000000000000 ≤
        ((389 : ℝ)/512)^2 *
          (7027101786941/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (389/512 : ℝ) = ((389 : ℝ)/512) := by
    norm_num
  have hright :
      (195/256 : ℝ) = (((( 389+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((389 : ℝ)/512)^2 *
        (7027101786941/100000000000000000000000 : ℝ) ≤
      ((389 : ℝ)/512)^2 *
        (∫ x in (((389 : ℝ)/512))..((((389+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_390 :
    (39987835 : ℝ) / 1000000000000000000 ≤
      ((390 : ℝ)/512)^2 *
        (∫ x in (((390 : ℝ)/512))..((((390+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_390).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((390 : ℝ)/512)^2 by positivity)
  have hn :
      (39987835 : ℝ) / 1000000000000000000 ≤
        ((390 : ℝ)/512)^2 *
          (6891894192123/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (195/256 : ℝ) = ((390 : ℝ)/512) := by
    norm_num
  have hright :
      (391/512 : ℝ) = (((( 390+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((390 : ℝ)/512)^2 *
        (6891894192123/100000000000000000000000 : ℝ) ≤
      ((390 : ℝ)/512)^2 *
        (∫ x in (((390 : ℝ)/512))..((((390+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_391 :
    (39407508 : ℝ) / 1000000000000000000 ≤
      ((391 : ℝ)/512)^2 *
        (∫ x in (((391 : ℝ)/512))..((((391+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_391).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((391 : ℝ)/512)^2 by positivity)
  have hn :
      (39407508 : ℝ) / 1000000000000000000 ≤
        ((391 : ℝ)/512)^2 *
          (6757178430143/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (391/512 : ℝ) = ((391 : ℝ)/512) := by
    norm_num
  have hright :
      (49/64 : ℝ) = (((( 391+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((391 : ℝ)/512)^2 *
        (6757178430143/100000000000000000000000 : ℝ) ≤
      ((391 : ℝ)/512)^2 *
        (∫ x in (((391 : ℝ)/512))..((((391+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_392 :
    (38822959 : ℝ) / 1000000000000000000 ≤
      ((392 : ℝ)/512)^2 *
        (∫ x in (((392 : ℝ)/512))..((((392+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_392).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((392 : ℝ)/512)^2 by positivity)
  have hn :
      (38822959 : ℝ) / 1000000000000000000 ≤
        ((392 : ℝ)/512)^2 *
          (6623025549457/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (49/64 : ℝ) = ((392 : ℝ)/512) := by
    norm_num
  have hright :
      (393/512 : ℝ) = (((( 392+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((392 : ℝ)/512)^2 *
        (6623025549457/100000000000000000000000 : ℝ) ≤
      ((392 : ℝ)/512)^2 *
        (∫ x in (((392 : ℝ)/512))..((((392+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_393 :
    (38234616 : ℝ) / 1000000000000000000 ≤
      ((393 : ℝ)/512)^2 *
        (∫ x in (((393 : ℝ)/512))..((((393+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_393).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((393 : ℝ)/512)^2 by positivity)
  have hn :
      (38234616 : ℝ) / 1000000000000000000 ≤
        ((393 : ℝ)/512)^2 *
          (6489504788647/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (393/512 : ℝ) = ((393 : ℝ)/512) := by
    norm_num
  have hright :
      (197/256 : ℝ) = (((( 393+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((393 : ℝ)/512)^2 *
        (6489504788647/100000000000000000000000 : ℝ) ≤
      ((393 : ℝ)/512)^2 *
        (∫ x in (((393 : ℝ)/512))..((((393+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_394 :
    (37642903 : ℝ) / 1000000000000000000 ≤
      ((394 : ℝ)/512)^2 *
        (∫ x in (((394 : ℝ)/512))..((((394+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_394).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((394 : ℝ)/512)^2 by positivity)
  have hn :
      (37642903 : ℝ) / 1000000000000000000 ≤
        ((394 : ℝ)/512)^2 *
          (3178341764513/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (197/256 : ℝ) = ((394 : ℝ)/512) := by
    norm_num
  have hright :
      (395/512 : ℝ) = (((( 394+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((394 : ℝ)/512)^2 *
        (3178341764513/50000000000000000000000 : ℝ) ≤
      ((394 : ℝ)/512)^2 *
        (∫ x in (((394 : ℝ)/512))..((((394+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_395 :
    (37048243 : ℝ) / 1000000000000000000 ≤
      ((395 : ℝ)/512)^2 *
        (∫ x in (((395 : ℝ)/512))..((((395+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_395).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((395 : ℝ)/512)^2 by positivity)
  have hn :
      (37048243 : ℝ) / 1000000000000000000 ≤
        ((395 : ℝ)/512)^2 *
          (6224627250733/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (395/512 : ℝ) = ((395 : ℝ)/512) := by
    norm_num
  have hright :
      (99/128 : ℝ) = (((( 395+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((395 : ℝ)/512)^2 *
        (6224627250733/100000000000000000000000 : ℝ) ≤
      ((395 : ℝ)/512)^2 *
        (∫ x in (((395 : ℝ)/512))..((((395+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_396 :
    (36451054 : ℝ) / 1000000000000000000 ≤
      ((396 : ℝ)/512)^2 *
        (∫ x in (((396 : ℝ)/512))..((((396+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_396).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((396 : ℝ)/512)^2 by positivity)
  have hn :
      (36451054 : ℝ) / 1000000000000000000 ≤
        ((396 : ℝ)/512)^2 *
          (3046699746167/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (99/128 : ℝ) = ((396 : ℝ)/512) := by
    norm_num
  have hright :
      (397/512 : ℝ) = (((( 396+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((396 : ℝ)/512)^2 *
        (3046699746167/50000000000000000000000 : ℝ) ≤
      ((396 : ℝ)/512)^2 *
        (∫ x in (((396 : ℝ)/512))..((((396+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_397 :
    (35851753 : ℝ) / 1000000000000000000 ≤
      ((397 : ℝ)/512)^2 *
        (∫ x in (((397 : ℝ)/512))..((((397+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_397).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((397 : ℝ)/512)^2 by positivity)
  have hn :
      (35851753 : ℝ) / 1000000000000000000 ≤
        ((397 : ℝ)/512)^2 *
          (5963061813929/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (397/512 : ℝ) = ((397 : ℝ)/512) := by
    norm_num
  have hright :
      (199/256 : ℝ) = (((( 397+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((397 : ℝ)/512)^2 *
        (5963061813929/100000000000000000000000 : ℝ) ≤
      ((397 : ℝ)/512)^2 *
        (∫ x in (((397 : ℝ)/512))..((((397+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_398 :
    (35250749 : ℝ) / 1000000000000000000 ≤
      ((398 : ℝ)/512)^2 *
        (∫ x in (((398 : ℝ)/512))..((((398+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_398).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((398 : ℝ)/512)^2 by positivity)
  have hn :
      (35250749 : ℝ) / 1000000000000000000 ≤
        ((398 : ℝ)/512)^2 *
          (91151152559/1562500000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (199/256 : ℝ) = ((398 : ℝ)/512) := by
    norm_num
  have hright :
      (399/512 : ℝ) = (((( 398+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((398 : ℝ)/512)^2 *
        (91151152559/1562500000000000000000 : ℝ) ≤
      ((398 : ℝ)/512)^2 *
        (∫ x in (((398 : ℝ)/512))..((((398+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_399 :
    (34648449 : ℝ) / 1000000000000000000 ≤
      ((399 : ℝ)/512)^2 *
        (∫ x in (((399 : ℝ)/512))..((((399+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_399).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((399 : ℝ)/512)^2 by positivity)
  have hn :
      (34648449 : ℝ) / 1000000000000000000 ≤
        ((399 : ℝ)/512)^2 *
          (5705292848409/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (399/512 : ℝ) = ((399 : ℝ)/512) := by
    norm_num
  have hright :
      (25/32 : ℝ) = (((( 399+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((399 : ℝ)/512)^2 *
        (5705292848409/100000000000000000000000 : ℝ) ≤
      ((399 : ℝ)/512)^2 *
        (∫ x in (((399 : ℝ)/512))..((((399+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_400 :
    (34045254 : ℝ) / 1000000000000000000 ≤
      ((400 : ℝ)/512)^2 *
        (∫ x in (((400 : ℝ)/512))..((((400+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_400).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((400 : ℝ)/512)^2 by positivity)
  have hn :
      (34045254 : ℝ) / 1000000000000000000 ≤
        ((400 : ℝ)/512)^2 *
          (5577974506257/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (25/32 : ℝ) = ((400 : ℝ)/512) := by
    norm_num
  have hright :
      (401/512 : ℝ) = (((( 400+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((400 : ℝ)/512)^2 *
        (5577974506257/100000000000000000000000 : ℝ) ≤
      ((400 : ℝ)/512)^2 *
        (∫ x in (((400 : ℝ)/512))..((((400+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_401 :
    (33441558 : ℝ) / 1000000000000000000 ≤
      ((401 : ℝ)/512)^2 *
        (∫ x in (((401 : ℝ)/512))..((((401+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_401).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((401 : ℝ)/512)^2 by positivity)
  have hn :
      (33441558 : ℝ) / 1000000000000000000 ≤
        ((401 : ℝ)/512)^2 *
          (681471510591/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (401/512 : ℝ) = ((401 : ℝ)/512) := by
    norm_num
  have hright :
      (201/256 : ℝ) = (((( 401+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((401 : ℝ)/512)^2 *
        (681471510591/12500000000000000000000 : ℝ) ≤
      ((401 : ℝ)/512)^2 *
        (∫ x in (((401 : ℝ)/512))..((((401+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_402 :
    (32837752 : ℝ) / 1000000000000000000 ≤
      ((402 : ℝ)/512)^2 *
        (∫ x in (((402 : ℝ)/512))..((((402+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_402).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((402 : ℝ)/512)^2 by positivity)
  have hn :
      (32837752 : ℝ) / 1000000000000000000 ≤
        ((402 : ℝ)/512)^2 *
          (2663368410369/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (201/256 : ℝ) = ((402 : ℝ)/512) := by
    norm_num
  have hright :
      (403/512 : ℝ) = (((( 402+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((402 : ℝ)/512)^2 *
        (2663368410369/50000000000000000000000 : ℝ) ≤
      ((402 : ℝ)/512)^2 *
        (∫ x in (((402 : ℝ)/512))..((((402+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_403 :
    (32234217 : ℝ) / 1000000000000000000 ≤
      ((403 : ℝ)/512)^2 *
        (∫ x in (((403 : ℝ)/512))..((((403+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_403).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((403 : ℝ)/512)^2 by positivity)
  have hn :
      (32234217 : ℝ) / 1000000000000000000 ≤
        ((403 : ℝ)/512)^2 *
          (104058356493/2000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (403/512 : ℝ) = ((403 : ℝ)/512) := by
    norm_num
  have hright :
      (101/128 : ℝ) = (((( 403+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((403 : ℝ)/512)^2 *
        (104058356493/2000000000000000000000 : ℝ) ≤
      ((403 : ℝ)/512)^2 *
        (∫ x in (((403 : ℝ)/512))..((((403+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_404 :
    (31631331 : ℝ) / 1000000000000000000 ≤
      ((404 : ℝ)/512)^2 *
        (∫ x in (((404 : ℝ)/512))..((((404+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_404).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((404 : ℝ)/512)^2 by positivity)
  have hn :
      (31631331 : ℝ) / 1000000000000000000 ≤
        ((404 : ℝ)/512)^2 *
          (5080362067591/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (101/128 : ℝ) = ((404 : ℝ)/512) := by
    norm_num
  have hright :
      (405/512 : ℝ) = (((( 404+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((404 : ℝ)/512)^2 *
        (5080362067591/100000000000000000000000 : ℝ) ≤
      ((404 : ℝ)/512)^2 *
        (∫ x in (((404 : ℝ)/512))..((((404+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_405 :
    (31029462 : ℝ) / 1000000000000000000 ≤
      ((405 : ℝ)/512)^2 *
        (∫ x in (((405 : ℝ)/512))..((((405+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_405).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((405 : ℝ)/512)^2 by positivity)
  have hn :
      (31029462 : ℝ) / 1000000000000000000 ≤
        ((405 : ℝ)/512)^2 *
          (4959114372093/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (405/512 : ℝ) = ((405 : ℝ)/512) := by
    norm_num
  have hright :
      (203/256 : ℝ) = (((( 405+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((405 : ℝ)/512)^2 *
        (4959114372093/100000000000000000000000 : ℝ) ≤
      ((405 : ℝ)/512)^2 *
        (∫ x in (((405 : ℝ)/512))..((((405+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_406 :
    (30428971 : ℝ) / 1000000000000000000 ≤
      ((406 : ℝ)/512)^2 *
        (∫ x in (((406 : ℝ)/512))..((((406+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_406).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((406 : ℝ)/512)^2 by positivity)
  have hn :
      (30428971 : ℝ) / 1000000000000000000 ≤
        ((406 : ℝ)/512)^2 *
          (2419608703007/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (203/256 : ℝ) = ((406 : ℝ)/512) := by
    norm_num
  have hright :
      (407/512 : ℝ) = (((( 406+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((406 : ℝ)/512)^2 *
        (2419608703007/50000000000000000000000 : ℝ) ≤
      ((406 : ℝ)/512)^2 *
        (∫ x in (((406 : ℝ)/512))..((((406+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_407 :
    (29830214 : ℝ) / 1000000000000000000 ≤
      ((407 : ℝ)/512)^2 *
        (∫ x in (((407 : ℝ)/512))..((((407+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_407).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((407 : ℝ)/512)^2 by positivity)
  have hn :
      (29830214 : ℝ) / 1000000000000000000 ≤
        ((407 : ℝ)/512)^2 *
          (4720711679679/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (407/512 : ℝ) = ((407 : ℝ)/512) := by
    norm_num
  have hright :
      (51/64 : ℝ) = (((( 407+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((407 : ℝ)/512)^2 *
        (4720711679679/100000000000000000000000 : ℝ) ≤
      ((407 : ℝ)/512)^2 *
        (∫ x in (((407 : ℝ)/512))..((((407+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_408 :
    (29233535 : ℝ) / 1000000000000000000 ≤
      ((408 : ℝ)/512)^2 *
        (∫ x in (((408 : ℝ)/512))..((((408+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_408).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((408 : ℝ)/512)^2 by positivity)
  have hn :
      (29233535 : ℝ) / 1000000000000000000 ≤
        ((408 : ℝ)/512)^2 *
          (460363554619/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (51/64 : ℝ) = ((408 : ℝ)/512) := by
    norm_num
  have hright :
      (409/512 : ℝ) = (((( 408+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((408 : ℝ)/512)^2 *
        (460363554619/10000000000000000000000 : ℝ) ≤
      ((408 : ℝ)/512)^2 *
        (∫ x in (((408 : ℝ)/512))..((((408+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_409 :
    (28639272 : ℝ) / 1000000000000000000 ≤
      ((409 : ℝ)/512)^2 *
        (∫ x in (((409 : ℝ)/512))..((((409+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_409).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((409 : ℝ)/512)^2 by positivity)
  have hn :
      (28639272 : ℝ) / 1000000000000000000 ≤
        ((409 : ℝ)/512)^2 *
          (4488025204823/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (409/512 : ℝ) = ((409 : ℝ)/512) := by
    norm_num
  have hright :
      (205/256 : ℝ) = (((( 409+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((409 : ℝ)/512)^2 *
        (4488025204823/100000000000000000000000 : ℝ) ≤
      ((409 : ℝ)/512)^2 *
        (∫ x in (((409 : ℝ)/512))..((((409+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_410 :
    (28047754 : ℝ) / 1000000000000000000 ≤
      ((410 : ℝ)/512)^2 *
        (∫ x in (((410 : ℝ)/512))..((((410+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_410).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((410 : ℝ)/512)^2 by positivity)
  have hn :
      (28047754 : ℝ) / 1000000000000000000 ≤
        ((410 : ℝ)/512)^2 *
          (874782941491/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (205/256 : ℝ) = ((410 : ℝ)/512) := by
    norm_num
  have hright :
      (411/512 : ℝ) = (((( 410+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((410 : ℝ)/512)^2 *
        (874782941491/20000000000000000000000 : ℝ) ≤
      ((410 : ℝ)/512)^2 *
        (∫ x in (((410 : ℝ)/512))..((((410+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_411 :
    (27459302 : ℝ) / 1000000000000000000 ≤
      ((411 : ℝ)/512)^2 *
        (∫ x in (((411 : ℝ)/512))..((((411+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_411).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((411 : ℝ)/512)^2 by positivity)
  have hn :
      (27459302 : ℝ) / 1000000000000000000 ≤
        ((411 : ℝ)/512)^2 *
          (532666995993/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (411/512 : ℝ) = ((411 : ℝ)/512) := by
    norm_num
  have hright :
      (103/128 : ℝ) = (((( 411+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((411 : ℝ)/512)^2 *
        (532666995993/12500000000000000000000 : ℝ) ≤
      ((411 : ℝ)/512)^2 *
        (∫ x in (((411 : ℝ)/512))..((((411+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_412 :
    (26874225 : ℝ) / 1000000000000000000 ≤
      ((412 : ℝ)/512)^2 *
        (∫ x in (((412 : ℝ)/512))..((((412+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_412).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((412 : ℝ)/512)^2 by positivity)
  have hn :
      (26874225 : ℝ) / 1000000000000000000 ≤
        ((412 : ℝ)/512)^2 *
          (6640510039/160000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (103/128 : ℝ) = ((412 : ℝ)/512) := by
    norm_num
  have hright :
      (413/512 : ℝ) = (((( 412+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((412 : ℝ)/512)^2 *
        (6640510039/160000000000000000000 : ℝ) ≤
      ((412 : ℝ)/512)^2 *
        (∫ x in (((412 : ℝ)/512))..((((412+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_413 :
    (26292827 : ℝ) / 1000000000000000000 ≤
      ((413 : ℝ)/512)^2 *
        (∫ x in (((413 : ℝ)/512))..((((413+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_413).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((413 : ℝ)/512)^2 by positivity)
  have hn :
      (26292827 : ℝ) / 1000000000000000000 ≤
        ((413 : ℝ)/512)^2 *
          (808178160819/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (413/512 : ℝ) = ((413 : ℝ)/512) := by
    norm_num
  have hright :
      (207/256 : ℝ) = (((( 413+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((413 : ℝ)/512)^2 *
        (808178160819/20000000000000000000000 : ℝ) ≤
      ((413 : ℝ)/512)^2 *
        (∫ x in (((413 : ℝ)/512))..((((413+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_414 :
    (25715399 : ℝ) / 1000000000000000000 ≤
      ((414 : ℝ)/512)^2 *
        (∫ x in (((414 : ℝ)/512))..((((414+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_414).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((414 : ℝ)/512)^2 by positivity)
  have hn :
      (25715399 : ℝ) / 1000000000000000000 ≤
        ((414 : ℝ)/512)^2 *
          (983269410363/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (207/256 : ℝ) = ((414 : ℝ)/512) := by
    norm_num
  have hright :
      (415/512 : ℝ) = (((( 414+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((414 : ℝ)/512)^2 *
        (983269410363/25000000000000000000000 : ℝ) ≤
      ((414 : ℝ)/512)^2 *
        (∫ x in (((414 : ℝ)/512))..((((414+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_415 :
    (25142224 : ℝ) / 1000000000000000000 ≤
      ((415 : ℝ)/512)^2 *
        (∫ x in (((415 : ℝ)/512))..((((415+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_415).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((415 : ℝ)/512)^2 by positivity)
  have hn :
      (25142224 : ℝ) / 1000000000000000000 ≤
        ((415 : ℝ)/512)^2 *
          (191345139907/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (415/512 : ℝ) = ((415 : ℝ)/512) := by
    norm_num
  have hright :
      (13/16 : ℝ) = (((( 415+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((415 : ℝ)/512)^2 *
        (191345139907/5000000000000000000000 : ℝ) ≤
      ((415 : ℝ)/512)^2 *
        (∫ x in (((415 : ℝ)/512))..((((415+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
