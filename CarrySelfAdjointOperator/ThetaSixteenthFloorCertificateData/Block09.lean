import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_09
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_288 :
    (32796682 : ℝ) / 1000000000000000000 ≤
      ((288 : ℝ)/512)^2 *
        (∫ x in (9/16:ℝ)..(289/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_288).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((288 : ℝ)/512)^2 by positivity)
  have hn :
      (32796682 : ℝ) / 1000000000000000000 ≤
        ((288 : ℝ)/512)^2 *
          (2073074264719/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((288 : ℝ)/512)^2 *
        (2073074264719/20000000000000000000000 : ℝ) ≤
      ((288 : ℝ)/512)^2 *
        (∫ x in (9/16:ℝ)..(289/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_289 :
    (33405852 : ℝ) / 1000000000000000000 ≤
      ((289 : ℝ)/512)^2 *
        (∫ x in (289/512:ℝ)..(145/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_289).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((289 : ℝ)/512)^2 by positivity)
  have hn :
      (33405852 : ℝ) / 1000000000000000000 ≤
        ((289 : ℝ)/512)^2 *
          (2621240109221/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((289 : ℝ)/512)^2 *
        (2621240109221/25000000000000000000000 : ℝ) ≤
      ((289 : ℝ)/512)^2 *
        (∫ x in (289/512:ℝ)..(145/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_290 :
    (34014786 : ℝ) / 1000000000000000000 ≤
      ((290 : ℝ)/512)^2 *
        (∫ x in (145/256:ℝ)..(291/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_290).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((290 : ℝ)/512)^2 by positivity)
  have hn :
      (34014786 : ℝ) / 1000000000000000000 ≤
        ((290 : ℝ)/512)^2 *
          (5301291503547/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((290 : ℝ)/512)^2 *
        (5301291503547/50000000000000000000000 : ℝ) ≤
      ((290 : ℝ)/512)^2 *
        (∫ x in (145/256:ℝ)..(291/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_291 :
    (34623089 : ℝ) / 1000000000000000000 ≤
      ((291 : ℝ)/512)^2 *
        (∫ x in (291/512:ℝ)..(73/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_291).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((291 : ℝ)/512)^2 by positivity)
  have hn :
      (34623089 : ℝ) / 1000000000000000000 ≤
        ((291 : ℝ)/512)^2 *
          (41867767221/390625000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((291 : ℝ)/512)^2 *
        (41867767221/390625000000000000000 : ℝ) ≤
      ((291 : ℝ)/512)^2 *
        (∫ x in (291/512:ℝ)..(73/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_292 :
    (35230359 : ℝ) / 1000000000000000000 ≤
      ((292 : ℝ)/512)^2 *
        (∫ x in (73/128:ℝ)..(293/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_292).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((292 : ℝ)/512)^2 by positivity)
  have hn :
      (35230359 : ℝ) / 1000000000000000000 ≤
        ((292 : ℝ)/512)^2 *
          (5415783507371/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((292 : ℝ)/512)^2 *
        (5415783507371/50000000000000000000000 : ℝ) ≤
      ((292 : ℝ)/512)^2 *
        (∫ x in (73/128:ℝ)..(293/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_293 :
    (35836188 : ℝ) / 1000000000000000000 ≤
      ((293 : ℝ)/512)^2 *
        (∫ x in (293/512:ℝ)..(147/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_293).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((293 : ℝ)/512)^2 by positivity)
  have hn :
      (35836188 : ℝ) / 1000000000000000000 ≤
        ((293 : ℝ)/512)^2 *
          (10942750310497/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((293 : ℝ)/512)^2 *
        (10942750310497/100000000000000000000000 : ℝ) ≤
      ((293 : ℝ)/512)^2 *
        (∫ x in (293/512:ℝ)..(147/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_294 :
    (36440164 : ℝ) / 1000000000000000000 ≤
      ((294 : ℝ)/512)^2 *
        (∫ x in (147/256:ℝ)..(295/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_294).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((294 : ℝ)/512)^2 by positivity)
  have hn :
      (36440164 : ℝ) / 1000000000000000000 ≤
        ((294 : ℝ)/512)^2 *
          (11051611003987/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((294 : ℝ)/512)^2 *
        (11051611003987/100000000000000000000000 : ℝ) ≤
      ((294 : ℝ)/512)^2 *
        (∫ x in (147/256:ℝ)..(295/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_295 :
    (37041871 : ℝ) / 1000000000000000000 ≤
      ((295 : ℝ)/512)^2 *
        (∫ x in (295/512:ℝ)..(37/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_295).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((295 : ℝ)/512)^2 by positivity)
  have hn :
      (37041871 : ℝ) / 1000000000000000000 ≤
        ((295 : ℝ)/512)^2 *
          (11158063137479/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((295 : ℝ)/512)^2 *
        (11158063137479/100000000000000000000000 : ℝ) ≤
      ((295 : ℝ)/512)^2 *
        (∫ x in (295/512:ℝ)..(37/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_296 :
    (37640889 : ℝ) / 1000000000000000000 ≤
      ((296 : ℝ)/512)^2 *
        (∫ x in (37/64:ℝ)..(297/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_296).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((296 : ℝ)/512)^2 by positivity)
  have hn :
      (37640889 : ℝ) / 1000000000000000000 ≤
        ((296 : ℝ)/512)^2 *
          (5631011098587/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((296 : ℝ)/512)^2 *
        (5631011098587/50000000000000000000000 : ℝ) ≤
      ((296 : ℝ)/512)^2 *
        (∫ x in (37/64:ℝ)..(297/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_297 :
    (38236793 : ℝ) / 1000000000000000000 ≤
      ((297 : ℝ)/512)^2 *
        (∫ x in (297/512:ℝ)..(149/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_297).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((297 : ℝ)/512)^2 by positivity)
  have hn :
      (38236793 : ℝ) / 1000000000000000000 ≤
        ((297 : ℝ)/512)^2 *
          (11363405221771/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((297 : ℝ)/512)^2 *
        (11363405221771/100000000000000000000000 : ℝ) ≤
      ((297 : ℝ)/512)^2 *
        (∫ x in (297/512:ℝ)..(149/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_298 :
    (38829157 : ℝ) / 1000000000000000000 ≤
      ((298 : ℝ)/512)^2 *
        (∫ x in (149/256:ℝ)..(299/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_298).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((298 : ℝ)/512)^2 by positivity)
  have hn :
      (38829157 : ℝ) / 1000000000000000000 ≤
        ((298 : ℝ)/512)^2 *
          (11462130909593/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((298 : ℝ)/512)^2 *
        (11462130909593/100000000000000000000000 : ℝ) ≤
      ((298 : ℝ)/512)^2 *
        (∫ x in (149/256:ℝ)..(299/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_299 :
    (39417551 : ℝ) / 1000000000000000000 ≤
      ((299 : ℝ)/512)^2 *
        (∫ x in (299/512:ℝ)..(75/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_299).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((299 : ℝ)/512)^2 by positivity)
  have hn :
      (39417551 : ℝ) / 1000000000000000000 ≤
        ((299 : ℝ)/512)^2 *
          (5779059862039/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((299 : ℝ)/512)^2 *
        (5779059862039/50000000000000000000000 : ℝ) ≤
      ((299 : ℝ)/512)^2 *
        (∫ x in (299/512:ℝ)..(75/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_300 :
    (40001543 : ℝ) / 1000000000000000000 ≤
      ((300 : ℝ)/512)^2 *
        (∫ x in (75/128:ℝ)..(301/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_300).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((300 : ℝ)/512)^2 by positivity)
  have hn :
      (40001543 : ℝ) / 1000000000000000000 ≤
        ((300 : ℝ)/512)^2 *
          (582564699873/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((300 : ℝ)/512)^2 *
        (582564699873/5000000000000000000000 : ℝ) ≤
      ((300 : ℝ)/512)^2 *
        (∫ x in (75/128:ℝ)..(301/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_301 :
    (40580700 : ℝ) / 1000000000000000000 ≤
      ((301 : ℝ)/512)^2 *
        (∫ x in (301/512:ℝ)..(151/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_301).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((301 : ℝ)/512)^2 by positivity)
  have hn :
      (40580700 : ℝ) / 1000000000000000000 ≤
        ((301 : ℝ)/512)^2 *
          (11741578032453/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((301 : ℝ)/512)^2 *
        (11741578032453/100000000000000000000000 : ℝ) ≤
      ((301 : ℝ)/512)^2 *
        (∫ x in (301/512:ℝ)..(151/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_302 :
    (41154587 : ℝ) / 1000000000000000000 ≤
      ((302 : ℝ)/512)^2 *
        (∫ x in (151/256:ℝ)..(303/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_302).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((302 : ℝ)/512)^2 by positivity)
  have hn :
      (41154587 : ℝ) / 1000000000000000000 ≤
        ((302 : ℝ)/512)^2 *
          (2957224550439/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((302 : ℝ)/512)^2 *
        (2957224550439/25000000000000000000000 : ℝ) ≤
      ((302 : ℝ)/512)^2 *
        (∫ x in (151/256:ℝ)..(303/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_303 :
    (41722771 : ℝ) / 1000000000000000000 ≤
      ((303 : ℝ)/512)^2 *
        (∫ x in (303/512:ℝ)..(19/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_303).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((303 : ℝ)/512)^2 by positivity)
  have hn :
      (41722771 : ℝ) / 1000000000000000000 ≤
        ((303 : ℝ)/512)^2 *
          (2978295761301/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((303 : ℝ)/512)^2 *
        (2978295761301/25000000000000000000000 : ℝ) ≤
      ((303 : ℝ)/512)^2 *
        (∫ x in (303/512:ℝ)..(19/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_304 :
    (42284816 : ℝ) / 1000000000000000000 ≤
      ((304 : ℝ)/512)^2 *
        (∫ x in (19/32:ℝ)..(305/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_304).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((304 : ℝ)/512)^2 by positivity)
  have hn :
      (42284816 : ℝ) / 1000000000000000000 ≤
        ((304 : ℝ)/512)^2 *
          (11994363364393/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((304 : ℝ)/512)^2 *
        (11994363364393/100000000000000000000000 : ℝ) ≤
      ((304 : ℝ)/512)^2 *
        (∫ x in (19/32:ℝ)..(305/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_305 :
    (42840287 : ℝ) / 1000000000000000000 ≤
      ((305 : ℝ)/512)^2 *
        (∫ x in (305/512:ℝ)..(153/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_305).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((305 : ℝ)/512)^2 by positivity)
  have hn :
      (42840287 : ℝ) / 1000000000000000000 ≤
        ((305 : ℝ)/512)^2 *
          (6036186157299/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((305 : ℝ)/512)^2 *
        (6036186157299/50000000000000000000000 : ℝ) ≤
      ((305 : ℝ)/512)^2 *
        (∫ x in (305/512:ℝ)..(153/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_306 :
    (43388752 : ℝ) / 1000000000000000000 ≤
      ((306 : ℝ)/512)^2 *
        (∫ x in (153/256:ℝ)..(307/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_306).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((306 : ℝ)/512)^2 by positivity)
  have hn :
      (43388752 : ℝ) / 1000000000000000000 ≤
        ((306 : ℝ)/512)^2 *
          (12147145493837/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((306 : ℝ)/512)^2 *
        (12147145493837/100000000000000000000000 : ℝ) ≤
      ((306 : ℝ)/512)^2 *
        (∫ x in (153/256:ℝ)..(307/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_307 :
    (43929779 : ℝ) / 1000000000000000000 ≤
      ((307 : ℝ)/512)^2 *
        (∫ x in (307/512:ℝ)..(77/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_307).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((307 : ℝ)/512)^2 by positivity)
  have hn :
      (43929779 : ℝ) / 1000000000000000000 ≤
        ((307 : ℝ)/512)^2 *
          (2443724205781/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((307 : ℝ)/512)^2 *
        (2443724205781/20000000000000000000000 : ℝ) ≤
      ((307 : ℝ)/512)^2 *
        (∫ x in (307/512:ℝ)..(77/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_308 :
    (44462939 : ℝ) / 1000000000000000000 ≤
      ((308 : ℝ)/512)^2 *
        (∫ x in (77/128:ℝ)..(309/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_308).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((308 : ℝ)/512)^2 by positivity)
  have hn :
      (44462939 : ℝ) / 1000000000000000000 ≤
        ((308 : ℝ)/512)^2 *
          (767921228639/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((308 : ℝ)/512)^2 *
        (767921228639/6250000000000000000000 : ℝ) ≤
      ((308 : ℝ)/512)^2 *
        (∫ x in (77/128:ℝ)..(309/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_309 :
    (44987804 : ℝ) / 1000000000000000000 ≤
      ((309 : ℝ)/512)^2 *
        (∫ x in (309/512:ℝ)..(155/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_309).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((309 : ℝ)/512)^2 by positivity)
  have hn :
      (44987804 : ℝ) / 1000000000000000000 ≤
        ((309 : ℝ)/512)^2 *
          (1235144481137/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((309 : ℝ)/512)^2 *
        (1235144481137/10000000000000000000000 : ℝ) ≤
      ((309 : ℝ)/512)^2 *
        (∫ x in (309/512:ℝ)..(155/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_310 :
    (45503952 : ℝ) / 1000000000000000000 ≤
      ((310 : ℝ)/512)^2 *
        (∫ x in (155/256:ℝ)..(311/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_310).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((310 : ℝ)/512)^2 by positivity)
  have hn :
      (45503952 : ℝ) / 1000000000000000000 ≤
        ((310 : ℝ)/512)^2 *
          (12412682685111/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((310 : ℝ)/512)^2 *
        (12412682685111/100000000000000000000000 : ℝ) ≤
      ((310 : ℝ)/512)^2 *
        (∫ x in (155/256:ℝ)..(311/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_311 :
    (46010962 : ℝ) / 1000000000000000000 ≤
      ((311 : ℝ)/512)^2 *
        (∫ x in (311/512:ℝ)..(39/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_311).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((311 : ℝ)/512)^2 by positivity)
  have hn :
      (46010962 : ℝ) / 1000000000000000000 ≤
        ((311 : ℝ)/512)^2 *
          (38970007237/312500000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((311 : ℝ)/512)^2 *
        (38970007237/312500000000000000000 : ℝ) ≤
      ((311 : ℝ)/512)^2 *
        (∫ x in (311/512:ℝ)..(39/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_312 :
    (46508420 : ℝ) / 1000000000000000000 ≤
      ((312 : ℝ)/512)^2 *
        (∫ x in (39/64:ℝ)..(313/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_312).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((312 : ℝ)/512)^2 by positivity)
  have hn :
      (46508420 : ℝ) / 1000000000000000000 ≤
        ((312 : ℝ)/512)^2 *
          (6262277824129/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((312 : ℝ)/512)^2 *
        (6262277824129/50000000000000000000000 : ℝ) ≤
      ((312 : ℝ)/512)^2 *
        (∫ x in (39/64:ℝ)..(313/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_313 :
    (46995915 : ℝ) / 1000000000000000000 ≤
      ((313 : ℝ)/512)^2 *
        (∫ x in (313/512:ℝ)..(157/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_313).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((313 : ℝ)/512)^2 by positivity)
  have hn :
      (46995915 : ℝ) / 1000000000000000000 ≤
        ((313 : ℝ)/512)^2 *
          (785943600011/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((313 : ℝ)/512)^2 *
        (785943600011/6250000000000000000000 : ℝ) ≤
      ((313 : ℝ)/512)^2 *
        (∫ x in (313/512:ℝ)..(157/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_314 :
    (47473043 : ℝ) / 1000000000000000000 ≤
      ((314 : ℝ)/512)^2 *
        (∫ x in (157/256:ℝ)..(315/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_314).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((314 : ℝ)/512)^2 by positivity)
  have hn :
      (47473043 : ℝ) / 1000000000000000000 ≤
        ((314 : ℝ)/512)^2 *
          (1577748265417/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((314 : ℝ)/512)^2 *
        (1577748265417/12500000000000000000000 : ℝ) ≤
      ((314 : ℝ)/512)^2 *
        (∫ x in (157/256:ℝ)..(315/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_315 :
    (47939403 : ℝ) / 1000000000000000000 ≤
      ((315 : ℝ)/512)^2 *
        (∫ x in (315/512:ℝ)..(79/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_315).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((315 : ℝ)/512)^2 by positivity)
  have hn :
      (47939403 : ℝ) / 1000000000000000000 ≤
        ((315 : ℝ)/512)^2 *
          (12665182260113/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((315 : ℝ)/512)^2 *
        (12665182260113/100000000000000000000000 : ℝ) ≤
      ((315 : ℝ)/512)^2 *
        (∫ x in (315/512:ℝ)..(79/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_316 :
    (48394605 : ℝ) / 1000000000000000000 ≤
      ((316 : ℝ)/512)^2 *
        (∫ x in (79/128:ℝ)..(317/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_316).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((316 : ℝ)/512)^2 by positivity)
  have hn :
      (48394605 : ℝ) / 1000000000000000000 ≤
        ((316 : ℝ)/512)^2 *
          (508186007841/4000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((316 : ℝ)/512)^2 *
        (508186007841/4000000000000000000000 : ℝ) ≤
      ((316 : ℝ)/512)^2 *
        (∫ x in (79/128:ℝ)..(317/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_317 :
    (48838263 : ℝ) / 1000000000000000000 ≤
      ((317 : ℝ)/512)^2 *
        (∫ x in (317/512:ℝ)..(159/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_317).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((317 : ℝ)/512)^2 by positivity)
  have hn :
      (48838263 : ℝ) / 1000000000000000000 ≤
        ((317 : ℝ)/512)^2 *
          (6370178653961/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((317 : ℝ)/512)^2 *
        (6370178653961/50000000000000000000000 : ℝ) ≤
      ((317 : ℝ)/512)^2 *
        (∫ x in (317/512:ℝ)..(159/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_318 :
    (49269998 : ℝ) / 1000000000000000000 ≤
      ((318 : ℝ)/512)^2 *
        (∫ x in (159/256:ℝ)..(319/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_318).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((318 : ℝ)/512)^2 by positivity)
  have hn :
      (49269998 : ℝ) / 1000000000000000000 ≤
        ((318 : ℝ)/512)^2 *
          (12772274207789/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((318 : ℝ)/512)^2 *
        (12772274207789/100000000000000000000000 : ℝ) ≤
      ((318 : ℝ)/512)^2 *
        (∫ x in (159/256:ℝ)..(319/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_319 :
    (49689443 : ℝ) / 1000000000000000000 ≤
      ((319 : ℝ)/512)^2 *
        (∫ x in (319/512:ℝ)..(5/8:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_319).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((319 : ℝ)/512)^2 by positivity)
  have hn :
      (49689443 : ℝ) / 1000000000000000000 ≤
        ((319 : ℝ)/512)^2 *
          (12800374782077/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((319 : ℝ)/512)^2 *
        (12800374782077/100000000000000000000000 : ℝ) ≤
      ((319 : ℝ)/512)^2 *
        (∫ x in (319/512:ℝ)..(5/8:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
