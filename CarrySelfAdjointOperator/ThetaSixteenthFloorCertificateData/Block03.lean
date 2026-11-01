import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_03
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_096 :
    (110 : ℝ) / 1000000000000000000 ≤
      ((96 : ℝ)/512)^2 *
        (∫ x in (3/16:ℝ)..(97/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_096).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((96 : ℝ)/512)^2 by positivity)
  have hn :
      (110 : ℝ) / 1000000000000000000 ≤
        ((96 : ℝ)/512)^2 *
          (31442851/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((96 : ℝ)/512)^2 *
        (31442851/10000000000000000000000 : ℝ) ≤
      ((96 : ℝ)/512)^2 *
        (∫ x in (3/16:ℝ)..(97/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_097 :
    (128 : ℝ) / 1000000000000000000 ≤
      ((97 : ℝ)/512)^2 *
        (∫ x in (97/512:ℝ)..(49/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_097).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((97 : ℝ)/512)^2 by positivity)
  have hn :
      (128 : ℝ) / 1000000000000000000 ≤
        ((97 : ℝ)/512)^2 *
          (178569289/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((97 : ℝ)/512)^2 *
        (178569289/50000000000000000000000 : ℝ) ≤
      ((97 : ℝ)/512)^2 *
        (∫ x in (97/512:ℝ)..(49/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_098 :
    (148 : ℝ) / 1000000000000000000 ≤
      ((98 : ℝ)/512)^2 *
        (∫ x in (49/256:ℝ)..(99/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_098).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((98 : ℝ)/512)^2 by positivity)
  have hn :
      (148 : ℝ) / 1000000000000000000 ≤
        ((98 : ℝ)/512)^2 *
          (405024901/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((98 : ℝ)/512)^2 *
        (405024901/100000000000000000000000 : ℝ) ≤
      ((98 : ℝ)/512)^2 *
        (∫ x in (49/256:ℝ)..(99/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_099 :
    (171 : ℝ) / 1000000000000000000 ≤
      ((99 : ℝ)/512)^2 *
        (∫ x in (99/512:ℝ)..(25/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_099).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((99 : ℝ)/512)^2 by positivity)
  have hn :
      (171 : ℝ) / 1000000000000000000 ≤
        ((99 : ℝ)/512)^2 *
          (458637531/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((99 : ℝ)/512)^2 *
        (458637531/100000000000000000000000 : ℝ) ≤
      ((99 : ℝ)/512)^2 *
        (∫ x in (99/512:ℝ)..(25/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_100 :
    (197 : ℝ) / 1000000000000000000 ≤
      ((100 : ℝ)/512)^2 *
        (∫ x in (25/128:ℝ)..(101/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_100).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((100 : ℝ)/512)^2 by positivity)
  have hn :
      (197 : ℝ) / 1000000000000000000 ≤
        ((100 : ℝ)/512)^2 *
          (64822053/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((100 : ℝ)/512)^2 *
        (64822053/12500000000000000000000 : ℝ) ≤
      ((100 : ℝ)/512)^2 *
        (∫ x in (25/128:ℝ)..(101/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_101 :
    (227 : ℝ) / 1000000000000000000 ≤
      ((101 : ℝ)/512)^2 *
        (∫ x in (101/512:ℝ)..(51/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_101).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((101 : ℝ)/512)^2 by positivity)
  have hn :
      (227 : ℝ) / 1000000000000000000 ≤
        ((101 : ℝ)/512)^2 *
          (29274757/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((101 : ℝ)/512)^2 *
        (29274757/5000000000000000000000 : ℝ) ≤
      ((101 : ℝ)/512)^2 *
        (∫ x in (101/512:ℝ)..(51/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_102 :
    (261 : ℝ) / 1000000000000000000 ≤
      ((102 : ℝ)/512)^2 *
        (∫ x in (51/256:ℝ)..(103/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_102).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((102 : ℝ)/512)^2 by positivity)
  have hn :
      (261 : ℝ) / 1000000000000000000 ≤
        ((102 : ℝ)/512)^2 *
          (660104727/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((102 : ℝ)/512)^2 *
        (660104727/100000000000000000000000 : ℝ) ≤
      ((102 : ℝ)/512)^2 *
        (∫ x in (51/256:ℝ)..(103/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_103 :
    (300 : ℝ) / 1000000000000000000 ≤
      ((103 : ℝ)/512)^2 *
        (∫ x in (103/512:ℝ)..(13/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_103).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((103 : ℝ)/512)^2 by positivity)
  have hn :
      (300 : ℝ) / 1000000000000000000 ≤
        ((103 : ℝ)/512)^2 *
          (371588917/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((103 : ℝ)/512)^2 *
        (371588917/50000000000000000000000 : ℝ) ≤
      ((103 : ℝ)/512)^2 *
        (∫ x in (103/512:ℝ)..(13/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_104 :
    (344 : ℝ) / 1000000000000000000 ≤
      ((104 : ℝ)/512)^2 *
        (∫ x in (13/64:ℝ)..(105/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_104).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((104 : ℝ)/512)^2 by positivity)
  have hn :
      (344 : ℝ) / 1000000000000000000 ≤
        ((104 : ℝ)/512)^2 *
          (417776507/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((104 : ℝ)/512)^2 *
        (417776507/50000000000000000000000 : ℝ) ≤
      ((104 : ℝ)/512)^2 *
        (∫ x in (13/64:ℝ)..(105/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_105 :
    (394 : ℝ) / 1000000000000000000 ≤
      ((105 : ℝ)/512)^2 *
        (∫ x in (105/512:ℝ)..(53/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_105).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((105 : ℝ)/512)^2 by positivity)
  have hn :
      (394 : ℝ) / 1000000000000000000 ≤
        ((105 : ℝ)/512)^2 *
          (938139267/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((105 : ℝ)/512)^2 *
        (938139267/100000000000000000000000 : ℝ) ≤
      ((105 : ℝ)/512)^2 *
        (∫ x in (105/512:ℝ)..(53/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_106 :
    (450 : ℝ) / 1000000000000000000 ≤
      ((106 : ℝ)/512)^2 *
        (∫ x in (53/256:ℝ)..(107/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_106).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((106 : ℝ)/512)^2 by positivity)
  have hn :
      (450 : ℝ) / 1000000000000000000 ≤
        ((106 : ℝ)/512)^2 *
          (1051920787/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((106 : ℝ)/512)^2 *
        (1051920787/100000000000000000000000 : ℝ) ≤
      ((106 : ℝ)/512)^2 *
        (∫ x in (53/256:ℝ)..(107/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_107 :
    (514 : ℝ) / 1000000000000000000 ≤
      ((107 : ℝ)/512)^2 *
        (∫ x in (107/512:ℝ)..(27/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_107).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((107 : ℝ)/512)^2 by positivity)
  have hn :
      (514 : ℝ) / 1000000000000000000 ≤
        ((107 : ℝ)/512)^2 *
          (1177961949/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((107 : ℝ)/512)^2 *
        (1177961949/100000000000000000000000 : ℝ) ≤
      ((107 : ℝ)/512)^2 *
        (∫ x in (107/512:ℝ)..(27/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_108 :
    (586 : ℝ) / 1000000000000000000 ≤
      ((108 : ℝ)/512)^2 *
        (∫ x in (27/128:ℝ)..(109/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_108).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((108 : ℝ)/512)^2 by positivity)
  have hn :
      (586 : ℝ) / 1000000000000000000 ≤
        ((108 : ℝ)/512)^2 *
          (658706261/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((108 : ℝ)/512)^2 *
        (658706261/50000000000000000000000 : ℝ) ≤
      ((108 : ℝ)/512)^2 *
        (∫ x in (27/128:ℝ)..(109/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_109 :
    (666 : ℝ) / 1000000000000000000 ≤
      ((109 : ℝ)/512)^2 *
        (∫ x in (109/512:ℝ)..(55/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_109).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((109 : ℝ)/512)^2 by positivity)
  have hn :
      (666 : ℝ) / 1000000000000000000 ≤
        ((109 : ℝ)/512)^2 *
          (1471513117/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((109 : ℝ)/512)^2 *
        (1471513117/100000000000000000000000 : ℝ) ≤
      ((109 : ℝ)/512)^2 *
        (∫ x in (109/512:ℝ)..(55/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_110 :
    (757 : ℝ) / 1000000000000000000 ≤
      ((110 : ℝ)/512)^2 *
        (∫ x in (55/256:ℝ)..(111/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_110).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((110 : ℝ)/512)^2 by positivity)
  have hn :
      (757 : ℝ) / 1000000000000000000 ≤
        ((110 : ℝ)/512)^2 *
          (1641600879/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((110 : ℝ)/512)^2 *
        (1641600879/100000000000000000000000 : ℝ) ≤
      ((110 : ℝ)/512)^2 *
        (∫ x in (55/256:ℝ)..(111/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_111 :
    (859 : ℝ) / 1000000000000000000 ≤
      ((111 : ℝ)/512)^2 *
        (∫ x in (111/512:ℝ)..(7/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_111).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((111 : ℝ)/512)^2 by positivity)
  have hn :
      (859 : ℝ) / 1000000000000000000 ≤
        ((111 : ℝ)/512)^2 *
          (1829115413/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((111 : ℝ)/512)^2 *
        (1829115413/100000000000000000000000 : ℝ) ≤
      ((111 : ℝ)/512)^2 *
        (∫ x in (111/512:ℝ)..(7/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_112 :
    (974 : ℝ) / 1000000000000000000 ≤
      ((112 : ℝ)/512)^2 *
        (∫ x in (7/32:ℝ)..(113/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_112).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((112 : ℝ)/512)^2 by positivity)
  have hn :
      (974 : ℝ) / 1000000000000000000 ≤
        ((112 : ℝ)/512)^2 *
          (12722531/625000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((112 : ℝ)/512)^2 *
        (12722531/625000000000000000000 : ℝ) ≤
      ((112 : ℝ)/512)^2 *
        (∫ x in (7/32:ℝ)..(113/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_113 :
    (1102 : ℝ) / 1000000000000000000 ≤
      ((113 : ℝ)/512)^2 *
        (∫ x in (113/512:ℝ)..(57/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_113).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((113 : ℝ)/512)^2 by positivity)
  have hn :
      (1102 : ℝ) / 1000000000000000000 ≤
        ((113 : ℝ)/512)^2 *
          (141420801/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((113 : ℝ)/512)^2 *
        (141420801/6250000000000000000000 : ℝ) ≤
      ((113 : ℝ)/512)^2 *
        (∫ x in (113/512:ℝ)..(57/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_114 :
    (1245 : ℝ) / 1000000000000000000 ≤
      ((114 : ℝ)/512)^2 *
        (∫ x in (57/256:ℝ)..(115/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_114).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((114 : ℝ)/512)^2 by positivity)
  have hn :
      (1245 : ℝ) / 1000000000000000000 ≤
        ((114 : ℝ)/512)^2 *
          (2512284001/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((114 : ℝ)/512)^2 *
        (2512284001/100000000000000000000000 : ℝ) ≤
      ((114 : ℝ)/512)^2 *
        (∫ x in (57/256:ℝ)..(115/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_115 :
    (1405 : ℝ) / 1000000000000000000 ≤
      ((115 : ℝ)/512)^2 *
        (∫ x in (115/512:ℝ)..(29/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_115).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((115 : ℝ)/512)^2 by positivity)
  have hn :
      (1405 : ℝ) / 1000000000000000000 ≤
        ((115 : ℝ)/512)^2 *
          (2786172169/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((115 : ℝ)/512)^2 *
        (2786172169/100000000000000000000000 : ℝ) ≤
      ((115 : ℝ)/512)^2 *
        (∫ x in (115/512:ℝ)..(29/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_116 :
    (1584 : ℝ) / 1000000000000000000 ≤
      ((116 : ℝ)/512)^2 *
        (∫ x in (29/128:ℝ)..(117/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_116).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((116 : ℝ)/512)^2 by positivity)
  have hn :
      (1584 : ℝ) / 1000000000000000000 ≤
        ((116 : ℝ)/512)^2 *
          (385805847/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((116 : ℝ)/512)^2 *
        (385805847/12500000000000000000000 : ℝ) ≤
      ((116 : ℝ)/512)^2 *
        (∫ x in (29/128:ℝ)..(117/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_117 :
    (1783 : ℝ) / 1000000000000000000 ≤
      ((117 : ℝ)/512)^2 *
        (∫ x in (117/512:ℝ)..(59/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_117).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((117 : ℝ)/512)^2 by positivity)
  have hn :
      (1783 : ℝ) / 1000000000000000000 ≤
        ((117 : ℝ)/512)^2 *
          (1707650243/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((117 : ℝ)/512)^2 *
        (1707650243/50000000000000000000000 : ℝ) ≤
      ((117 : ℝ)/512)^2 *
        (∫ x in (117/512:ℝ)..(59/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_118 :
    (2005 : ℝ) / 1000000000000000000 ≤
      ((118 : ℝ)/512)^2 *
        (∫ x in (59/256:ℝ)..(119/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_118).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((118 : ℝ)/512)^2 by positivity)
  have hn :
      (2005 : ℝ) / 1000000000000000000 ≤
        ((118 : ℝ)/512)^2 *
          (3775076827/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((118 : ℝ)/512)^2 *
        (3775076827/100000000000000000000000 : ℝ) ≤
      ((118 : ℝ)/512)^2 *
        (∫ x in (59/256:ℝ)..(119/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_119 :
    (2251 : ℝ) / 1000000000000000000 ≤
      ((119 : ℝ)/512)^2 *
        (∫ x in (119/512:ℝ)..(15/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_119).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((119 : ℝ)/512)^2 by positivity)
  have hn :
      (2251 : ℝ) / 1000000000000000000 ≤
        ((119 : ℝ)/512)^2 *
          (4168278087/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((119 : ℝ)/512)^2 *
        (4168278087/100000000000000000000000 : ℝ) ≤
      ((119 : ℝ)/512)^2 *
        (∫ x in (119/512:ℝ)..(15/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_120 :
    (2525 : ℝ) / 1000000000000000000 ≤
      ((120 : ℝ)/512)^2 *
        (∫ x in (15/64:ℝ)..(121/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_120).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((120 : ℝ)/512)^2 by positivity)
  have hn :
      (2525 : ℝ) / 1000000000000000000 ≤
        ((120 : ℝ)/512)^2 *
          (287348341/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((120 : ℝ)/512)^2 *
        (287348341/6250000000000000000000 : ℝ) ≤
      ((120 : ℝ)/512)^2 *
        (∫ x in (15/64:ℝ)..(121/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_121 :
    (2829 : ℝ) / 1000000000000000000 ≤
      ((121 : ℝ)/512)^2 *
        (∫ x in (121/512:ℝ)..(61/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_121).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((121 : ℝ)/512)^2 by positivity)
  have hn :
      (2829 : ℝ) / 1000000000000000000 ≤
        ((121 : ℝ)/512)^2 *
          (5065807397/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((121 : ℝ)/512)^2 *
        (5065807397/100000000000000000000000 : ℝ) ≤
      ((121 : ℝ)/512)^2 *
        (∫ x in (121/512:ℝ)..(61/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_122 :
    (3165 : ℝ) / 1000000000000000000 ≤
      ((122 : ℝ)/512)^2 *
        (∫ x in (61/256:ℝ)..(123/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_122).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((122 : ℝ)/512)^2 by positivity)
  have hn :
      (3165 : ℝ) / 1000000000000000000 ≤
        ((122 : ℝ)/512)^2 *
          (1115201651/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((122 : ℝ)/512)^2 *
        (1115201651/20000000000000000000000 : ℝ) ≤
      ((122 : ℝ)/512)^2 *
        (∫ x in (61/256:ℝ)..(123/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_123 :
    (3538 : ℝ) / 1000000000000000000 ≤
      ((123 : ℝ)/512)^2 *
        (∫ x in (123/512:ℝ)..(31/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_123).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((123 : ℝ)/512)^2 by positivity)
  have hn :
      (3538 : ℝ) / 1000000000000000000 ≤
        ((123 : ℝ)/512)^2 *
          (1226279417/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((123 : ℝ)/512)^2 *
        (1226279417/20000000000000000000000 : ℝ) ≤
      ((123 : ℝ)/512)^2 *
        (∫ x in (123/512:ℝ)..(31/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_124 :
    (3950 : ℝ) / 1000000000000000000 ≤
      ((124 : ℝ)/512)^2 *
        (∫ x in (31/128:ℝ)..(125/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_124).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((124 : ℝ)/512)^2 by positivity)
  have hn :
      (3950 : ℝ) / 1000000000000000000 ≤
        ((124 : ℝ)/512)^2 *
          (6735396703/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((124 : ℝ)/512)^2 *
        (6735396703/100000000000000000000000 : ℝ) ≤
      ((124 : ℝ)/512)^2 *
        (∫ x in (31/128:ℝ)..(125/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_125 :
    (4405 : ℝ) / 1000000000000000000 ≤
      ((125 : ℝ)/512)^2 *
        (∫ x in (125/512:ℝ)..(63/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_125).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((125 : ℝ)/512)^2 by positivity)
  have hn :
      (4405 : ℝ) / 1000000000000000000 ≤
        ((125 : ℝ)/512)^2 *
          (7391640953/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((125 : ℝ)/512)^2 *
        (7391640953/100000000000000000000000 : ℝ) ≤
      ((125 : ℝ)/512)^2 *
        (∫ x in (125/512:ℝ)..(63/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_126 :
    (4907 : ℝ) / 1000000000000000000 ≤
      ((126 : ℝ)/512)^2 *
        (∫ x in (63/256:ℝ)..(127/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_126).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((126 : ℝ)/512)^2 by positivity)
  have hn :
      (4907 : ℝ) / 1000000000000000000 ≤
        ((126 : ℝ)/512)^2 *
          (4051992081/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((126 : ℝ)/512)^2 *
        (4051992081/50000000000000000000000 : ℝ) ≤
      ((126 : ℝ)/512)^2 *
        (∫ x in (63/256:ℝ)..(127/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_127 :
    (5461 : ℝ) / 1000000000000000000 ≤
      ((127 : ℝ)/512)^2 *
        (∫ x in (127/512:ℝ)..(1/4:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_127).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((127 : ℝ)/512)^2 by positivity)
  have hn :
      (5461 : ℝ) / 1000000000000000000 ≤
        ((127 : ℝ)/512)^2 *
          (2219127701/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((127 : ℝ)/512)^2 *
        (2219127701/25000000000000000000000 : ℝ) ≤
      ((127 : ℝ)/512)^2 *
        (∫ x in (127/512:ℝ)..(1/4:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
