import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_04
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_128 :
    (6070 : ℝ) / 1000000000000000000 ≤
      ((128 : ℝ)/512)^2 *
        (∫ x in (1/4:ℝ)..(129/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_128).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((128 : ℝ)/512)^2 by positivity)
  have hn :
      (6070 : ℝ) / 1000000000000000000 ≤
        ((128 : ℝ)/512)^2 *
          (1214193167/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((128 : ℝ)/512)^2 *
        (1214193167/12500000000000000000000 : ℝ) ≤
      ((128 : ℝ)/512)^2 *
        (∫ x in (1/4:ℝ)..(129/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_129 :
    (6741 : ℝ) / 1000000000000000000 ≤
      ((129 : ℝ)/512)^2 *
        (∫ x in (129/512:ℝ)..(65/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_129).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((129 : ℝ)/512)^2 by positivity)
  have hn :
      (6741 : ℝ) / 1000000000000000000 ≤
        ((129 : ℝ)/512)^2 *
          (5309831103/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((129 : ℝ)/512)^2 *
        (5309831103/50000000000000000000000 : ℝ) ≤
      ((129 : ℝ)/512)^2 *
        (∫ x in (129/512:ℝ)..(65/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_130 :
    (7478 : ℝ) / 1000000000000000000 ≤
      ((130 : ℝ)/512)^2 *
        (∫ x in (65/256:ℝ)..(131/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_130).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((130 : ℝ)/512)^2 by positivity)
  have hn :
      (7478 : ℝ) / 1000000000000000000 ≤
        ((130 : ℝ)/512)^2 *
          (11599696021/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((130 : ℝ)/512)^2 *
        (11599696021/100000000000000000000000 : ℝ) ≤
      ((130 : ℝ)/512)^2 *
        (∫ x in (65/256:ℝ)..(131/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_131 :
    (8286 : ℝ) / 1000000000000000000 ≤
      ((131 : ℝ)/512)^2 *
        (∫ x in (131/512:ℝ)..(33/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_131).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((131 : ℝ)/512)^2 by positivity)
  have hn :
      (8286 : ℝ) / 1000000000000000000 ≤
        ((131 : ℝ)/512)^2 *
          (12658751851/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((131 : ℝ)/512)^2 *
        (12658751851/100000000000000000000000 : ℝ) ≤
      ((131 : ℝ)/512)^2 *
        (∫ x in (131/512:ℝ)..(33/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_132 :
    (9173 : ℝ) / 1000000000000000000 ≤
      ((132 : ℝ)/512)^2 *
        (∫ x in (33/128:ℝ)..(133/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_132).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((132 : ℝ)/512)^2 by positivity)
  have hn :
      (9173 : ℝ) / 1000000000000000000 ≤
        ((132 : ℝ)/512)^2 *
          (3450553917/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((132 : ℝ)/512)^2 *
        (3450553917/25000000000000000000000 : ℝ) ≤
      ((132 : ℝ)/512)^2 *
        (∫ x in (33/128:ℝ)..(133/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_133 :
    (10145 : ℝ) / 1000000000000000000 ≤
      ((133 : ℝ)/512)^2 *
        (∫ x in (133/512:ℝ)..(67/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_133).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((133 : ℝ)/512)^2 by positivity)
  have hn :
      (10145 : ℝ) / 1000000000000000000 ≤
        ((133 : ℝ)/512)^2 *
          (1879470611/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((133 : ℝ)/512)^2 *
        (1879470611/12500000000000000000000 : ℝ) ≤
      ((133 : ℝ)/512)^2 *
        (∫ x in (133/512:ℝ)..(67/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_134 :
    (11209 : ℝ) / 1000000000000000000 ≤
      ((134 : ℝ)/512)^2 *
        (∫ x in (67/256:ℝ)..(135/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_134).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((134 : ℝ)/512)^2 by positivity)
  have hn :
      (11209 : ℝ) / 1000000000000000000 ≤
        ((134 : ℝ)/512)^2 *
          (8182689507/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((134 : ℝ)/512)^2 *
        (8182689507/50000000000000000000000 : ℝ) ≤
      ((134 : ℝ)/512)^2 *
        (∫ x in (67/256:ℝ)..(135/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_135 :
    (12373 : ℝ) / 1000000000000000000 ≤
      ((135 : ℝ)/512)^2 *
        (∫ x in (135/512:ℝ)..(17/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_135).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((135 : ℝ)/512)^2 by positivity)
  have hn :
      (12373 : ℝ) / 1000000000000000000 ≤
        ((135 : ℝ)/512)^2 *
          (3559470069/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((135 : ℝ)/512)^2 *
        (3559470069/20000000000000000000000 : ℝ) ≤
      ((135 : ℝ)/512)^2 *
        (∫ x in (135/512:ℝ)..(17/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_136 :
    (13644 : ℝ) / 1000000000000000000 ≤
      ((136 : ℝ)/512)^2 *
        (∫ x in (17/64:ℝ)..(137/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_136).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((136 : ℝ)/512)^2 by positivity)
  have hn :
      (13644 : ℝ) / 1000000000000000000 ≤
        ((136 : ℝ)/512)^2 *
          (19338294743/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((136 : ℝ)/512)^2 *
        (19338294743/100000000000000000000000 : ℝ) ≤
      ((136 : ℝ)/512)^2 *
        (∫ x in (17/64:ℝ)..(137/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_137 :
    (15032 : ℝ) / 1000000000000000000 ≤
      ((137 : ℝ)/512)^2 *
        (∫ x in (137/512:ℝ)..(69/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_137).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((137 : ℝ)/512)^2 by positivity)
  have hn :
      (15032 : ℝ) / 1000000000000000000 ≤
        ((137 : ℝ)/512)^2 *
          (328049413/1562500000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((137 : ℝ)/512)^2 *
        (328049413/1562500000000000000000 : ℝ) ≤
      ((137 : ℝ)/512)^2 *
        (∫ x in (137/512:ℝ)..(69/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_138 :
    (16545 : ℝ) / 1000000000000000000 ≤
      ((138 : ℝ)/512)^2 *
        (∫ x in (69/256:ℝ)..(139/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_138).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((138 : ℝ)/512)^2 by positivity)
  have hn :
      (16545 : ℝ) / 1000000000000000000 ≤
        ((138 : ℝ)/512)^2 *
          (11387624403/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((138 : ℝ)/512)^2 *
        (11387624403/50000000000000000000000 : ℝ) ≤
      ((138 : ℝ)/512)^2 *
        (∫ x in (69/256:ℝ)..(139/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_139 :
    (18194 : ℝ) / 1000000000000000000 ≤
      ((139 : ℝ)/512)^2 *
        (∫ x in (139/512:ℝ)..(35/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_139).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((139 : ℝ)/512)^2 by positivity)
  have hn :
      (18194 : ℝ) / 1000000000000000000 ≤
        ((139 : ℝ)/512)^2 *
          (12343102611/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((139 : ℝ)/512)^2 *
        (12343102611/50000000000000000000000 : ℝ) ≤
      ((139 : ℝ)/512)^2 *
        (∫ x in (139/512:ℝ)..(35/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_140 :
    (19990 : ℝ) / 1000000000000000000 ≤
      ((140 : ℝ)/512)^2 *
        (∫ x in (35/128:ℝ)..(141/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_140).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((140 : ℝ)/512)^2 by positivity)
  have hn :
      (19990 : ℝ) / 1000000000000000000 ≤
        ((140 : ℝ)/512)^2 *
          (6684012439/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((140 : ℝ)/512)^2 *
        (6684012439/25000000000000000000000 : ℝ) ≤
      ((140 : ℝ)/512)^2 *
        (∫ x in (35/128:ℝ)..(141/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_141 :
    (21942 : ℝ) / 1000000000000000000 ≤
      ((141 : ℝ)/512)^2 *
        (∫ x in (141/512:ℝ)..(71/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_141).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((141 : ℝ)/512)^2 by positivity)
  have hn :
      (21942 : ℝ) / 1000000000000000000 ≤
        ((141 : ℝ)/512)^2 *
          (7233294473/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((141 : ℝ)/512)^2 *
        (7233294473/25000000000000000000000 : ℝ) ≤
      ((141 : ℝ)/512)^2 *
        (∫ x in (141/512:ℝ)..(71/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_142 :
    (24065 : ℝ) / 1000000000000000000 ≤
      ((142 : ℝ)/512)^2 *
        (∫ x in (71/256:ℝ)..(143/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_142).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((142 : ℝ)/512)^2 by positivity)
  have hn :
      (24065 : ℝ) / 1000000000000000000 ≤
        ((142 : ℝ)/512)^2 *
          (31286373121/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((142 : ℝ)/512)^2 *
        (31286373121/100000000000000000000000 : ℝ) ≤
      ((142 : ℝ)/512)^2 *
        (∫ x in (71/256:ℝ)..(143/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_143 :
    (26370 : ℝ) / 1000000000000000000 ≤
      ((143 : ℝ)/512)^2 *
        (∫ x in (143/512:ℝ)..(9/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_143).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((143 : ℝ)/512)^2 by positivity)
  have hn :
      (26370 : ℝ) / 1000000000000000000 ≤
        ((143 : ℝ)/512)^2 *
          (8451204353/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((143 : ℝ)/512)^2 *
        (8451204353/25000000000000000000000 : ℝ) ≤
      ((143 : ℝ)/512)^2 *
        (∫ x in (143/512:ℝ)..(9/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_144 :
    (28870 : ℝ) / 1000000000000000000 ≤
      ((144 : ℝ)/512)^2 *
        (∫ x in (9/32:ℝ)..(145/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_144).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((144 : ℝ)/512)^2 by positivity)
  have hn :
      (28870 : ℝ) / 1000000000000000000 ≤
        ((144 : ℝ)/512)^2 *
          (18249050771/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((144 : ℝ)/512)^2 *
        (18249050771/50000000000000000000000 : ℝ) ≤
      ((144 : ℝ)/512)^2 *
        (∫ x in (9/32:ℝ)..(145/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_145 :
    (31581 : ℝ) / 1000000000000000000 ≤
      ((145 : ℝ)/512)^2 *
        (∫ x in (145/512:ℝ)..(73/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_145).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((145 : ℝ)/512)^2 by positivity)
  have hn :
      (31581 : ℝ) / 1000000000000000000 ≤
        ((145 : ℝ)/512)^2 *
          (39376235237/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((145 : ℝ)/512)^2 *
        (39376235237/100000000000000000000000 : ℝ) ≤
      ((145 : ℝ)/512)^2 *
        (∫ x in (145/512:ℝ)..(73/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_146 :
    (34517 : ℝ) / 1000000000000000000 ≤
      ((146 : ℝ)/512)^2 *
        (∫ x in (73/256:ℝ)..(147/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_146).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((146 : ℝ)/512)^2 by positivity)
  have hn :
      (34517 : ℝ) / 1000000000000000000 ≤
        ((146 : ℝ)/512)^2 *
          (2653103569/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((146 : ℝ)/512)^2 *
        (2653103569/6250000000000000000000 : ℝ) ≤
      ((146 : ℝ)/512)^2 *
        (∫ x in (73/256:ℝ)..(147/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_147 :
    (37695 : ℝ) / 1000000000000000000 ≤
      ((147 : ℝ)/512)^2 *
        (∫ x in (147/512:ℝ)..(37/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_147).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((147 : ℝ)/512)^2 by positivity)
  have hn :
      (37695 : ℝ) / 1000000000000000000 ≤
        ((147 : ℝ)/512)^2 *
          (45729244311/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((147 : ℝ)/512)^2 *
        (45729244311/100000000000000000000000 : ℝ) ≤
      ((147 : ℝ)/512)^2 *
        (∫ x in (147/512:ℝ)..(37/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_148 :
    (41132 : ℝ) / 1000000000000000000 ≤
      ((148 : ℝ)/512)^2 *
        (∫ x in (37/128:ℝ)..(149/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_148).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((148 : ℝ)/512)^2 by positivity)
  have hn :
      (41132 : ℝ) / 1000000000000000000 ≤
        ((148 : ℝ)/512)^2 *
          (49226321997/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((148 : ℝ)/512)^2 *
        (49226321997/100000000000000000000000 : ℝ) ≤
      ((148 : ℝ)/512)^2 *
        (∫ x in (37/128:ℝ)..(149/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_149 :
    (44845 : ℝ) / 1000000000000000000 ≤
      ((149 : ℝ)/512)^2 *
        (∫ x in (149/512:ℝ)..(75/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_149).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((149 : ℝ)/512)^2 by positivity)
  have hn :
      (44845 : ℝ) / 1000000000000000000 ≤
        ((149 : ℝ)/512)^2 *
          (26476336179/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((149 : ℝ)/512)^2 *
        (26476336179/50000000000000000000000 : ℝ) ≤
      ((149 : ℝ)/512)^2 *
        (∫ x in (149/512:ℝ)..(75/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_150 :
    (48855 : ℝ) / 1000000000000000000 ≤
      ((150 : ℝ)/512)^2 *
        (∫ x in (75/256:ℝ)..(151/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_150).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((150 : ℝ)/512)^2 by positivity)
  have hn :
      (48855 : ℝ) / 1000000000000000000 ≤
        ((150 : ℝ)/512)^2 *
          (14230135847/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((150 : ℝ)/512)^2 *
        (14230135847/25000000000000000000000 : ℝ) ≤
      ((150 : ℝ)/512)^2 *
        (∫ x in (75/256:ℝ)..(151/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_151 :
    (53181 : ℝ) / 1000000000000000000 ≤
      ((151 : ℝ)/512)^2 *
        (∫ x in (151/512:ℝ)..(19/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_151).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((151 : ℝ)/512)^2 by positivity)
  have hn :
      (53181 : ℝ) / 1000000000000000000 ≤
        ((151 : ℝ)/512)^2 *
          (3821416077/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((151 : ℝ)/512)^2 *
        (3821416077/6250000000000000000000 : ℝ) ≤
      ((151 : ℝ)/512)^2 *
        (∫ x in (151/512:ℝ)..(19/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_152 :
    (57844 : ℝ) / 1000000000000000000 ≤
      ((152 : ℝ)/512)^2 *
        (∫ x in (19/64:ℝ)..(153/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_152).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((152 : ℝ)/512)^2 by positivity)
  have hn :
      (57844 : ℝ) / 1000000000000000000 ≤
        ((152 : ℝ)/512)^2 *
          (32816109057/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((152 : ℝ)/512)^2 *
        (32816109057/50000000000000000000000 : ℝ) ≤
      ((152 : ℝ)/512)^2 *
        (∫ x in (19/64:ℝ)..(153/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_153 :
    (62868 : ℝ) / 1000000000000000000 ≤
      ((153 : ℝ)/512)^2 *
        (∫ x in (153/512:ℝ)..(77/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_153).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((153 : ℝ)/512)^2 by positivity)
  have hn :
      (62868 : ℝ) / 1000000000000000000 ≤
        ((153 : ℝ)/512)^2 *
          (70402919807/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((153 : ℝ)/512)^2 *
        (70402919807/100000000000000000000000 : ℝ) ≤
      ((153 : ℝ)/512)^2 *
        (∫ x in (153/512:ℝ)..(77/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_154 :
    (68276 : ℝ) / 1000000000000000000 ≤
      ((154 : ℝ)/512)^2 *
        (∫ x in (77/256:ℝ)..(155/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_154).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((154 : ℝ)/512)^2 by positivity)
  have hn :
      (68276 : ℝ) / 1000000000000000000 ≤
        ((154 : ℝ)/512)^2 *
          (18867238149/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((154 : ℝ)/512)^2 *
        (18867238149/25000000000000000000000 : ℝ) ≤
      ((154 : ℝ)/512)^2 *
        (∫ x in (77/256:ℝ)..(155/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_155 :
    (74092 : ℝ) / 1000000000000000000 ≤
      ((155 : ℝ)/512)^2 *
        (∫ x in (155/512:ℝ)..(39/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_155).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((155 : ℝ)/512)^2 by positivity)
  have hn :
      (74092 : ℝ) / 1000000000000000000 ≤
        ((155 : ℝ)/512)^2 *
          (80845009711/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((155 : ℝ)/512)^2 *
        (80845009711/100000000000000000000000 : ℝ) ≤
      ((155 : ℝ)/512)^2 *
        (∫ x in (155/512:ℝ)..(39/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_156 :
    (80344 : ℝ) / 1000000000000000000 ≤
      ((156 : ℝ)/512)^2 *
        (∫ x in (39/128:ℝ)..(157/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_156).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((156 : ℝ)/512)^2 by positivity)
  have hn :
      (80344 : ℝ) / 1000000000000000000 ≤
        ((156 : ℝ)/512)^2 *
          (43273146587/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((156 : ℝ)/512)^2 *
        (43273146587/50000000000000000000000 : ℝ) ≤
      ((156 : ℝ)/512)^2 *
        (∫ x in (39/128:ℝ)..(157/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_157 :
    (87059 : ℝ) / 1000000000000000000 ≤
      ((157 : ℝ)/512)^2 *
        (∫ x in (157/512:ℝ)..(79/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_157).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((157 : ℝ)/512)^2 by positivity)
  have hn :
      (87059 : ℝ) / 1000000000000000000 ≤
        ((157 : ℝ)/512)^2 *
          (92588519027/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((157 : ℝ)/512)^2 *
        (92588519027/100000000000000000000000 : ℝ) ≤
      ((157 : ℝ)/512)^2 *
        (∫ x in (157/512:ℝ)..(79/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_158 :
    (94266 : ℝ) / 1000000000000000000 ≤
      ((158 : ℝ)/512)^2 *
        (∫ x in (79/256:ℝ)..(159/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_158).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((158 : ℝ)/512)^2 by positivity)
  have hn :
      (94266 : ℝ) / 1000000000000000000 ≤
        ((158 : ℝ)/512)^2 *
          (98987921907/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((158 : ℝ)/512)^2 *
        (98987921907/100000000000000000000000 : ℝ) ≤
      ((158 : ℝ)/512)^2 *
        (∫ x in (79/256:ℝ)..(159/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_159 :
    (101995 : ℝ) / 1000000000000000000 ≤
      ((159 : ℝ)/512)^2 *
        (∫ x in (159/512:ℝ)..(5/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_159).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((159 : ℝ)/512)^2 by positivity)
  have hn :
      (101995 : ℝ) / 1000000000000000000 ≤
        ((159 : ℝ)/512)^2 *
          (21152251783/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((159 : ℝ)/512)^2 *
        (21152251783/20000000000000000000000 : ℝ) ≤
      ((159 : ℝ)/512)^2 *
        (∫ x in (159/512:ℝ)..(5/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
