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
        (∫ x in (((96 : ℝ)/512))..((((96+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_096).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((96 : ℝ)/512)^2 by positivity)
  have hn :
      (110 : ℝ) / 1000000000000000000 ≤
        ((96 : ℝ)/512)^2 *
          (31442851/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (3/16 : ℝ) = ((96 : ℝ)/512) := by
    norm_num
  have hright :
      (97/512 : ℝ) = (((( 96+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((96 : ℝ)/512)^2 *
        (31442851/10000000000000000000000 : ℝ) ≤
      ((96 : ℝ)/512)^2 *
        (∫ x in (((96 : ℝ)/512))..((((96+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_097 :
    (128 : ℝ) / 1000000000000000000 ≤
      ((97 : ℝ)/512)^2 *
        (∫ x in (((97 : ℝ)/512))..((((97+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_097).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((97 : ℝ)/512)^2 by positivity)
  have hn :
      (128 : ℝ) / 1000000000000000000 ≤
        ((97 : ℝ)/512)^2 *
          (178569289/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (97/512 : ℝ) = ((97 : ℝ)/512) := by
    norm_num
  have hright :
      (49/256 : ℝ) = (((( 97+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((97 : ℝ)/512)^2 *
        (178569289/50000000000000000000000 : ℝ) ≤
      ((97 : ℝ)/512)^2 *
        (∫ x in (((97 : ℝ)/512))..((((97+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_098 :
    (148 : ℝ) / 1000000000000000000 ≤
      ((98 : ℝ)/512)^2 *
        (∫ x in (((98 : ℝ)/512))..((((98+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_098).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((98 : ℝ)/512)^2 by positivity)
  have hn :
      (148 : ℝ) / 1000000000000000000 ≤
        ((98 : ℝ)/512)^2 *
          (405024901/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (49/256 : ℝ) = ((98 : ℝ)/512) := by
    norm_num
  have hright :
      (99/512 : ℝ) = (((( 98+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((98 : ℝ)/512)^2 *
        (405024901/100000000000000000000000 : ℝ) ≤
      ((98 : ℝ)/512)^2 *
        (∫ x in (((98 : ℝ)/512))..((((98+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_099 :
    (171 : ℝ) / 1000000000000000000 ≤
      ((99 : ℝ)/512)^2 *
        (∫ x in (((99 : ℝ)/512))..((((99+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_099).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((99 : ℝ)/512)^2 by positivity)
  have hn :
      (171 : ℝ) / 1000000000000000000 ≤
        ((99 : ℝ)/512)^2 *
          (458637531/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (99/512 : ℝ) = ((99 : ℝ)/512) := by
    norm_num
  have hright :
      (25/128 : ℝ) = (((( 99+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((99 : ℝ)/512)^2 *
        (458637531/100000000000000000000000 : ℝ) ≤
      ((99 : ℝ)/512)^2 *
        (∫ x in (((99 : ℝ)/512))..((((99+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_100 :
    (197 : ℝ) / 1000000000000000000 ≤
      ((100 : ℝ)/512)^2 *
        (∫ x in (((100 : ℝ)/512))..((((100+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_100).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((100 : ℝ)/512)^2 by positivity)
  have hn :
      (197 : ℝ) / 1000000000000000000 ≤
        ((100 : ℝ)/512)^2 *
          (64822053/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (25/128 : ℝ) = ((100 : ℝ)/512) := by
    norm_num
  have hright :
      (101/512 : ℝ) = (((( 100+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((100 : ℝ)/512)^2 *
        (64822053/12500000000000000000000 : ℝ) ≤
      ((100 : ℝ)/512)^2 *
        (∫ x in (((100 : ℝ)/512))..((((100+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_101 :
    (227 : ℝ) / 1000000000000000000 ≤
      ((101 : ℝ)/512)^2 *
        (∫ x in (((101 : ℝ)/512))..((((101+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_101).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((101 : ℝ)/512)^2 by positivity)
  have hn :
      (227 : ℝ) / 1000000000000000000 ≤
        ((101 : ℝ)/512)^2 *
          (29274757/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (101/512 : ℝ) = ((101 : ℝ)/512) := by
    norm_num
  have hright :
      (51/256 : ℝ) = (((( 101+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((101 : ℝ)/512)^2 *
        (29274757/5000000000000000000000 : ℝ) ≤
      ((101 : ℝ)/512)^2 *
        (∫ x in (((101 : ℝ)/512))..((((101+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_102 :
    (261 : ℝ) / 1000000000000000000 ≤
      ((102 : ℝ)/512)^2 *
        (∫ x in (((102 : ℝ)/512))..((((102+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_102).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((102 : ℝ)/512)^2 by positivity)
  have hn :
      (261 : ℝ) / 1000000000000000000 ≤
        ((102 : ℝ)/512)^2 *
          (660104727/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (51/256 : ℝ) = ((102 : ℝ)/512) := by
    norm_num
  have hright :
      (103/512 : ℝ) = (((( 102+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((102 : ℝ)/512)^2 *
        (660104727/100000000000000000000000 : ℝ) ≤
      ((102 : ℝ)/512)^2 *
        (∫ x in (((102 : ℝ)/512))..((((102+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_103 :
    (300 : ℝ) / 1000000000000000000 ≤
      ((103 : ℝ)/512)^2 *
        (∫ x in (((103 : ℝ)/512))..((((103+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_103).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((103 : ℝ)/512)^2 by positivity)
  have hn :
      (300 : ℝ) / 1000000000000000000 ≤
        ((103 : ℝ)/512)^2 *
          (371588917/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (103/512 : ℝ) = ((103 : ℝ)/512) := by
    norm_num
  have hright :
      (13/64 : ℝ) = (((( 103+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((103 : ℝ)/512)^2 *
        (371588917/50000000000000000000000 : ℝ) ≤
      ((103 : ℝ)/512)^2 *
        (∫ x in (((103 : ℝ)/512))..((((103+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_104 :
    (344 : ℝ) / 1000000000000000000 ≤
      ((104 : ℝ)/512)^2 *
        (∫ x in (((104 : ℝ)/512))..((((104+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_104).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((104 : ℝ)/512)^2 by positivity)
  have hn :
      (344 : ℝ) / 1000000000000000000 ≤
        ((104 : ℝ)/512)^2 *
          (417776507/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (13/64 : ℝ) = ((104 : ℝ)/512) := by
    norm_num
  have hright :
      (105/512 : ℝ) = (((( 104+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((104 : ℝ)/512)^2 *
        (417776507/50000000000000000000000 : ℝ) ≤
      ((104 : ℝ)/512)^2 *
        (∫ x in (((104 : ℝ)/512))..((((104+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_105 :
    (394 : ℝ) / 1000000000000000000 ≤
      ((105 : ℝ)/512)^2 *
        (∫ x in (((105 : ℝ)/512))..((((105+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_105).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((105 : ℝ)/512)^2 by positivity)
  have hn :
      (394 : ℝ) / 1000000000000000000 ≤
        ((105 : ℝ)/512)^2 *
          (938139267/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (105/512 : ℝ) = ((105 : ℝ)/512) := by
    norm_num
  have hright :
      (53/256 : ℝ) = (((( 105+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((105 : ℝ)/512)^2 *
        (938139267/100000000000000000000000 : ℝ) ≤
      ((105 : ℝ)/512)^2 *
        (∫ x in (((105 : ℝ)/512))..((((105+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_106 :
    (450 : ℝ) / 1000000000000000000 ≤
      ((106 : ℝ)/512)^2 *
        (∫ x in (((106 : ℝ)/512))..((((106+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_106).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((106 : ℝ)/512)^2 by positivity)
  have hn :
      (450 : ℝ) / 1000000000000000000 ≤
        ((106 : ℝ)/512)^2 *
          (1051920787/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (53/256 : ℝ) = ((106 : ℝ)/512) := by
    norm_num
  have hright :
      (107/512 : ℝ) = (((( 106+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((106 : ℝ)/512)^2 *
        (1051920787/100000000000000000000000 : ℝ) ≤
      ((106 : ℝ)/512)^2 *
        (∫ x in (((106 : ℝ)/512))..((((106+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_107 :
    (514 : ℝ) / 1000000000000000000 ≤
      ((107 : ℝ)/512)^2 *
        (∫ x in (((107 : ℝ)/512))..((((107+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_107).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((107 : ℝ)/512)^2 by positivity)
  have hn :
      (514 : ℝ) / 1000000000000000000 ≤
        ((107 : ℝ)/512)^2 *
          (1177961949/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (107/512 : ℝ) = ((107 : ℝ)/512) := by
    norm_num
  have hright :
      (27/128 : ℝ) = (((( 107+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((107 : ℝ)/512)^2 *
        (1177961949/100000000000000000000000 : ℝ) ≤
      ((107 : ℝ)/512)^2 *
        (∫ x in (((107 : ℝ)/512))..((((107+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_108 :
    (586 : ℝ) / 1000000000000000000 ≤
      ((108 : ℝ)/512)^2 *
        (∫ x in (((108 : ℝ)/512))..((((108+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_108).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((108 : ℝ)/512)^2 by positivity)
  have hn :
      (586 : ℝ) / 1000000000000000000 ≤
        ((108 : ℝ)/512)^2 *
          (658706261/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (27/128 : ℝ) = ((108 : ℝ)/512) := by
    norm_num
  have hright :
      (109/512 : ℝ) = (((( 108+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((108 : ℝ)/512)^2 *
        (658706261/50000000000000000000000 : ℝ) ≤
      ((108 : ℝ)/512)^2 *
        (∫ x in (((108 : ℝ)/512))..((((108+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_109 :
    (666 : ℝ) / 1000000000000000000 ≤
      ((109 : ℝ)/512)^2 *
        (∫ x in (((109 : ℝ)/512))..((((109+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_109).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((109 : ℝ)/512)^2 by positivity)
  have hn :
      (666 : ℝ) / 1000000000000000000 ≤
        ((109 : ℝ)/512)^2 *
          (1471513117/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (109/512 : ℝ) = ((109 : ℝ)/512) := by
    norm_num
  have hright :
      (55/256 : ℝ) = (((( 109+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((109 : ℝ)/512)^2 *
        (1471513117/100000000000000000000000 : ℝ) ≤
      ((109 : ℝ)/512)^2 *
        (∫ x in (((109 : ℝ)/512))..((((109+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_110 :
    (757 : ℝ) / 1000000000000000000 ≤
      ((110 : ℝ)/512)^2 *
        (∫ x in (((110 : ℝ)/512))..((((110+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_110).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((110 : ℝ)/512)^2 by positivity)
  have hn :
      (757 : ℝ) / 1000000000000000000 ≤
        ((110 : ℝ)/512)^2 *
          (1641600879/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (55/256 : ℝ) = ((110 : ℝ)/512) := by
    norm_num
  have hright :
      (111/512 : ℝ) = (((( 110+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((110 : ℝ)/512)^2 *
        (1641600879/100000000000000000000000 : ℝ) ≤
      ((110 : ℝ)/512)^2 *
        (∫ x in (((110 : ℝ)/512))..((((110+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_111 :
    (859 : ℝ) / 1000000000000000000 ≤
      ((111 : ℝ)/512)^2 *
        (∫ x in (((111 : ℝ)/512))..((((111+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_111).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((111 : ℝ)/512)^2 by positivity)
  have hn :
      (859 : ℝ) / 1000000000000000000 ≤
        ((111 : ℝ)/512)^2 *
          (1829115413/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (111/512 : ℝ) = ((111 : ℝ)/512) := by
    norm_num
  have hright :
      (7/32 : ℝ) = (((( 111+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((111 : ℝ)/512)^2 *
        (1829115413/100000000000000000000000 : ℝ) ≤
      ((111 : ℝ)/512)^2 *
        (∫ x in (((111 : ℝ)/512))..((((111+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_112 :
    (974 : ℝ) / 1000000000000000000 ≤
      ((112 : ℝ)/512)^2 *
        (∫ x in (((112 : ℝ)/512))..((((112+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_112).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((112 : ℝ)/512)^2 by positivity)
  have hn :
      (974 : ℝ) / 1000000000000000000 ≤
        ((112 : ℝ)/512)^2 *
          (12722531/625000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (7/32 : ℝ) = ((112 : ℝ)/512) := by
    norm_num
  have hright :
      (113/512 : ℝ) = (((( 112+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((112 : ℝ)/512)^2 *
        (12722531/625000000000000000000 : ℝ) ≤
      ((112 : ℝ)/512)^2 *
        (∫ x in (((112 : ℝ)/512))..((((112+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_113 :
    (1102 : ℝ) / 1000000000000000000 ≤
      ((113 : ℝ)/512)^2 *
        (∫ x in (((113 : ℝ)/512))..((((113+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_113).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((113 : ℝ)/512)^2 by positivity)
  have hn :
      (1102 : ℝ) / 1000000000000000000 ≤
        ((113 : ℝ)/512)^2 *
          (141420801/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (113/512 : ℝ) = ((113 : ℝ)/512) := by
    norm_num
  have hright :
      (57/256 : ℝ) = (((( 113+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((113 : ℝ)/512)^2 *
        (141420801/6250000000000000000000 : ℝ) ≤
      ((113 : ℝ)/512)^2 *
        (∫ x in (((113 : ℝ)/512))..((((113+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_114 :
    (1245 : ℝ) / 1000000000000000000 ≤
      ((114 : ℝ)/512)^2 *
        (∫ x in (((114 : ℝ)/512))..((((114+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_114).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((114 : ℝ)/512)^2 by positivity)
  have hn :
      (1245 : ℝ) / 1000000000000000000 ≤
        ((114 : ℝ)/512)^2 *
          (2512284001/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (57/256 : ℝ) = ((114 : ℝ)/512) := by
    norm_num
  have hright :
      (115/512 : ℝ) = (((( 114+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((114 : ℝ)/512)^2 *
        (2512284001/100000000000000000000000 : ℝ) ≤
      ((114 : ℝ)/512)^2 *
        (∫ x in (((114 : ℝ)/512))..((((114+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_115 :
    (1405 : ℝ) / 1000000000000000000 ≤
      ((115 : ℝ)/512)^2 *
        (∫ x in (((115 : ℝ)/512))..((((115+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_115).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((115 : ℝ)/512)^2 by positivity)
  have hn :
      (1405 : ℝ) / 1000000000000000000 ≤
        ((115 : ℝ)/512)^2 *
          (2786172169/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (115/512 : ℝ) = ((115 : ℝ)/512) := by
    norm_num
  have hright :
      (29/128 : ℝ) = (((( 115+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((115 : ℝ)/512)^2 *
        (2786172169/100000000000000000000000 : ℝ) ≤
      ((115 : ℝ)/512)^2 *
        (∫ x in (((115 : ℝ)/512))..((((115+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_116 :
    (1584 : ℝ) / 1000000000000000000 ≤
      ((116 : ℝ)/512)^2 *
        (∫ x in (((116 : ℝ)/512))..((((116+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_116).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((116 : ℝ)/512)^2 by positivity)
  have hn :
      (1584 : ℝ) / 1000000000000000000 ≤
        ((116 : ℝ)/512)^2 *
          (385805847/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (29/128 : ℝ) = ((116 : ℝ)/512) := by
    norm_num
  have hright :
      (117/512 : ℝ) = (((( 116+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((116 : ℝ)/512)^2 *
        (385805847/12500000000000000000000 : ℝ) ≤
      ((116 : ℝ)/512)^2 *
        (∫ x in (((116 : ℝ)/512))..((((116+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_117 :
    (1783 : ℝ) / 1000000000000000000 ≤
      ((117 : ℝ)/512)^2 *
        (∫ x in (((117 : ℝ)/512))..((((117+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_117).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((117 : ℝ)/512)^2 by positivity)
  have hn :
      (1783 : ℝ) / 1000000000000000000 ≤
        ((117 : ℝ)/512)^2 *
          (1707650243/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (117/512 : ℝ) = ((117 : ℝ)/512) := by
    norm_num
  have hright :
      (59/256 : ℝ) = (((( 117+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((117 : ℝ)/512)^2 *
        (1707650243/50000000000000000000000 : ℝ) ≤
      ((117 : ℝ)/512)^2 *
        (∫ x in (((117 : ℝ)/512))..((((117+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_118 :
    (2005 : ℝ) / 1000000000000000000 ≤
      ((118 : ℝ)/512)^2 *
        (∫ x in (((118 : ℝ)/512))..((((118+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_118).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((118 : ℝ)/512)^2 by positivity)
  have hn :
      (2005 : ℝ) / 1000000000000000000 ≤
        ((118 : ℝ)/512)^2 *
          (3775076827/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (59/256 : ℝ) = ((118 : ℝ)/512) := by
    norm_num
  have hright :
      (119/512 : ℝ) = (((( 118+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((118 : ℝ)/512)^2 *
        (3775076827/100000000000000000000000 : ℝ) ≤
      ((118 : ℝ)/512)^2 *
        (∫ x in (((118 : ℝ)/512))..((((118+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_119 :
    (2251 : ℝ) / 1000000000000000000 ≤
      ((119 : ℝ)/512)^2 *
        (∫ x in (((119 : ℝ)/512))..((((119+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_119).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((119 : ℝ)/512)^2 by positivity)
  have hn :
      (2251 : ℝ) / 1000000000000000000 ≤
        ((119 : ℝ)/512)^2 *
          (4168278087/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (119/512 : ℝ) = ((119 : ℝ)/512) := by
    norm_num
  have hright :
      (15/64 : ℝ) = (((( 119+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((119 : ℝ)/512)^2 *
        (4168278087/100000000000000000000000 : ℝ) ≤
      ((119 : ℝ)/512)^2 *
        (∫ x in (((119 : ℝ)/512))..((((119+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_120 :
    (2525 : ℝ) / 1000000000000000000 ≤
      ((120 : ℝ)/512)^2 *
        (∫ x in (((120 : ℝ)/512))..((((120+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_120).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((120 : ℝ)/512)^2 by positivity)
  have hn :
      (2525 : ℝ) / 1000000000000000000 ≤
        ((120 : ℝ)/512)^2 *
          (287348341/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (15/64 : ℝ) = ((120 : ℝ)/512) := by
    norm_num
  have hright :
      (121/512 : ℝ) = (((( 120+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((120 : ℝ)/512)^2 *
        (287348341/6250000000000000000000 : ℝ) ≤
      ((120 : ℝ)/512)^2 *
        (∫ x in (((120 : ℝ)/512))..((((120+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_121 :
    (2829 : ℝ) / 1000000000000000000 ≤
      ((121 : ℝ)/512)^2 *
        (∫ x in (((121 : ℝ)/512))..((((121+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_121).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((121 : ℝ)/512)^2 by positivity)
  have hn :
      (2829 : ℝ) / 1000000000000000000 ≤
        ((121 : ℝ)/512)^2 *
          (5065807397/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (121/512 : ℝ) = ((121 : ℝ)/512) := by
    norm_num
  have hright :
      (61/256 : ℝ) = (((( 121+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((121 : ℝ)/512)^2 *
        (5065807397/100000000000000000000000 : ℝ) ≤
      ((121 : ℝ)/512)^2 *
        (∫ x in (((121 : ℝ)/512))..((((121+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_122 :
    (3165 : ℝ) / 1000000000000000000 ≤
      ((122 : ℝ)/512)^2 *
        (∫ x in (((122 : ℝ)/512))..((((122+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_122).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((122 : ℝ)/512)^2 by positivity)
  have hn :
      (3165 : ℝ) / 1000000000000000000 ≤
        ((122 : ℝ)/512)^2 *
          (1115201651/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (61/256 : ℝ) = ((122 : ℝ)/512) := by
    norm_num
  have hright :
      (123/512 : ℝ) = (((( 122+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((122 : ℝ)/512)^2 *
        (1115201651/20000000000000000000000 : ℝ) ≤
      ((122 : ℝ)/512)^2 *
        (∫ x in (((122 : ℝ)/512))..((((122+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_123 :
    (3538 : ℝ) / 1000000000000000000 ≤
      ((123 : ℝ)/512)^2 *
        (∫ x in (((123 : ℝ)/512))..((((123+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_123).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((123 : ℝ)/512)^2 by positivity)
  have hn :
      (3538 : ℝ) / 1000000000000000000 ≤
        ((123 : ℝ)/512)^2 *
          (1226279417/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (123/512 : ℝ) = ((123 : ℝ)/512) := by
    norm_num
  have hright :
      (31/128 : ℝ) = (((( 123+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((123 : ℝ)/512)^2 *
        (1226279417/20000000000000000000000 : ℝ) ≤
      ((123 : ℝ)/512)^2 *
        (∫ x in (((123 : ℝ)/512))..((((123+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_124 :
    (3950 : ℝ) / 1000000000000000000 ≤
      ((124 : ℝ)/512)^2 *
        (∫ x in (((124 : ℝ)/512))..((((124+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_124).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((124 : ℝ)/512)^2 by positivity)
  have hn :
      (3950 : ℝ) / 1000000000000000000 ≤
        ((124 : ℝ)/512)^2 *
          (6735396703/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (31/128 : ℝ) = ((124 : ℝ)/512) := by
    norm_num
  have hright :
      (125/512 : ℝ) = (((( 124+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((124 : ℝ)/512)^2 *
        (6735396703/100000000000000000000000 : ℝ) ≤
      ((124 : ℝ)/512)^2 *
        (∫ x in (((124 : ℝ)/512))..((((124+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_125 :
    (4405 : ℝ) / 1000000000000000000 ≤
      ((125 : ℝ)/512)^2 *
        (∫ x in (((125 : ℝ)/512))..((((125+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_125).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((125 : ℝ)/512)^2 by positivity)
  have hn :
      (4405 : ℝ) / 1000000000000000000 ≤
        ((125 : ℝ)/512)^2 *
          (7391640953/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (125/512 : ℝ) = ((125 : ℝ)/512) := by
    norm_num
  have hright :
      (63/256 : ℝ) = (((( 125+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((125 : ℝ)/512)^2 *
        (7391640953/100000000000000000000000 : ℝ) ≤
      ((125 : ℝ)/512)^2 *
        (∫ x in (((125 : ℝ)/512))..((((125+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_126 :
    (4907 : ℝ) / 1000000000000000000 ≤
      ((126 : ℝ)/512)^2 *
        (∫ x in (((126 : ℝ)/512))..((((126+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_126).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((126 : ℝ)/512)^2 by positivity)
  have hn :
      (4907 : ℝ) / 1000000000000000000 ≤
        ((126 : ℝ)/512)^2 *
          (4051992081/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (63/256 : ℝ) = ((126 : ℝ)/512) := by
    norm_num
  have hright :
      (127/512 : ℝ) = (((( 126+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((126 : ℝ)/512)^2 *
        (4051992081/50000000000000000000000 : ℝ) ≤
      ((126 : ℝ)/512)^2 *
        (∫ x in (((126 : ℝ)/512))..((((126+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_127 :
    (5461 : ℝ) / 1000000000000000000 ≤
      ((127 : ℝ)/512)^2 *
        (∫ x in (((127 : ℝ)/512))..((((127+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_127).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((127 : ℝ)/512)^2 by positivity)
  have hn :
      (5461 : ℝ) / 1000000000000000000 ≤
        ((127 : ℝ)/512)^2 *
          (2219127701/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (127/512 : ℝ) = ((127 : ℝ)/512) := by
    norm_num
  have hright :
      (1/4 : ℝ) = (((( 127+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((127 : ℝ)/512)^2 *
        (2219127701/25000000000000000000000 : ℝ) ≤
      ((127 : ℝ)/512)^2 *
        (∫ x in (((127 : ℝ)/512))..((((127+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
