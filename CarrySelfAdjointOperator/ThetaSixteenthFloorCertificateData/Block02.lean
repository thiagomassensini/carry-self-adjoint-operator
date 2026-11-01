import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_02
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_064 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((64 : ℝ)/512)^2 *
        (∫ x in (1/8:ℝ)..(65/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_064).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((64 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((64 : ℝ)/512)^2 *
          (1855799/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((64 : ℝ)/512)^2 *
        (1855799/100000000000000000000000 : ℝ) ≤
      ((64 : ℝ)/512)^2 *
        (∫ x in (1/8:ℝ)..(65/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_065 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((65 : ℝ)/512)^2 *
        (∫ x in (65/512:ℝ)..(33/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_065).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((65 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((65 : ℝ)/512)^2 *
          (1133899/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((65 : ℝ)/512)^2 *
        (1133899/50000000000000000000000 : ℝ) ≤
      ((65 : ℝ)/512)^2 *
        (∫ x in (65/512:ℝ)..(33/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_066 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((66 : ℝ)/512)^2 *
        (∫ x in (33/256:ℝ)..(67/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_066).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((66 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((66 : ℝ)/512)^2 *
          (276207/10000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((66 : ℝ)/512)^2 *
        (276207/10000000000000000000000 : ℝ) ≤
      ((66 : ℝ)/512)^2 *
        (∫ x in (33/256:ℝ)..(67/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_067 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((67 : ℝ)/512)^2 *
        (∫ x in (67/512:ℝ)..(17/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_067).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((67 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((67 : ℝ)/512)^2 *
          (670647/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((67 : ℝ)/512)^2 *
        (670647/20000000000000000000000 : ℝ) ≤
      ((67 : ℝ)/512)^2 *
        (∫ x in (67/512:ℝ)..(17/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_068 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((68 : ℝ)/512)^2 *
        (∫ x in (17/128:ℝ)..(69/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_068).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((68 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((68 : ℝ)/512)^2 *
          (4058191/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((68 : ℝ)/512)^2 *
        (4058191/100000000000000000000000 : ℝ) ≤
      ((68 : ℝ)/512)^2 *
        (∫ x in (17/128:ℝ)..(69/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_069 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((69 : ℝ)/512)^2 *
        (∫ x in (69/512:ℝ)..(35/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_069).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((69 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((69 : ℝ)/512)^2 *
          (244821/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((69 : ℝ)/512)^2 *
        (244821/5000000000000000000000 : ℝ) ≤
      ((69 : ℝ)/512)^2 *
        (∫ x in (69/512:ℝ)..(35/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_070 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((70 : ℝ)/512)^2 *
        (∫ x in (35/256:ℝ)..(71/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_070).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((70 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((70 : ℝ)/512)^2 *
          (5890329/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((70 : ℝ)/512)^2 *
        (5890329/100000000000000000000000 : ℝ) ≤
      ((70 : ℝ)/512)^2 *
        (∫ x in (35/256:ℝ)..(71/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_071 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((71 : ℝ)/512)^2 *
        (∫ x in (71/512:ℝ)..(9/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_071).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((71 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((71 : ℝ)/512)^2 *
          (353281/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((71 : ℝ)/512)^2 *
        (353281/5000000000000000000000 : ℝ) ≤
      ((71 : ℝ)/512)^2 *
        (∫ x in (71/512:ℝ)..(9/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_072 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((72 : ℝ)/512)^2 *
        (∫ x in (9/64:ℝ)..(73/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_072).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((72 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((72 : ℝ)/512)^2 *
          (8451713/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((72 : ℝ)/512)^2 *
        (8451713/100000000000000000000000 : ℝ) ≤
      ((72 : ℝ)/512)^2 *
        (∫ x in (9/64:ℝ)..(73/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_073 :
    (2 : ℝ) / 1000000000000000000 ≤
      ((73 : ℝ)/512)^2 *
        (∫ x in (73/512:ℝ)..(37/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_073).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((73 : ℝ)/512)^2 by positivity)
  have hn :
      (2 : ℝ) / 1000000000000000000 ≤
        ((73 : ℝ)/512)^2 *
          (10082203/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((73 : ℝ)/512)^2 *
        (10082203/100000000000000000000000 : ℝ) ≤
      ((73 : ℝ)/512)^2 *
        (∫ x in (73/512:ℝ)..(37/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_074 :
    (2 : ℝ) / 1000000000000000000 ≤
      ((74 : ℝ)/512)^2 *
        (∫ x in (37/256:ℝ)..(75/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_074).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((74 : ℝ)/512)^2 by positivity)
  have hn :
      (2 : ℝ) / 1000000000000000000 ≤
        ((74 : ℝ)/512)^2 *
          (2399073/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((74 : ℝ)/512)^2 *
        (2399073/20000000000000000000000 : ℝ) ≤
      ((74 : ℝ)/512)^2 *
        (∫ x in (37/256:ℝ)..(75/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_075 :
    (3 : ℝ) / 1000000000000000000 ≤
      ((75 : ℝ)/512)^2 *
        (∫ x in (75/512:ℝ)..(19/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_075).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((75 : ℝ)/512)^2 by positivity)
  have hn :
      (3 : ℝ) / 1000000000000000000 ≤
        ((75 : ℝ)/512)^2 *
          (1779339/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((75 : ℝ)/512)^2 *
        (1779339/12500000000000000000000 : ℝ) ≤
      ((75 : ℝ)/512)^2 *
        (∫ x in (75/512:ℝ)..(19/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_076 :
    (3 : ℝ) / 1000000000000000000 ≤
      ((76 : ℝ)/512)^2 *
        (∫ x in (19/128:ℝ)..(77/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_076).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((76 : ℝ)/512)^2 by positivity)
  have hn :
      (3 : ℝ) / 1000000000000000000 ≤
        ((76 : ℝ)/512)^2 *
          (16849607/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((76 : ℝ)/512)^2 *
        (16849607/100000000000000000000000 : ℝ) ≤
      ((76 : ℝ)/512)^2 *
        (∫ x in (19/128:ℝ)..(77/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_077 :
    (4 : ℝ) / 1000000000000000000 ≤
      ((77 : ℝ)/512)^2 *
        (∫ x in (77/512:ℝ)..(39/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_077).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((77 : ℝ)/512)^2 by positivity)
  have hn :
      (4 : ℝ) / 1000000000000000000 ≤
        ((77 : ℝ)/512)^2 *
          (9947967/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((77 : ℝ)/512)^2 *
        (9947967/50000000000000000000000 : ℝ) ≤
      ((77 : ℝ)/512)^2 *
        (∫ x in (77/512:ℝ)..(39/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_078 :
    (5 : ℝ) / 1000000000000000000 ≤
      ((78 : ℝ)/512)^2 *
        (∫ x in (39/256:ℝ)..(79/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_078).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((78 : ℝ)/512)^2 by positivity)
  have hn :
      (5 : ℝ) / 1000000000000000000 ≤
        ((78 : ℝ)/512)^2 *
          (5859207/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((78 : ℝ)/512)^2 *
        (5859207/25000000000000000000000 : ℝ) ≤
      ((78 : ℝ)/512)^2 *
        (∫ x in (39/256:ℝ)..(79/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_079 :
    (6 : ℝ) / 1000000000000000000 ≤
      ((79 : ℝ)/512)^2 *
        (∫ x in (79/512:ℝ)..(5/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_079).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((79 : ℝ)/512)^2 by positivity)
  have hn :
      (6 : ℝ) / 1000000000000000000 ≤
        ((79 : ℝ)/512)^2 *
          (27543479/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((79 : ℝ)/512)^2 *
        (27543479/100000000000000000000000 : ℝ) ≤
      ((79 : ℝ)/512)^2 *
        (∫ x in (79/512:ℝ)..(5/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_080 :
    (7 : ℝ) / 1000000000000000000 ≤
      ((80 : ℝ)/512)^2 *
        (∫ x in (5/32:ℝ)..(81/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_080).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((80 : ℝ)/512)^2 by positivity)
  have hn :
      (7 : ℝ) / 1000000000000000000 ≤
        ((80 : ℝ)/512)^2 *
          (32296001/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((80 : ℝ)/512)^2 *
        (32296001/100000000000000000000000 : ℝ) ≤
      ((80 : ℝ)/512)^2 *
        (∫ x in (5/32:ℝ)..(81/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_081 :
    (9 : ℝ) / 1000000000000000000 ≤
      ((81 : ℝ)/512)^2 *
        (∫ x in (81/512:ℝ)..(41/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_081).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((81 : ℝ)/512)^2 by positivity)
  have hn :
      (9 : ℝ) / 1000000000000000000 ≤
        ((81 : ℝ)/512)^2 *
          (37784381/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((81 : ℝ)/512)^2 *
        (37784381/100000000000000000000000 : ℝ) ≤
      ((81 : ℝ)/512)^2 *
        (∫ x in (81/512:ℝ)..(41/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_082 :
    (11 : ℝ) / 1000000000000000000 ≤
      ((82 : ℝ)/512)^2 *
        (∫ x in (41/256:ℝ)..(83/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_082).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((82 : ℝ)/512)^2 by positivity)
  have hn :
      (11 : ℝ) / 1000000000000000000 ≤
        ((82 : ℝ)/512)^2 *
          (44109511/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((82 : ℝ)/512)^2 *
        (44109511/100000000000000000000000 : ℝ) ≤
      ((82 : ℝ)/512)^2 *
        (∫ x in (41/256:ℝ)..(83/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_083 :
    (13 : ℝ) / 1000000000000000000 ≤
      ((83 : ℝ)/512)^2 *
        (∫ x in (83/512:ℝ)..(21/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_083).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((83 : ℝ)/512)^2 by positivity)
  have hn :
      (13 : ℝ) / 1000000000000000000 ≤
        ((83 : ℝ)/512)^2 *
          (51384301/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((83 : ℝ)/512)^2 *
        (51384301/100000000000000000000000 : ℝ) ≤
      ((83 : ℝ)/512)^2 *
        (∫ x in (83/512:ℝ)..(21/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_084 :
    (16 : ℝ) / 1000000000000000000 ≤
      ((84 : ℝ)/512)^2 *
        (∫ x in (21/128:ℝ)..(85/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_084).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((84 : ℝ)/512)^2 by positivity)
  have hn :
      (16 : ℝ) / 1000000000000000000 ≤
        ((84 : ℝ)/512)^2 *
          (11946979/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((84 : ℝ)/512)^2 *
        (11946979/20000000000000000000000 : ℝ) ≤
      ((84 : ℝ)/512)^2 *
        (∫ x in (21/128:ℝ)..(85/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_085 :
    (19 : ℝ) / 1000000000000000000 ≤
      ((85 : ℝ)/512)^2 *
        (∫ x in (85/512:ℝ)..(43/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_085).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((85 : ℝ)/512)^2 by positivity)
  have hn :
      (19 : ℝ) / 1000000000000000000 ≤
        ((85 : ℝ)/512)^2 *
          (69301969/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((85 : ℝ)/512)^2 *
        (69301969/100000000000000000000000 : ℝ) ≤
      ((85 : ℝ)/512)^2 *
        (∫ x in (85/512:ℝ)..(43/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_086 :
    (22 : ℝ) / 1000000000000000000 ≤
      ((86 : ℝ)/512)^2 *
        (∫ x in (43/256:ℝ)..(87/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_086).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((86 : ℝ)/512)^2 by positivity)
  have hn :
      (22 : ℝ) / 1000000000000000000 ≤
        ((86 : ℝ)/512)^2 *
          (40121073/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((86 : ℝ)/512)^2 *
        (40121073/50000000000000000000000 : ℝ) ≤
      ((86 : ℝ)/512)^2 *
        (∫ x in (43/256:ℝ)..(87/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_087 :
    (26 : ℝ) / 1000000000000000000 ≤
      ((87 : ℝ)/512)^2 *
        (∫ x in (87/512:ℝ)..(11/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_087).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((87 : ℝ)/512)^2 by positivity)
  have hn :
      (26 : ℝ) / 1000000000000000000 ≤
        ((87 : ℝ)/512)^2 *
          (46364757/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((87 : ℝ)/512)^2 *
        (46364757/50000000000000000000000 : ℝ) ≤
      ((87 : ℝ)/512)^2 *
        (∫ x in (87/512:ℝ)..(11/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_088 :
    (31 : ℝ) / 1000000000000000000 ≤
      ((88 : ℝ)/512)^2 *
        (∫ x in (11/64:ℝ)..(89/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_088).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((88 : ℝ)/512)^2 by positivity)
  have hn :
      (31 : ℝ) / 1000000000000000000 ≤
        ((88 : ℝ)/512)^2 *
          (53478629/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((88 : ℝ)/512)^2 *
        (53478629/50000000000000000000000 : ℝ) ≤
      ((88 : ℝ)/512)^2 *
        (∫ x in (11/64:ℝ)..(89/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_089 :
    (37 : ℝ) / 1000000000000000000 ≤
      ((89 : ℝ)/512)^2 *
        (∫ x in (89/512:ℝ)..(45/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_089).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((89 : ℝ)/512)^2 by positivity)
  have hn :
      (37 : ℝ) / 1000000000000000000 ≤
        ((89 : ℝ)/512)^2 *
          (61569707/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((89 : ℝ)/512)^2 *
        (61569707/50000000000000000000000 : ℝ) ≤
      ((89 : ℝ)/512)^2 *
        (∫ x in (89/512:ℝ)..(45/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_090 :
    (43 : ℝ) / 1000000000000000000 ≤
      ((90 : ℝ)/512)^2 *
        (∫ x in (45/256:ℝ)..(91/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_090).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((90 : ℝ)/512)^2 by positivity)
  have hn :
      (43 : ℝ) / 1000000000000000000 ≤
        ((90 : ℝ)/512)^2 *
          (8844547/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((90 : ℝ)/512)^2 *
        (8844547/6250000000000000000000 : ℝ) ≤
      ((90 : ℝ)/512)^2 *
        (∫ x in (45/256:ℝ)..(91/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_091 :
    (51 : ℝ) / 1000000000000000000 ≤
      ((91 : ℝ)/512)^2 *
        (∫ x in (91/512:ℝ)..(23/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_091).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((91 : ℝ)/512)^2 by positivity)
  have hn :
      (51 : ℝ) / 1000000000000000000 ≤
        ((91 : ℝ)/512)^2 *
          (162338787/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((91 : ℝ)/512)^2 *
        (162338787/100000000000000000000000 : ℝ) ≤
      ((91 : ℝ)/512)^2 *
        (∫ x in (91/512:ℝ)..(23/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_092 :
    (60 : ℝ) / 1000000000000000000 ≤
      ((92 : ℝ)/512)^2 *
        (∫ x in (23/128:ℝ)..(93/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_092).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((92 : ℝ)/512)^2 by positivity)
  have hn :
      (60 : ℝ) / 1000000000000000000 ≤
        ((92 : ℝ)/512)^2 *
          (92952967/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((92 : ℝ)/512)^2 *
        (92952967/50000000000000000000000 : ℝ) ≤
      ((92 : ℝ)/512)^2 *
        (∫ x in (23/128:ℝ)..(93/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_093 :
    (70 : ℝ) / 1000000000000000000 ≤
      ((93 : ℝ)/512)^2 *
        (∫ x in (93/512:ℝ)..(47/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_093).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((93 : ℝ)/512)^2 by positivity)
  have hn :
      (70 : ℝ) / 1000000000000000000 ≤
        ((93 : ℝ)/512)^2 *
          (6641619/3125000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((93 : ℝ)/512)^2 *
        (6641619/3125000000000000000000 : ℝ) ≤
      ((93 : ℝ)/512)^2 *
        (∫ x in (93/512:ℝ)..(47/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_094 :
    (81 : ℝ) / 1000000000000000000 ≤
      ((94 : ℝ)/512)^2 *
        (∫ x in (47/256:ℝ)..(95/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_094).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((94 : ℝ)/512)^2 by positivity)
  have hn :
      (81 : ℝ) / 1000000000000000000 ≤
        ((94 : ℝ)/512)^2 *
          (242565673/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((94 : ℝ)/512)^2 *
        (242565673/100000000000000000000000 : ℝ) ≤
      ((94 : ℝ)/512)^2 *
        (∫ x in (47/256:ℝ)..(95/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_095 :
    (95 : ℝ) / 1000000000000000000 ≤
      ((95 : ℝ)/512)^2 *
        (∫ x in (95/512:ℝ)..(3/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_095).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((95 : ℝ)/512)^2 by positivity)
  have hn :
      (95 : ℝ) / 1000000000000000000 ≤
        ((95 : ℝ)/512)^2 *
          (138195527/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((95 : ℝ)/512)^2 *
        (138195527/50000000000000000000000 : ℝ) ≤
      ((95 : ℝ)/512)^2 *
        (∫ x in (95/512:ℝ)..(3/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
