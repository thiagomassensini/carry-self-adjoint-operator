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
        (∫ x in (((64 : ℝ)/512))..((((64+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_064).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((64 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((64 : ℝ)/512)^2 *
          (1855799/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (1/8 : ℝ) = ((64 : ℝ)/512) := by
    norm_num
  have hright :
      (65/512 : ℝ) = (((( 64+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((64 : ℝ)/512)^2 *
        (1855799/100000000000000000000000 : ℝ) ≤
      ((64 : ℝ)/512)^2 *
        (∫ x in (((64 : ℝ)/512))..((((64+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_065 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((65 : ℝ)/512)^2 *
        (∫ x in (((65 : ℝ)/512))..((((65+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_065).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((65 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((65 : ℝ)/512)^2 *
          (1133899/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (65/512 : ℝ) = ((65 : ℝ)/512) := by
    norm_num
  have hright :
      (33/256 : ℝ) = (((( 65+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((65 : ℝ)/512)^2 *
        (1133899/50000000000000000000000 : ℝ) ≤
      ((65 : ℝ)/512)^2 *
        (∫ x in (((65 : ℝ)/512))..((((65+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_066 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((66 : ℝ)/512)^2 *
        (∫ x in (((66 : ℝ)/512))..((((66+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_066).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((66 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((66 : ℝ)/512)^2 *
          (276207/10000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (33/256 : ℝ) = ((66 : ℝ)/512) := by
    norm_num
  have hright :
      (67/512 : ℝ) = (((( 66+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((66 : ℝ)/512)^2 *
        (276207/10000000000000000000000 : ℝ) ≤
      ((66 : ℝ)/512)^2 *
        (∫ x in (((66 : ℝ)/512))..((((66+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_067 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((67 : ℝ)/512)^2 *
        (∫ x in (((67 : ℝ)/512))..((((67+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_067).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((67 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((67 : ℝ)/512)^2 *
          (670647/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (67/512 : ℝ) = ((67 : ℝ)/512) := by
    norm_num
  have hright :
      (17/128 : ℝ) = (((( 67+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((67 : ℝ)/512)^2 *
        (670647/20000000000000000000000 : ℝ) ≤
      ((67 : ℝ)/512)^2 *
        (∫ x in (((67 : ℝ)/512))..((((67+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_068 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((68 : ℝ)/512)^2 *
        (∫ x in (((68 : ℝ)/512))..((((68+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_068).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((68 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((68 : ℝ)/512)^2 *
          (4058191/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (17/128 : ℝ) = ((68 : ℝ)/512) := by
    norm_num
  have hright :
      (69/512 : ℝ) = (((( 68+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((68 : ℝ)/512)^2 *
        (4058191/100000000000000000000000 : ℝ) ≤
      ((68 : ℝ)/512)^2 *
        (∫ x in (((68 : ℝ)/512))..((((68+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_069 :
    (0 : ℝ) / 1000000000000000000 ≤
      ((69 : ℝ)/512)^2 *
        (∫ x in (((69 : ℝ)/512))..((((69+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_069).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((69 : ℝ)/512)^2 by positivity)
  have hn :
      (0 : ℝ) / 1000000000000000000 ≤
        ((69 : ℝ)/512)^2 *
          (244821/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (69/512 : ℝ) = ((69 : ℝ)/512) := by
    norm_num
  have hright :
      (35/256 : ℝ) = (((( 69+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((69 : ℝ)/512)^2 *
        (244821/5000000000000000000000 : ℝ) ≤
      ((69 : ℝ)/512)^2 *
        (∫ x in (((69 : ℝ)/512))..((((69+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_070 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((70 : ℝ)/512)^2 *
        (∫ x in (((70 : ℝ)/512))..((((70+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_070).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((70 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((70 : ℝ)/512)^2 *
          (5890329/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (35/256 : ℝ) = ((70 : ℝ)/512) := by
    norm_num
  have hright :
      (71/512 : ℝ) = (((( 70+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((70 : ℝ)/512)^2 *
        (5890329/100000000000000000000000 : ℝ) ≤
      ((70 : ℝ)/512)^2 *
        (∫ x in (((70 : ℝ)/512))..((((70+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_071 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((71 : ℝ)/512)^2 *
        (∫ x in (((71 : ℝ)/512))..((((71+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_071).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((71 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((71 : ℝ)/512)^2 *
          (353281/5000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (71/512 : ℝ) = ((71 : ℝ)/512) := by
    norm_num
  have hright :
      (9/64 : ℝ) = (((( 71+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((71 : ℝ)/512)^2 *
        (353281/5000000000000000000000 : ℝ) ≤
      ((71 : ℝ)/512)^2 *
        (∫ x in (((71 : ℝ)/512))..((((71+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_072 :
    (1 : ℝ) / 1000000000000000000 ≤
      ((72 : ℝ)/512)^2 *
        (∫ x in (((72 : ℝ)/512))..((((72+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_072).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((72 : ℝ)/512)^2 by positivity)
  have hn :
      (1 : ℝ) / 1000000000000000000 ≤
        ((72 : ℝ)/512)^2 *
          (8451713/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (9/64 : ℝ) = ((72 : ℝ)/512) := by
    norm_num
  have hright :
      (73/512 : ℝ) = (((( 72+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((72 : ℝ)/512)^2 *
        (8451713/100000000000000000000000 : ℝ) ≤
      ((72 : ℝ)/512)^2 *
        (∫ x in (((72 : ℝ)/512))..((((72+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_073 :
    (2 : ℝ) / 1000000000000000000 ≤
      ((73 : ℝ)/512)^2 *
        (∫ x in (((73 : ℝ)/512))..((((73+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_073).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((73 : ℝ)/512)^2 by positivity)
  have hn :
      (2 : ℝ) / 1000000000000000000 ≤
        ((73 : ℝ)/512)^2 *
          (10082203/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (73/512 : ℝ) = ((73 : ℝ)/512) := by
    norm_num
  have hright :
      (37/256 : ℝ) = (((( 73+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((73 : ℝ)/512)^2 *
        (10082203/100000000000000000000000 : ℝ) ≤
      ((73 : ℝ)/512)^2 *
        (∫ x in (((73 : ℝ)/512))..((((73+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_074 :
    (2 : ℝ) / 1000000000000000000 ≤
      ((74 : ℝ)/512)^2 *
        (∫ x in (((74 : ℝ)/512))..((((74+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_074).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((74 : ℝ)/512)^2 by positivity)
  have hn :
      (2 : ℝ) / 1000000000000000000 ≤
        ((74 : ℝ)/512)^2 *
          (2399073/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (37/256 : ℝ) = ((74 : ℝ)/512) := by
    norm_num
  have hright :
      (75/512 : ℝ) = (((( 74+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((74 : ℝ)/512)^2 *
        (2399073/20000000000000000000000 : ℝ) ≤
      ((74 : ℝ)/512)^2 *
        (∫ x in (((74 : ℝ)/512))..((((74+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_075 :
    (3 : ℝ) / 1000000000000000000 ≤
      ((75 : ℝ)/512)^2 *
        (∫ x in (((75 : ℝ)/512))..((((75+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_075).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((75 : ℝ)/512)^2 by positivity)
  have hn :
      (3 : ℝ) / 1000000000000000000 ≤
        ((75 : ℝ)/512)^2 *
          (1779339/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (75/512 : ℝ) = ((75 : ℝ)/512) := by
    norm_num
  have hright :
      (19/128 : ℝ) = (((( 75+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((75 : ℝ)/512)^2 *
        (1779339/12500000000000000000000 : ℝ) ≤
      ((75 : ℝ)/512)^2 *
        (∫ x in (((75 : ℝ)/512))..((((75+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_076 :
    (3 : ℝ) / 1000000000000000000 ≤
      ((76 : ℝ)/512)^2 *
        (∫ x in (((76 : ℝ)/512))..((((76+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_076).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((76 : ℝ)/512)^2 by positivity)
  have hn :
      (3 : ℝ) / 1000000000000000000 ≤
        ((76 : ℝ)/512)^2 *
          (16849607/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (19/128 : ℝ) = ((76 : ℝ)/512) := by
    norm_num
  have hright :
      (77/512 : ℝ) = (((( 76+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((76 : ℝ)/512)^2 *
        (16849607/100000000000000000000000 : ℝ) ≤
      ((76 : ℝ)/512)^2 *
        (∫ x in (((76 : ℝ)/512))..((((76+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_077 :
    (4 : ℝ) / 1000000000000000000 ≤
      ((77 : ℝ)/512)^2 *
        (∫ x in (((77 : ℝ)/512))..((((77+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_077).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((77 : ℝ)/512)^2 by positivity)
  have hn :
      (4 : ℝ) / 1000000000000000000 ≤
        ((77 : ℝ)/512)^2 *
          (9947967/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (77/512 : ℝ) = ((77 : ℝ)/512) := by
    norm_num
  have hright :
      (39/256 : ℝ) = (((( 77+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((77 : ℝ)/512)^2 *
        (9947967/50000000000000000000000 : ℝ) ≤
      ((77 : ℝ)/512)^2 *
        (∫ x in (((77 : ℝ)/512))..((((77+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_078 :
    (5 : ℝ) / 1000000000000000000 ≤
      ((78 : ℝ)/512)^2 *
        (∫ x in (((78 : ℝ)/512))..((((78+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_078).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((78 : ℝ)/512)^2 by positivity)
  have hn :
      (5 : ℝ) / 1000000000000000000 ≤
        ((78 : ℝ)/512)^2 *
          (5859207/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (39/256 : ℝ) = ((78 : ℝ)/512) := by
    norm_num
  have hright :
      (79/512 : ℝ) = (((( 78+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((78 : ℝ)/512)^2 *
        (5859207/25000000000000000000000 : ℝ) ≤
      ((78 : ℝ)/512)^2 *
        (∫ x in (((78 : ℝ)/512))..((((78+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_079 :
    (6 : ℝ) / 1000000000000000000 ≤
      ((79 : ℝ)/512)^2 *
        (∫ x in (((79 : ℝ)/512))..((((79+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_079).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((79 : ℝ)/512)^2 by positivity)
  have hn :
      (6 : ℝ) / 1000000000000000000 ≤
        ((79 : ℝ)/512)^2 *
          (27543479/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (79/512 : ℝ) = ((79 : ℝ)/512) := by
    norm_num
  have hright :
      (5/32 : ℝ) = (((( 79+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((79 : ℝ)/512)^2 *
        (27543479/100000000000000000000000 : ℝ) ≤
      ((79 : ℝ)/512)^2 *
        (∫ x in (((79 : ℝ)/512))..((((79+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_080 :
    (7 : ℝ) / 1000000000000000000 ≤
      ((80 : ℝ)/512)^2 *
        (∫ x in (((80 : ℝ)/512))..((((80+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_080).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((80 : ℝ)/512)^2 by positivity)
  have hn :
      (7 : ℝ) / 1000000000000000000 ≤
        ((80 : ℝ)/512)^2 *
          (32296001/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (5/32 : ℝ) = ((80 : ℝ)/512) := by
    norm_num
  have hright :
      (81/512 : ℝ) = (((( 80+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((80 : ℝ)/512)^2 *
        (32296001/100000000000000000000000 : ℝ) ≤
      ((80 : ℝ)/512)^2 *
        (∫ x in (((80 : ℝ)/512))..((((80+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_081 :
    (9 : ℝ) / 1000000000000000000 ≤
      ((81 : ℝ)/512)^2 *
        (∫ x in (((81 : ℝ)/512))..((((81+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_081).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((81 : ℝ)/512)^2 by positivity)
  have hn :
      (9 : ℝ) / 1000000000000000000 ≤
        ((81 : ℝ)/512)^2 *
          (37784381/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (81/512 : ℝ) = ((81 : ℝ)/512) := by
    norm_num
  have hright :
      (41/256 : ℝ) = (((( 81+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((81 : ℝ)/512)^2 *
        (37784381/100000000000000000000000 : ℝ) ≤
      ((81 : ℝ)/512)^2 *
        (∫ x in (((81 : ℝ)/512))..((((81+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_082 :
    (11 : ℝ) / 1000000000000000000 ≤
      ((82 : ℝ)/512)^2 *
        (∫ x in (((82 : ℝ)/512))..((((82+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_082).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((82 : ℝ)/512)^2 by positivity)
  have hn :
      (11 : ℝ) / 1000000000000000000 ≤
        ((82 : ℝ)/512)^2 *
          (44109511/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (41/256 : ℝ) = ((82 : ℝ)/512) := by
    norm_num
  have hright :
      (83/512 : ℝ) = (((( 82+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((82 : ℝ)/512)^2 *
        (44109511/100000000000000000000000 : ℝ) ≤
      ((82 : ℝ)/512)^2 *
        (∫ x in (((82 : ℝ)/512))..((((82+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_083 :
    (13 : ℝ) / 1000000000000000000 ≤
      ((83 : ℝ)/512)^2 *
        (∫ x in (((83 : ℝ)/512))..((((83+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_083).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((83 : ℝ)/512)^2 by positivity)
  have hn :
      (13 : ℝ) / 1000000000000000000 ≤
        ((83 : ℝ)/512)^2 *
          (51384301/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (83/512 : ℝ) = ((83 : ℝ)/512) := by
    norm_num
  have hright :
      (21/128 : ℝ) = (((( 83+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((83 : ℝ)/512)^2 *
        (51384301/100000000000000000000000 : ℝ) ≤
      ((83 : ℝ)/512)^2 *
        (∫ x in (((83 : ℝ)/512))..((((83+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_084 :
    (16 : ℝ) / 1000000000000000000 ≤
      ((84 : ℝ)/512)^2 *
        (∫ x in (((84 : ℝ)/512))..((((84+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_084).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((84 : ℝ)/512)^2 by positivity)
  have hn :
      (16 : ℝ) / 1000000000000000000 ≤
        ((84 : ℝ)/512)^2 *
          (11946979/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (21/128 : ℝ) = ((84 : ℝ)/512) := by
    norm_num
  have hright :
      (85/512 : ℝ) = (((( 84+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((84 : ℝ)/512)^2 *
        (11946979/20000000000000000000000 : ℝ) ≤
      ((84 : ℝ)/512)^2 *
        (∫ x in (((84 : ℝ)/512))..((((84+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_085 :
    (19 : ℝ) / 1000000000000000000 ≤
      ((85 : ℝ)/512)^2 *
        (∫ x in (((85 : ℝ)/512))..((((85+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_085).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((85 : ℝ)/512)^2 by positivity)
  have hn :
      (19 : ℝ) / 1000000000000000000 ≤
        ((85 : ℝ)/512)^2 *
          (69301969/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (85/512 : ℝ) = ((85 : ℝ)/512) := by
    norm_num
  have hright :
      (43/256 : ℝ) = (((( 85+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((85 : ℝ)/512)^2 *
        (69301969/100000000000000000000000 : ℝ) ≤
      ((85 : ℝ)/512)^2 *
        (∫ x in (((85 : ℝ)/512))..((((85+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_086 :
    (22 : ℝ) / 1000000000000000000 ≤
      ((86 : ℝ)/512)^2 *
        (∫ x in (((86 : ℝ)/512))..((((86+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_086).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((86 : ℝ)/512)^2 by positivity)
  have hn :
      (22 : ℝ) / 1000000000000000000 ≤
        ((86 : ℝ)/512)^2 *
          (40121073/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (43/256 : ℝ) = ((86 : ℝ)/512) := by
    norm_num
  have hright :
      (87/512 : ℝ) = (((( 86+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((86 : ℝ)/512)^2 *
        (40121073/50000000000000000000000 : ℝ) ≤
      ((86 : ℝ)/512)^2 *
        (∫ x in (((86 : ℝ)/512))..((((86+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_087 :
    (26 : ℝ) / 1000000000000000000 ≤
      ((87 : ℝ)/512)^2 *
        (∫ x in (((87 : ℝ)/512))..((((87+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_087).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((87 : ℝ)/512)^2 by positivity)
  have hn :
      (26 : ℝ) / 1000000000000000000 ≤
        ((87 : ℝ)/512)^2 *
          (46364757/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (87/512 : ℝ) = ((87 : ℝ)/512) := by
    norm_num
  have hright :
      (11/64 : ℝ) = (((( 87+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((87 : ℝ)/512)^2 *
        (46364757/50000000000000000000000 : ℝ) ≤
      ((87 : ℝ)/512)^2 *
        (∫ x in (((87 : ℝ)/512))..((((87+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_088 :
    (31 : ℝ) / 1000000000000000000 ≤
      ((88 : ℝ)/512)^2 *
        (∫ x in (((88 : ℝ)/512))..((((88+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_088).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((88 : ℝ)/512)^2 by positivity)
  have hn :
      (31 : ℝ) / 1000000000000000000 ≤
        ((88 : ℝ)/512)^2 *
          (53478629/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (11/64 : ℝ) = ((88 : ℝ)/512) := by
    norm_num
  have hright :
      (89/512 : ℝ) = (((( 88+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((88 : ℝ)/512)^2 *
        (53478629/50000000000000000000000 : ℝ) ≤
      ((88 : ℝ)/512)^2 *
        (∫ x in (((88 : ℝ)/512))..((((88+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_089 :
    (37 : ℝ) / 1000000000000000000 ≤
      ((89 : ℝ)/512)^2 *
        (∫ x in (((89 : ℝ)/512))..((((89+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_089).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((89 : ℝ)/512)^2 by positivity)
  have hn :
      (37 : ℝ) / 1000000000000000000 ≤
        ((89 : ℝ)/512)^2 *
          (61569707/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (89/512 : ℝ) = ((89 : ℝ)/512) := by
    norm_num
  have hright :
      (45/256 : ℝ) = (((( 89+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((89 : ℝ)/512)^2 *
        (61569707/50000000000000000000000 : ℝ) ≤
      ((89 : ℝ)/512)^2 *
        (∫ x in (((89 : ℝ)/512))..((((89+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_090 :
    (43 : ℝ) / 1000000000000000000 ≤
      ((90 : ℝ)/512)^2 *
        (∫ x in (((90 : ℝ)/512))..((((90+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_090).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((90 : ℝ)/512)^2 by positivity)
  have hn :
      (43 : ℝ) / 1000000000000000000 ≤
        ((90 : ℝ)/512)^2 *
          (8844547/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (45/256 : ℝ) = ((90 : ℝ)/512) := by
    norm_num
  have hright :
      (91/512 : ℝ) = (((( 90+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((90 : ℝ)/512)^2 *
        (8844547/6250000000000000000000 : ℝ) ≤
      ((90 : ℝ)/512)^2 *
        (∫ x in (((90 : ℝ)/512))..((((90+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_091 :
    (51 : ℝ) / 1000000000000000000 ≤
      ((91 : ℝ)/512)^2 *
        (∫ x in (((91 : ℝ)/512))..((((91+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_091).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((91 : ℝ)/512)^2 by positivity)
  have hn :
      (51 : ℝ) / 1000000000000000000 ≤
        ((91 : ℝ)/512)^2 *
          (162338787/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (91/512 : ℝ) = ((91 : ℝ)/512) := by
    norm_num
  have hright :
      (23/128 : ℝ) = (((( 91+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((91 : ℝ)/512)^2 *
        (162338787/100000000000000000000000 : ℝ) ≤
      ((91 : ℝ)/512)^2 *
        (∫ x in (((91 : ℝ)/512))..((((91+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_092 :
    (60 : ℝ) / 1000000000000000000 ≤
      ((92 : ℝ)/512)^2 *
        (∫ x in (((92 : ℝ)/512))..((((92+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_092).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((92 : ℝ)/512)^2 by positivity)
  have hn :
      (60 : ℝ) / 1000000000000000000 ≤
        ((92 : ℝ)/512)^2 *
          (92952967/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (23/128 : ℝ) = ((92 : ℝ)/512) := by
    norm_num
  have hright :
      (93/512 : ℝ) = (((( 92+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((92 : ℝ)/512)^2 *
        (92952967/50000000000000000000000 : ℝ) ≤
      ((92 : ℝ)/512)^2 *
        (∫ x in (((92 : ℝ)/512))..((((92+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_093 :
    (70 : ℝ) / 1000000000000000000 ≤
      ((93 : ℝ)/512)^2 *
        (∫ x in (((93 : ℝ)/512))..((((93+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_093).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((93 : ℝ)/512)^2 by positivity)
  have hn :
      (70 : ℝ) / 1000000000000000000 ≤
        ((93 : ℝ)/512)^2 *
          (6641619/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (93/512 : ℝ) = ((93 : ℝ)/512) := by
    norm_num
  have hright :
      (47/256 : ℝ) = (((( 93+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((93 : ℝ)/512)^2 *
        (6641619/3125000000000000000000 : ℝ) ≤
      ((93 : ℝ)/512)^2 *
        (∫ x in (((93 : ℝ)/512))..((((93+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_094 :
    (81 : ℝ) / 1000000000000000000 ≤
      ((94 : ℝ)/512)^2 *
        (∫ x in (((94 : ℝ)/512))..((((94+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_094).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((94 : ℝ)/512)^2 by positivity)
  have hn :
      (81 : ℝ) / 1000000000000000000 ≤
        ((94 : ℝ)/512)^2 *
          (242565673/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (47/256 : ℝ) = ((94 : ℝ)/512) := by
    norm_num
  have hright :
      (95/512 : ℝ) = (((( 94+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((94 : ℝ)/512)^2 *
        (242565673/100000000000000000000000 : ℝ) ≤
      ((94 : ℝ)/512)^2 *
        (∫ x in (((94 : ℝ)/512))..((((94+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_095 :
    (95 : ℝ) / 1000000000000000000 ≤
      ((95 : ℝ)/512)^2 *
        (∫ x in (((95 : ℝ)/512))..((((95+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_095).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((95 : ℝ)/512)^2 by positivity)
  have hn :
      (95 : ℝ) / 1000000000000000000 ≤
        ((95 : ℝ)/512)^2 *
          (138195527/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (95/512 : ℝ) = ((95 : ℝ)/512) := by
    norm_num
  have hright :
      (3/16 : ℝ) = (((( 95+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((95 : ℝ)/512)^2 *
        (138195527/50000000000000000000000 : ℝ) ≤
      ((95 : ℝ)/512)^2 *
        (∫ x in (((95 : ℝ)/512))..((((95+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
