import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_06
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_192 :
    (954369 : ℝ) / 1000000000000000000 ≤
      ((192 : ℝ)/512)^2 *
        (∫ x in (3/8:ℝ)..(193/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_192).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((192 : ℝ)/512)^2 by positivity)
  have hn :
      (954369 : ℝ) / 1000000000000000000 ≤
        ((192 : ℝ)/512)^2 *
          (339331293419/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((192 : ℝ)/512)^2 *
        (339331293419/50000000000000000000000 : ℝ) ≤
      ((192 : ℝ)/512)^2 *
        (∫ x in (3/8:ℝ)..(193/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_193 :
    (1011179 : ℝ) / 1000000000000000000 ≤
      ((193 : ℝ)/512)^2 *
        (∫ x in (193/512:ℝ)..(97/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_193).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((193 : ℝ)/512)^2 by positivity)
  have hn :
      (1011179 : ℝ) / 1000000000000000000 ≤
        ((193 : ℝ)/512)^2 *
          (88953626311/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((193 : ℝ)/512)^2 *
        (88953626311/12500000000000000000000 : ℝ) ≤
      ((193 : ℝ)/512)^2 *
        (∫ x in (193/512:ℝ)..(97/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_194 :
    (1070804 : ℝ) / 1000000000000000000 ≤
      ((194 : ℝ)/512)^2 *
        (∫ x in (97/256:ℝ)..(195/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_194).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((194 : ℝ)/512)^2 by positivity)
  have hn :
      (1070804 : ℝ) / 1000000000000000000 ≤
        ((194 : ℝ)/512)^2 *
          (745841719391/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((194 : ℝ)/512)^2 *
        (745841719391/100000000000000000000000 : ℝ) ≤
      ((194 : ℝ)/512)^2 *
        (∫ x in (97/256:ℝ)..(195/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_195 :
    (1133349 : ℝ) / 1000000000000000000 ≤
      ((195 : ℝ)/512)^2 *
        (∫ x in (195/512:ℝ)..(49/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_195).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((195 : ℝ)/512)^2 by positivity)
  have hn :
      (1133349 : ℝ) / 1000000000000000000 ≤
        ((195 : ℝ)/512)^2 *
          (390664985799/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((195 : ℝ)/512)^2 *
        (390664985799/50000000000000000000000 : ℝ) ≤
      ((195 : ℝ)/512)^2 *
        (∫ x in (195/512:ℝ)..(49/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_196 :
    (1198921 : ℝ) / 1000000000000000000 ≤
      ((196 : ℝ)/512)^2 *
        (∫ x in (49/128:ℝ)..(197/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_196).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((196 : ℝ)/512)^2 by positivity)
  have hn :
      (1198921 : ℝ) / 1000000000000000000 ≤
        ((196 : ℝ)/512)^2 *
          (409061446023/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((196 : ℝ)/512)^2 *
        (409061446023/50000000000000000000000 : ℝ) ≤
      ((196 : ℝ)/512)^2 *
        (∫ x in (49/128:ℝ)..(197/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_197 :
    (1267630 : ℝ) / 1000000000000000000 ≤
      ((197 : ℝ)/512)^2 *
        (∫ x in (197/512:ℝ)..(99/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_197).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((197 : ℝ)/512)^2 by positivity)
  have hn :
      (1267630 : ℝ) / 1000000000000000000 ≤
        ((197 : ℝ)/512)^2 *
          (428124714543/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((197 : ℝ)/512)^2 *
        (428124714543/50000000000000000000000 : ℝ) ≤
      ((197 : ℝ)/512)^2 *
        (∫ x in (197/512:ℝ)..(99/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_198 :
    (1339589 : ℝ) / 1000000000000000000 ≤
      ((198 : ℝ)/512)^2 *
        (∫ x in (99/256:ℝ)..(199/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_198).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((198 : ℝ)/512)^2 by positivity)
  have hn :
      (1339589 : ℝ) / 1000000000000000000 ≤
        ((198 : ℝ)/512)^2 *
          (895738309769/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((198 : ℝ)/512)^2 *
        (895738309769/100000000000000000000000 : ℝ) ≤
      ((198 : ℝ)/512)^2 *
        (∫ x in (99/256:ℝ)..(199/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_199 :
    (1414909 : ℝ) / 1000000000000000000 ≤
      ((199 : ℝ)/512)^2 *
        (∫ x in (199/512:ℝ)..(25/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_199).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((199 : ℝ)/512)^2 by positivity)
  have hn :
      (1414909 : ℝ) / 1000000000000000000 ≤
        ((199 : ℝ)/512)^2 *
          (468308996971/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((199 : ℝ)/512)^2 *
        (468308996971/50000000000000000000000 : ℝ) ≤
      ((199 : ℝ)/512)^2 *
        (∫ x in (199/512:ℝ)..(25/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_200 :
    (1493708 : ℝ) / 1000000000000000000 ≤
      ((200 : ℝ)/512)^2 *
        (∫ x in (25/64:ℝ)..(201/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_200).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((200 : ℝ)/512)^2 by positivity)
  have hn :
      (1493708 : ℝ) / 1000000000000000000 ≤
        ((200 : ℝ)/512)^2 *
          (978916627197/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((200 : ℝ)/512)^2 *
        (978916627197/100000000000000000000000 : ℝ) ≤
      ((200 : ℝ)/512)^2 *
        (∫ x in (25/64:ℝ)..(201/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_201 :
    (1576101 : ℝ) / 1000000000000000000 ≤
      ((201 : ℝ)/512)^2 *
        (∫ x in (201/512:ℝ)..(101/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_201).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((201 : ℝ)/512)^2 by positivity)
  have hn :
      (1576101 : ℝ) / 1000000000000000000 ≤
        ((201 : ℝ)/512)^2 *
          (1022661992721/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((201 : ℝ)/512)^2 *
        (1022661992721/100000000000000000000000 : ℝ) ≤
      ((201 : ℝ)/512)^2 *
        (∫ x in (201/512:ℝ)..(101/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_202 :
    (1662209 : ℝ) / 1000000000000000000 ≤
      ((202 : ℝ)/512)^2 *
        (∫ x in (101/256:ℝ)..(203/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_202).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((202 : ℝ)/512)^2 by positivity)
  have hn :
      (1662209 : ℝ) / 1000000000000000000 ≤
        ((202 : ℝ)/512)^2 *
          (266970365527/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((202 : ℝ)/512)^2 *
        (266970365527/25000000000000000000000 : ℝ) ≤
      ((202 : ℝ)/512)^2 *
        (∫ x in (101/256:ℝ)..(203/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_203 :
    (1752152 : ℝ) / 1000000000000000000 ≤
      ((203 : ℝ)/512)^2 *
        (∫ x in (203/512:ℝ)..(51/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_203).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((203 : ℝ)/512)^2 by positivity)
  have hn :
      (1752152 : ℝ) / 1000000000000000000 ≤
        ((203 : ℝ)/512)^2 *
          (34831310787/3125000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((203 : ℝ)/512)^2 *
        (34831310787/3125000000000000000000 : ℝ) ≤
      ((203 : ℝ)/512)^2 *
        (∫ x in (203/512:ℝ)..(51/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_204 :
    (1846052 : ℝ) / 1000000000000000000 ≤
      ((204 : ℝ)/512)^2 *
        (∫ x in (51/128:ℝ)..(205/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_204).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((204 : ℝ)/512)^2 by positivity)
  have hn :
      (1846052 : ℝ) / 1000000000000000000 ≤
        ((204 : ℝ)/512)^2 *
          (290712459727/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((204 : ℝ)/512)^2 *
        (290712459727/25000000000000000000000 : ℝ) ≤
      ((204 : ℝ)/512)^2 *
        (∫ x in (51/128:ℝ)..(205/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_205 :
    (1944032 : ℝ) / 1000000000000000000 ≤
      ((205 : ℝ)/512)^2 *
        (∫ x in (205/512:ℝ)..(103/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_205).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((205 : ℝ)/512)^2 by positivity)
  have hn :
      (1944032 : ℝ) / 1000000000000000000 ≤
        ((205 : ℝ)/512)^2 *
          (242530195083/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((205 : ℝ)/512)^2 *
        (242530195083/20000000000000000000000 : ℝ) ≤
      ((205 : ℝ)/512)^2 *
        (∫ x in (205/512:ℝ)..(103/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_206 :
    (2046218 : ℝ) / 1000000000000000000 ≤
      ((206 : ℝ)/512)^2 *
        (∫ x in (103/256:ℝ)..(207/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_206).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((206 : ℝ)/512)^2 by positivity)
  have hn :
      (2046218 : ℝ) / 1000000000000000000 ≤
        ((206 : ℝ)/512)^2 *
          (316007642319/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((206 : ℝ)/512)^2 *
        (316007642319/25000000000000000000000 : ℝ) ≤
      ((206 : ℝ)/512)^2 *
        (∫ x in (103/256:ℝ)..(207/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_207 :
    (2152736 : ℝ) / 1000000000000000000 ≤
      ((207 : ℝ)/512)^2 *
        (∫ x in (207/512:ℝ)..(13/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_207).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((207 : ℝ)/512)^2 by positivity)
  have hn :
      (2152736 : ℝ) / 1000000000000000000 ≤
        ((207 : ℝ)/512)^2 *
          (658506582019/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((207 : ℝ)/512)^2 *
        (658506582019/50000000000000000000000 : ℝ) ≤
      ((207 : ℝ)/512)^2 *
        (∫ x in (207/512:ℝ)..(13/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_208 :
    (2263713 : ℝ) / 1000000000000000000 ≤
      ((208 : ℝ)/512)^2 *
        (∫ x in (13/32:ℝ)..(209/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_208).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((208 : ℝ)/512)^2 by positivity)
  have hn :
      (2263713 : ℝ) / 1000000000000000000 ≤
        ((208 : ℝ)/512)^2 *
          (1371622578123/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((208 : ℝ)/512)^2 *
        (1371622578123/100000000000000000000000 : ℝ) ≤
      ((208 : ℝ)/512)^2 *
        (∫ x in (13/32:ℝ)..(209/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_209 :
    (2379276 : ℝ) / 1000000000000000000 ≤
      ((209 : ℝ)/512)^2 *
        (∫ x in (209/512:ℝ)..(105/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_209).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((209 : ℝ)/512)^2 by positivity)
  have hn :
      (2379276 : ℝ) / 1000000000000000000 ≤
        ((209 : ℝ)/512)^2 *
          (178485231271/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((209 : ℝ)/512)^2 *
        (178485231271/12500000000000000000000 : ℝ) ≤
      ((209 : ℝ)/512)^2 *
        (∫ x in (209/512:ℝ)..(105/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_210 :
    (2499556 : ℝ) / 1000000000000000000 ≤
      ((210 : ℝ)/512)^2 *
        (∫ x in (105/256:ℝ)..(211/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_210).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((210 : ℝ)/512)^2 by positivity)
  have hn :
      (2499556 : ℝ) / 1000000000000000000 ≤
        ((210 : ℝ)/512)^2 *
          (1485813183891/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((210 : ℝ)/512)^2 *
        (1485813183891/100000000000000000000000 : ℝ) ≤
      ((210 : ℝ)/512)^2 *
        (∫ x in (105/256:ℝ)..(211/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_211 :
    (2624681 : ℝ) / 1000000000000000000 ≤
      ((211 : ℝ)/512)^2 *
        (∫ x in (211/512:ℝ)..(53/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_211).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((211 : ℝ)/512)^2 by positivity)
  have hn :
      (2624681 : ℝ) / 1000000000000000000 ≤
        ((211 : ℝ)/512)^2 *
          (309087578513/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((211 : ℝ)/512)^2 *
        (309087578513/20000000000000000000000 : ℝ) ≤
      ((211 : ℝ)/512)^2 *
        (∫ x in (211/512:ℝ)..(53/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_212 :
    (2754781 : ℝ) / 1000000000000000000 ≤
      ((212 : ℝ)/512)^2 *
        (∫ x in (53/128:ℝ)..(213/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_212).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((212 : ℝ)/512)^2 by positivity)
  have hn :
      (2754781 : ℝ) / 1000000000000000000 ≤
        ((212 : ℝ)/512)^2 *
          (80338817159/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((212 : ℝ)/512)^2 *
        (80338817159/5000000000000000000000 : ℝ) ≤
      ((212 : ℝ)/512)^2 *
        (∫ x in (53/128:ℝ)..(213/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_213 :
    (2889989 : ℝ) / 1000000000000000000 ≤
      ((213 : ℝ)/512)^2 *
        (∫ x in (213/512:ℝ)..(107/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_213).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((213 : ℝ)/512)^2 by positivity)
  have hn :
      (2889989 : ℝ) / 1000000000000000000 ≤
        ((213 : ℝ)/512)^2 *
          (333969580083/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((213 : ℝ)/512)^2 *
        (333969580083/20000000000000000000000 : ℝ) ≤
      ((213 : ℝ)/512)^2 *
        (∫ x in (213/512:ℝ)..(107/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_214 :
    (3030433 : ℝ) / 1000000000000000000 ≤
      ((214 : ℝ)/512)^2 *
        (∫ x in (107/256:ℝ)..(215/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_214).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((214 : ℝ)/512)^2 by positivity)
  have hn :
      (3030433 : ℝ) / 1000000000000000000 ≤
        ((214 : ℝ)/512)^2 *
          (1734670870477/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((214 : ℝ)/512)^2 *
        (1734670870477/100000000000000000000000 : ℝ) ≤
      ((214 : ℝ)/512)^2 *
        (∫ x in (107/256:ℝ)..(215/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_215 :
    (3176244 : ℝ) / 1000000000000000000 ≤
      ((215 : ℝ)/512)^2 *
        (∫ x in (215/512:ℝ)..(27/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_215).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((215 : ℝ)/512)^2 by positivity)
  have hn :
      (3176244 : ℝ) / 1000000000000000000 ≤
        ((215 : ℝ)/512)^2 *
          (900631222467/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((215 : ℝ)/512)^2 *
        (900631222467/50000000000000000000000 : ℝ) ≤
      ((215 : ℝ)/512)^2 *
        (∫ x in (215/512:ℝ)..(27/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_216 :
    (3327555 : ℝ) / 1000000000000000000 ≤
      ((216 : ℝ)/512)^2 *
        (∫ x in (27/64:ℝ)..(217/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_216).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((216 : ℝ)/512)^2 by positivity)
  have hn :
      (3327555 : ℝ) / 1000000000000000000 ≤
        ((216 : ℝ)/512)^2 *
          (1869638644629/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((216 : ℝ)/512)^2 *
        (1869638644629/100000000000000000000000 : ℝ) ≤
      ((216 : ℝ)/512)^2 *
        (∫ x in (27/64:ℝ)..(217/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_217 :
    (3484493 : ℝ) / 1000000000000000000 ≤
      ((217 : ℝ)/512)^2 *
        (∫ x in (217/512:ℝ)..(109/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_217).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((217 : ℝ)/512)^2 by positivity)
  have hn :
      (3484493 : ℝ) / 1000000000000000000 ≤
        ((217 : ℝ)/512)^2 *
          (1939814263783/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((217 : ℝ)/512)^2 *
        (1939814263783/100000000000000000000000 : ℝ) ≤
      ((217 : ℝ)/512)^2 *
        (∫ x in (217/512:ℝ)..(109/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_218 :
    (3647190 : ℝ) / 1000000000000000000 ≤
      ((218 : ℝ)/512)^2 *
        (∫ x in (109/256:ℝ)..(219/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_218).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((218 : ℝ)/512)^2 by positivity)
  have hn :
      (3647190 : ℝ) / 1000000000000000000 ≤
        ((218 : ℝ)/512)^2 *
          (402360562877/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((218 : ℝ)/512)^2 *
        (402360562877/20000000000000000000000 : ℝ) ≤
      ((218 : ℝ)/512)^2 *
        (∫ x in (109/256:ℝ)..(219/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_219 :
    (3815774 : ℝ) / 1000000000000000000 ≤
      ((219 : ℝ)/512)^2 *
        (∫ x in (219/512:ℝ)..(55/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_219).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((219 : ℝ)/512)^2 by positivity)
  have hn :
      (3815774 : ℝ) / 1000000000000000000 ≤
        ((219 : ℝ)/512)^2 *
          (2085616470989/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((219 : ℝ)/512)^2 *
        (2085616470989/100000000000000000000000 : ℝ) ≤
      ((219 : ℝ)/512)^2 *
        (∫ x in (219/512:ℝ)..(55/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_220 :
    (3990374 : ℝ) / 1000000000000000000 ≤
      ((220 : ℝ)/512)^2 *
        (∫ x in (55/128:ℝ)..(221/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_220).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((220 : ℝ)/512)^2 by positivity)
  have hn :
      (3990374 : ℝ) / 1000000000000000000 ≤
        ((220 : ℝ)/512)^2 *
          (2161266016011/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((220 : ℝ)/512)^2 *
        (2161266016011/100000000000000000000000 : ℝ) ≤
      ((220 : ℝ)/512)^2 *
        (∫ x in (55/128:ℝ)..(221/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_221 :
    (4171116 : ℝ) / 1000000000000000000 ≤
      ((221 : ℝ)/512)^2 *
        (∫ x in (221/512:ℝ)..(111/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_221).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((221 : ℝ)/512)^2 by positivity)
  have hn :
      (4171116 : ℝ) / 1000000000000000000 ≤
        ((221 : ℝ)/512)^2 *
          (559690196413/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((221 : ℝ)/512)^2 *
        (559690196413/25000000000000000000000 : ℝ) ≤
      ((221 : ℝ)/512)^2 *
        (∫ x in (221/512:ℝ)..(111/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_222 :
    (4358126 : ℝ) / 1000000000000000000 ≤
      ((222 : ℝ)/512)^2 *
        (∫ x in (111/256:ℝ)..(223/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_222).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((222 : ℝ)/512)^2 by positivity)
  have hn :
      (4358126 : ℝ) / 1000000000000000000 ≤
        ((222 : ℝ)/512)^2 *
          (46362172331/2000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((222 : ℝ)/512)^2 *
        (46362172331/2000000000000000000000 : ℝ) ≤
      ((222 : ℝ)/512)^2 *
        (∫ x in (111/256:ℝ)..(223/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_223 :
    (4551527 : ℝ) / 1000000000000000000 ≤
      ((223 : ℝ)/512)^2 *
        (∫ x in (223/512:ℝ)..(7/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_223).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((223 : ℝ)/512)^2 by positivity)
  have hn :
      (4551527 : ℝ) / 1000000000000000000 ≤
        ((223 : ℝ)/512)^2 *
          (599828948319/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((223 : ℝ)/512)^2 *
        (599828948319/25000000000000000000000 : ℝ) ≤
      ((223 : ℝ)/512)^2 *
        (∫ x in (223/512:ℝ)..(7/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
