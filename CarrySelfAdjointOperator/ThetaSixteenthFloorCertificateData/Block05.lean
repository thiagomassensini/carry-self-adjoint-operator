import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_05
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_160 :
    (110279 : ℝ) / 1000000000000000000 ≤
      ((160 : ℝ)/512)^2 *
        (∫ x in (((160 : ℝ)/512))..((((160+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_160).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((160 : ℝ)/512)^2 by positivity)
  have hn :
      (110279 : ℝ) / 1000000000000000000 ≤
        ((160 : ℝ)/512)^2 *
          (28231453187/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (5/16 : ℝ) = ((160 : ℝ)/512) := by
    norm_num
  have hright :
      (161/512 : ℝ) = (((( 160+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((160 : ℝ)/512)^2 *
        (28231453187/25000000000000000000000 : ℝ) ≤
      ((160 : ℝ)/512)^2 *
        (∫ x in (((160 : ℝ)/512))..((((160+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_161 :
    (119150 : ℝ) / 1000000000000000000 ≤
      ((161 : ℝ)/512)^2 *
        (∫ x in (((161 : ℝ)/512))..((((161+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_161).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((161 : ℝ)/512)^2 by positivity)
  have hn :
      (119150 : ℝ) / 1000000000000000000 ≤
        ((161 : ℝ)/512)^2 *
          (2409987881/2000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (161/512 : ℝ) = ((161 : ℝ)/512) := by
    norm_num
  have hright :
      (81/256 : ℝ) = (((( 161+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((161 : ℝ)/512)^2 *
        (2409987881/2000000000000000000000 : ℝ) ≤
      ((161 : ℝ)/512)^2 *
        (∫ x in (((161 : ℝ)/512))..((((161+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_162 :
    (128645 : ℝ) / 1000000000000000000 ≤
      ((162 : ℝ)/512)^2 *
        (∫ x in (((162 : ℝ)/512))..((((162+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_162).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((162 : ℝ)/512)^2 by positivity)
  have hn :
      (128645 : ℝ) / 1000000000000000000 ≤
        ((162 : ℝ)/512)^2 *
          (128500342939/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (81/256 : ℝ) = ((162 : ℝ)/512) := by
    norm_num
  have hright :
      (163/512 : ℝ) = (((( 162+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((162 : ℝ)/512)^2 *
        (128500342939/100000000000000000000000 : ℝ) ≤
      ((162 : ℝ)/512)^2 *
        (∫ x in (((162 : ℝ)/512))..((((162+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_163 :
    (138800 : ℝ) / 1000000000000000000 ≤
      ((163 : ℝ)/512)^2 *
        (∫ x in (((163 : ℝ)/512))..((((163+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_163).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((163 : ℝ)/512)^2 by positivity)
  have hn :
      (138800 : ℝ) / 1000000000000000000 ≤
        ((163 : ℝ)/512)^2 *
          (34236882419/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (163/512 : ℝ) = ((163 : ℝ)/512) := by
    norm_num
  have hright :
      (41/128 : ℝ) = (((( 163+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((163 : ℝ)/512)^2 *
        (34236882419/25000000000000000000000 : ℝ) ≤
      ((163 : ℝ)/512)^2 *
        (∫ x in (((163 : ℝ)/512))..((((163+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_164 :
    (149652 : ℝ) / 1000000000000000000 ≤
      ((164 : ℝ)/512)^2 *
        (∫ x in (((164 : ℝ)/512))..((((164+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_164).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((164 : ℝ)/512)^2 by positivity)
  have hn :
      (149652 : ℝ) / 1000000000000000000 ≤
        ((164 : ℝ)/512)^2 *
          (36465088607/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (41/128 : ℝ) = ((164 : ℝ)/512) := by
    norm_num
  have hright :
      (165/512 : ℝ) = (((( 164+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((164 : ℝ)/512)^2 *
        (36465088607/25000000000000000000000 : ℝ) ≤
      ((164 : ℝ)/512)^2 *
        (∫ x in (((164 : ℝ)/512))..((((164+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_165 :
    (161244 : ℝ) / 1000000000000000000 ≤
      ((165 : ℝ)/512)^2 *
        (∫ x in (((165 : ℝ)/512))..((((165+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_165).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((165 : ℝ)/512)^2 by positivity)
  have hn :
      (161244 : ℝ) / 1000000000000000000 ≤
        ((165 : ℝ)/512)^2 *
          (9703671631/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (165/512 : ℝ) = ((165 : ℝ)/512) := by
    norm_num
  have hright :
      (83/256 : ℝ) = (((( 165+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((165 : ℝ)/512)^2 *
        (9703671631/6250000000000000000000 : ℝ) ≤
      ((165 : ℝ)/512)^2 *
        (∫ x in (((165 : ℝ)/512))..((((165+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_166 :
    (173615 : ℝ) / 1000000000000000000 ≤
      ((166 : ℝ)/512)^2 *
        (∫ x in (((166 : ℝ)/512))..((((166+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_166).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((166 : ℝ)/512)^2 by positivity)
  have hn :
      (173615 : ℝ) / 1000000000000000000 ≤
        ((166 : ℝ)/512)^2 *
          (165163160149/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (83/256 : ℝ) = ((166 : ℝ)/512) := by
    norm_num
  have hright :
      (167/512 : ℝ) = (((( 166+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((166 : ℝ)/512)^2 *
        (165163160149/100000000000000000000000 : ℝ) ≤
      ((166 : ℝ)/512)^2 *
        (∫ x in (((166 : ℝ)/512))..((((166+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_167 :
    (186811 : ℝ) / 1000000000000000000 ≤
      ((167 : ℝ)/512)^2 *
        (∫ x in (((167 : ℝ)/512))..((((167+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_167).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((167 : ℝ)/512)^2 by positivity)
  have hn :
      (186811 : ℝ) / 1000000000000000000 ≤
        ((167 : ℝ)/512)^2 *
          (5487330483/3125000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (167/512 : ℝ) = ((167 : ℝ)/512) := by
    norm_num
  have hright :
      (21/64 : ℝ) = (((( 167+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((167 : ℝ)/512)^2 *
        (5487330483/3125000000000000000000 : ℝ) ≤
      ((167 : ℝ)/512)^2 *
        (∫ x in (((167 : ℝ)/512))..((((167+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_168 :
    (200877 : ℝ) / 1000000000000000000 ≤
      ((168 : ℝ)/512)^2 *
        (∫ x in (((168 : ℝ)/512))..((((168+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_168).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((168 : ℝ)/512)^2 by positivity)
  have hn :
      (200877 : ℝ) / 1000000000000000000 ≤
        ((168 : ℝ)/512)^2 *
          (93287245023/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (21/64 : ℝ) = ((168 : ℝ)/512) := by
    norm_num
  have hright :
      (169/512 : ℝ) = (((( 168+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((168 : ℝ)/512)^2 *
        (93287245023/50000000000000000000000 : ℝ) ≤
      ((168 : ℝ)/512)^2 *
        (∫ x in (((168 : ℝ)/512))..((((168+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_169 :
    (215860 : ℝ) / 1000000000000000000 ≤
      ((169 : ℝ)/512)^2 *
        (∫ x in (((169 : ℝ)/512))..((((169+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_169).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((169 : ℝ)/512)^2 by positivity)
  have hn :
      (215860 : ℝ) / 1000000000000000000 ≤
        ((169 : ℝ)/512)^2 *
          (99062457891/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (169/512 : ℝ) = ((169 : ℝ)/512) := by
    norm_num
  have hright :
      (85/256 : ℝ) = (((( 169+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((169 : ℝ)/512)^2 *
        (99062457891/50000000000000000000000 : ℝ) ≤
      ((169 : ℝ)/512)^2 *
        (∫ x in (((169 : ℝ)/512))..((((169+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_170 :
    (231809 : ℝ) / 1000000000000000000 ≤
      ((170 : ℝ)/512)^2 *
        (∫ x in (((170 : ℝ)/512))..((((170+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_170).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((170 : ℝ)/512)^2 by positivity)
  have hn :
      (231809 : ℝ) / 1000000000000000000 ≤
        ((170 : ℝ)/512)^2 *
          (105134185951/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (85/256 : ℝ) = ((170 : ℝ)/512) := by
    norm_num
  have hright :
      (171/512 : ℝ) = (((( 170+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((170 : ℝ)/512)^2 *
        (105134185951/50000000000000000000000 : ℝ) ≤
      ((170 : ℝ)/512)^2 *
        (∫ x in (((170 : ℝ)/512))..((((170+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_171 :
    (248777 : ℝ) / 1000000000000000000 ≤
      ((171 : ℝ)/512)^2 *
        (∫ x in (((171 : ℝ)/512))..((((171+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_171).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((171 : ℝ)/512)^2 by positivity)
  have hn :
      (248777 : ℝ) / 1000000000000000000 ≤
        ((171 : ℝ)/512)^2 *
          (44605575479/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (171/512 : ℝ) = ((171 : ℝ)/512) := by
    norm_num
  have hright :
      (43/128 : ℝ) = (((( 171+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((171 : ℝ)/512)^2 *
        (44605575479/20000000000000000000000 : ℝ) ≤
      ((171 : ℝ)/512)^2 *
        (∫ x in (((171 : ℝ)/512))..((((171+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_172 :
    (266817 : ℝ) / 1000000000000000000 ≤
      ((172 : ℝ)/512)^2 *
        (∫ x in (((172 : ℝ)/512))..((((172+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_172).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((172 : ℝ)/512)^2 by positivity)
  have hn :
      (266817 : ℝ) / 1000000000000000000 ≤
        ((172 : ℝ)/512)^2 *
          (118213471091/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (43/128 : ℝ) = ((172 : ℝ)/512) := by
    norm_num
  have hright :
      (173/512 : ℝ) = (((( 172+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((172 : ℝ)/512)^2 *
        (118213471091/50000000000000000000000 : ℝ) ≤
      ((172 : ℝ)/512)^2 *
        (∫ x in (((172 : ℝ)/512))..((((172+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_173 :
    (285984 : ℝ) / 1000000000000000000 ≤
      ((173 : ℝ)/512)^2 *
        (∫ x in (((173 : ℝ)/512))..((((173+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_173).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((173 : ℝ)/512)^2 by positivity)
  have hn :
      (285984 : ℝ) / 1000000000000000000 ≤
        ((173 : ℝ)/512)^2 *
          (250489557063/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (173/512 : ℝ) = ((173 : ℝ)/512) := by
    norm_num
  have hright :
      (87/256 : ℝ) = (((( 173+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((173 : ℝ)/512)^2 *
        (250489557063/100000000000000000000000 : ℝ) ≤
      ((173 : ℝ)/512)^2 *
        (∫ x in (((173 : ℝ)/512))..((((173+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_174 :
    (306335 : ℝ) / 1000000000000000000 ≤
      ((174 : ℝ)/512)^2 *
        (∫ x in (((174 : ℝ)/512))..((((174+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_174).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((174 : ℝ)/512)^2 by positivity)
  have hn :
      (306335 : ℝ) / 1000000000000000000 ≤
        ((174 : ℝ)/512)^2 *
          (265240182399/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (87/256 : ℝ) = ((174 : ℝ)/512) := by
    norm_num
  have hright :
      (175/512 : ℝ) = (((( 174+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((174 : ℝ)/512)^2 *
        (265240182399/100000000000000000000000 : ℝ) ≤
      ((174 : ℝ)/512)^2 *
        (∫ x in (((174 : ℝ)/512))..((((174+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_175 :
    (327932 : ℝ) / 1000000000000000000 ≤
      ((175 : ℝ)/512)^2 *
        (∫ x in (((175 : ℝ)/512))..((((175+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_175).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((175 : ℝ)/512)^2 by positivity)
  have hn :
      (327932 : ℝ) / 1000000000000000000 ≤
        ((175 : ℝ)/512)^2 *
          (140351867759/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (175/512 : ℝ) = ((175 : ℝ)/512) := by
    norm_num
  have hright :
      (11/32 : ℝ) = (((( 175+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((175 : ℝ)/512)^2 *
        (140351867759/50000000000000000000000 : ℝ) ≤
      ((175 : ℝ)/512)^2 *
        (∫ x in (((175 : ℝ)/512))..((((175+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_176 :
    (350835 : ℝ) / 1000000000000000000 ≤
      ((176 : ℝ)/512)^2 *
        (∫ x in (((176 : ℝ)/512))..((((176+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_176).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((176 : ℝ)/512)^2 by positivity)
  have hn :
      (350835 : ℝ) / 1000000000000000000 ≤
        ((176 : ℝ)/512)^2 *
          (148452788393/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (11/32 : ℝ) = ((176 : ℝ)/512) := by
    norm_num
  have hright :
      (177/512 : ℝ) = (((( 176+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((176 : ℝ)/512)^2 *
        (148452788393/50000000000000000000000 : ℝ) ≤
      ((176 : ℝ)/512)^2 *
        (∫ x in (((176 : ℝ)/512))..((((176+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_177 :
    (375109 : ℝ) / 1000000000000000000 ≤
      ((177 : ℝ)/512)^2 *
        (∫ x in (((177 : ℝ)/512))..((((177+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_177).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((177 : ℝ)/512)^2 by positivity)
  have hn :
      (375109 : ℝ) / 1000000000000000000 ≤
        ((177 : ℝ)/512)^2 *
          (156935747173/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (177/512 : ℝ) = ((177 : ℝ)/512) := by
    norm_num
  have hright :
      (89/256 : ℝ) = (((( 177+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((177 : ℝ)/512)^2 *
        (156935747173/50000000000000000000000 : ℝ) ≤
      ((177 : ℝ)/512)^2 *
        (∫ x in (((177 : ℝ)/512))..((((177+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_178 :
    (400821 : ℝ) / 1000000000000000000 ≤
      ((178 : ℝ)/512)^2 *
        (∫ x in (((178 : ℝ)/512))..((((178+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_178).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((178 : ℝ)/512)^2 by positivity)
  have hn :
      (400821 : ℝ) / 1000000000000000000 ≤
        ((178 : ℝ)/512)^2 *
          (82906921873/25000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (89/256 : ℝ) = ((178 : ℝ)/512) := by
    norm_num
  have hright :
      (179/512 : ℝ) = (((( 178+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((178 : ℝ)/512)^2 *
        (82906921873/25000000000000000000000 : ℝ) ≤
      ((178 : ℝ)/512)^2 *
        (∫ x in (((178 : ℝ)/512))..((((178+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_179 :
    (428038 : ℝ) / 1000000000000000000 ≤
      ((179 : ℝ)/512)^2 *
        (∫ x in (((179 : ℝ)/512))..((((179+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_179).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((179 : ℝ)/512)^2 by positivity)
  have hn :
      (428038 : ℝ) / 1000000000000000000 ≤
        ((179 : ℝ)/512)^2 *
          (43775093581/12500000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (179/512 : ℝ) = ((179 : ℝ)/512) := by
    norm_num
  have hright :
      (45/128 : ℝ) = (((( 179+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((179 : ℝ)/512)^2 *
        (43775093581/12500000000000000000000 : ℝ) ≤
      ((179 : ℝ)/512)^2 *
        (∫ x in (((179 : ℝ)/512))..((((179+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_180 :
    (456833 : ℝ) / 1000000000000000000 ≤
      ((180 : ℝ)/512)^2 *
        (∫ x in (((180 : ℝ)/512))..((((180+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_180).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((180 : ℝ)/512)^2 by positivity)
  have hn :
      (456833 : ℝ) / 1000000000000000000 ≤
        ((180 : ℝ)/512)^2 *
          (369617643947/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (45/128 : ℝ) = ((180 : ℝ)/512) := by
    norm_num
  have hright :
      (181/512 : ℝ) = (((( 180+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((180 : ℝ)/512)^2 *
        (369617643947/100000000000000000000000 : ℝ) ≤
      ((180 : ℝ)/512)^2 *
        (∫ x in (((180 : ℝ)/512))..((((180+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_181 :
    (487277 : ℝ) / 1000000000000000000 ≤
      ((181 : ℝ)/512)^2 *
        (∫ x in (((181 : ℝ)/512))..((((181+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_181).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((181 : ℝ)/512)^2 by positivity)
  have hn :
      (487277 : ℝ) / 1000000000000000000 ≤
        ((181 : ℝ)/512)^2 *
          (77981138477/20000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (181/512 : ℝ) = ((181 : ℝ)/512) := by
    norm_num
  have hright :
      (91/256 : ℝ) = (((( 181+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((181 : ℝ)/512)^2 *
        (77981138477/20000000000000000000000 : ℝ) ≤
      ((181 : ℝ)/512)^2 *
        (∫ x in (((181 : ℝ)/512))..((((181+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_182 :
    (519448 : ℝ) / 1000000000000000000 ≤
      ((182 : ℝ)/512)^2 *
        (∫ x in (((182 : ℝ)/512))..((((182+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_182).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((182 : ℝ)/512)^2 by positivity)
  have hn :
      (519448 : ℝ) / 1000000000000000000 ≤
        ((182 : ℝ)/512)^2 *
          (411092543541/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (91/256 : ℝ) = ((182 : ℝ)/512) := by
    norm_num
  have hright :
      (183/512 : ℝ) = (((( 182+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((182 : ℝ)/512)^2 *
        (411092543541/100000000000000000000000 : ℝ) ≤
      ((182 : ℝ)/512)^2 *
        (∫ x in (((182 : ℝ)/512))..((((182+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_183 :
    (553422 : ℝ) / 1000000000000000000 ≤
      ((183 : ℝ)/512)^2 *
        (∫ x in (((183 : ℝ)/512))..((((183+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_183).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((183 : ℝ)/512)^2 by positivity)
  have hn :
      (553422 : ℝ) / 1000000000000000000 ≤
        ((183 : ℝ)/512)^2 *
          (433206153847/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (183/512 : ℝ) = ((183 : ℝ)/512) := by
    norm_num
  have hright :
      (23/64 : ℝ) = (((( 183+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((183 : ℝ)/512)^2 *
        (433206153847/100000000000000000000000 : ℝ) ≤
      ((183 : ℝ)/512)^2 *
        (∫ x in (((183 : ℝ)/512))..((((183+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_184 :
    (589280 : ℝ) / 1000000000000000000 ≤
      ((184 : ℝ)/512)^2 *
        (∫ x in (((184 : ℝ)/512))..((((184+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_184).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((184 : ℝ)/512)^2 by positivity)
  have hn :
      (589280 : ℝ) / 1000000000000000000 ≤
        ((184 : ℝ)/512)^2 *
          (228137380699/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (23/64 : ℝ) = ((184 : ℝ)/512) := by
    norm_num
  have hright :
      (185/512 : ℝ) = (((( 184+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((184 : ℝ)/512)^2 *
        (228137380699/50000000000000000000000 : ℝ) ≤
      ((184 : ℝ)/512)^2 *
        (∫ x in (((184 : ℝ)/512))..((((184+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_185 :
    (627105 : ℝ) / 1000000000000000000 ≤
      ((185 : ℝ)/512)^2 *
        (∫ x in (((185 : ℝ)/512))..((((185+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_185).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((185 : ℝ)/512)^2 by positivity)
  have hn :
      (627105 : ℝ) / 1000000000000000000 ≤
        ((185 : ℝ)/512)^2 *
          (30020428707/6250000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (185/512 : ℝ) = ((185 : ℝ)/512) := by
    norm_num
  have hright :
      (93/256 : ℝ) = (((( 185+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((185 : ℝ)/512)^2 *
        (30020428707/6250000000000000000000 : ℝ) ≤
      ((185 : ℝ)/512)^2 *
        (∫ x in (((185 : ℝ)/512))..((((185+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_186 :
    (666981 : ℝ) / 1000000000000000000 ≤
      ((186 : ℝ)/512)^2 *
        (∫ x in (((186 : ℝ)/512))..((((186+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_186).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((186 : ℝ)/512)^2 by positivity)
  have hn :
      (666981 : ℝ) / 1000000000000000000 ≤
        ((186 : ℝ)/512)^2 *
          (252695583803/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (93/256 : ℝ) = ((186 : ℝ)/512) := by
    norm_num
  have hright :
      (187/512 : ℝ) = (((( 186+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((186 : ℝ)/512)^2 *
        (252695583803/50000000000000000000000 : ℝ) ≤
      ((186 : ℝ)/512)^2 *
        (∫ x in (((186 : ℝ)/512))..((((186+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_187 :
    (708995 : ℝ) / 1000000000000000000 ≤
      ((187 : ℝ)/512)^2 *
        (∫ x in (((187 : ℝ)/512))..((((187+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_187).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((187 : ℝ)/512)^2 by positivity)
  have hn :
      (708995 : ℝ) / 1000000000000000000 ≤
        ((187 : ℝ)/512)^2 *
          (531496603627/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (187/512 : ℝ) = ((187 : ℝ)/512) := by
    norm_num
  have hright :
      (47/128 : ℝ) = (((( 187+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((187 : ℝ)/512)^2 *
        (531496603627/100000000000000000000000 : ℝ) ≤
      ((187 : ℝ)/512)^2 *
        (∫ x in (((187 : ℝ)/512))..((((187+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_188 :
    (753239 : ℝ) / 1000000000000000000 ≤
      ((188 : ℝ)/512)^2 *
        (∫ x in (((188 : ℝ)/512))..((((188+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_188).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((188 : ℝ)/512)^2 by positivity)
  have hn :
      (753239 : ℝ) / 1000000000000000000 ≤
        ((188 : ℝ)/512)^2 *
          (4364626961/781250000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (47/128 : ℝ) = ((188 : ℝ)/512) := by
    norm_num
  have hright :
      (189/512 : ℝ) = (((( 188+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((188 : ℝ)/512)^2 *
        (4364626961/781250000000000000000 : ℝ) ≤
      ((188 : ℝ)/512)^2 *
        (∫ x in (((188 : ℝ)/512))..((((188+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_189 :
    (799802 : ℝ) / 1000000000000000000 ≤
      ((189 : ℝ)/512)^2 *
        (∫ x in (((189 : ℝ)/512))..((((189+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_189).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((189 : ℝ)/512)^2 by positivity)
  have hn :
      (799802 : ℝ) / 1000000000000000000 ≤
        ((189 : ℝ)/512)^2 *
          (23477893087/4000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (189/512 : ℝ) = ((189 : ℝ)/512) := by
    norm_num
  have hright :
      (95/256 : ℝ) = (((( 189+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((189 : ℝ)/512)^2 *
        (23477893087/4000000000000000000000 : ℝ) ≤
      ((189 : ℝ)/512)^2 *
        (∫ x in (((189 : ℝ)/512))..((((189+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_190 :
    (848780 : ℝ) / 1000000000000000000 ≤
      ((190 : ℝ)/512)^2 *
        (∫ x in (((190 : ℝ)/512))..((((190+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_190).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((190 : ℝ)/512)^2 by positivity)
  have hn :
      (848780 : ℝ) / 1000000000000000000 ≤
        ((190 : ℝ)/512)^2 *
          (616351149409/100000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (95/256 : ℝ) = ((190 : ℝ)/512) := by
    norm_num
  have hright :
      (191/512 : ℝ) = (((( 190+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((190 : ℝ)/512)^2 *
        (616351149409/100000000000000000000000 : ℝ) ≤
      ((190 : ℝ)/512)^2 *
        (∫ x in (((190 : ℝ)/512))..((((190+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

theorem theta16_floor_cell_191 :
    (900269 : ℝ) / 1000000000000000000 ≤
      ((191 : ℝ)/512)^2 *
        (∫ x in (((191 : ℝ)/512))..((((191+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_191).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((191 : ℝ)/512)^2 by positivity)
  have hn :
      (900269 : ℝ) / 1000000000000000000 ≤
        ((191 : ℝ)/512)^2 *
          (323456549737/50000000000000000000000 : ℝ) := by
    norm_num
  have hleft :
      (191/512 : ℝ) = ((191 : ℝ)/512) := by
    norm_num
  have hright :
      (3/8 : ℝ) = (((( 191+1 : ℕ) : ℝ)/512)) := by
    norm_num
  have ht :
      ((191 : ℝ)/512)^2 *
        (323456549737/50000000000000000000000 : ℝ) ≤
      ((191 : ℝ)/512)^2 *
        (∫ x in (((191 : ℝ)/512))..((((191+1 : ℕ) : ℝ)/512)), x^14*thetaFirstMode x) := by
    simpa [hleft, hright] using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
