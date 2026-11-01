import CarrySelfAdjointOperator.ThetaFourteenthSourceCertificateData.Cells14_08
import Mathlib.Tactic

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem theta16_floor_cell_256 :
    (15132889 : ℝ) / 1000000000000000000 ≤
      ((256 : ℝ)/512)^2 *
        (∫ x in (1/2:ℝ)..(257/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_256).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((256 : ℝ)/512)^2 by positivity)
  have hn :
      (15132889 : ℝ) / 1000000000000000000 ≤
        ((256 : ℝ)/512)^2 *
          (3026577856901/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((256 : ℝ)/512)^2 *
        (3026577856901/50000000000000000000000 : ℝ) ≤
      ((256 : ℝ)/512)^2 *
        (∫ x in (1/2:ℝ)..(257/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_257 :
    (15589998 : ℝ) / 1000000000000000000 ≤
      ((257 : ℝ)/512)^2 *
        (∫ x in (257/512:ℝ)..(129/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_257).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((257 : ℝ)/512)^2 by positivity)
  have hn :
      (15589998 : ℝ) / 1000000000000000000 ≤
        ((257 : ℝ)/512)^2 *
          (6187564678729/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((257 : ℝ)/512)^2 *
        (6187564678729/100000000000000000000000 : ℝ) ≤
      ((257 : ℝ)/512)^2 *
        (∫ x in (257/512:ℝ)..(129/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_258 :
    (16054934 : ℝ) / 1000000000000000000 ≤
      ((258 : ℝ)/512)^2 *
        (∫ x in (129/256:ℝ)..(259/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_258).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((258 : ℝ)/512)^2 by positivity)
  have hn :
      (16054934 : ℝ) / 1000000000000000000 ≤
        ((258 : ℝ)/512)^2 *
          (790349263541/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((258 : ℝ)/512)^2 *
        (790349263541/12500000000000000000000 : ℝ) ≤
      ((258 : ℝ)/512)^2 *
        (∫ x in (129/256:ℝ)..(259/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_259 :
    (16527600 : ℝ) / 1000000000000000000 ≤
      ((259 : ℝ)/512)^2 *
        (∫ x in (259/512:ℝ)..(65/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_259).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((259 : ℝ)/512)^2 by positivity)
  have hn :
      (16527600 : ℝ) / 1000000000000000000 ≤
        ((259 : ℝ)/512)^2 *
          (6458775602989/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((259 : ℝ)/512)^2 *
        (6458775602989/100000000000000000000000 : ℝ) ≤
      ((259 : ℝ)/512)^2 *
        (∫ x in (259/512:ℝ)..(65/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_260 :
    (17007891 : ℝ) / 1000000000000000000 ≤
      ((260 : ℝ)/512)^2 *
        (∫ x in (65/128:ℝ)..(261/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_260).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((260 : ℝ)/512)^2 by positivity)
  have hn :
      (17007891 : ℝ) / 1000000000000000000 ≤
        ((260 : ℝ)/512)^2 *
          (1648859706133/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((260 : ℝ)/512)^2 *
        (1648859706133/25000000000000000000000 : ℝ) ≤
      ((260 : ℝ)/512)^2 *
        (∫ x in (65/128:ℝ)..(261/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_261 :
    (17495691 : ℝ) / 1000000000000000000 ≤
      ((261 : ℝ)/512)^2 *
        (∫ x in (261/512:ℝ)..(131/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_261).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((261 : ℝ)/512)^2 by positivity)
  have hn :
      (17495691 : ℝ) / 1000000000000000000 ≤
        ((261 : ℝ)/512)^2 *
          (3366355773277/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((261 : ℝ)/512)^2 *
        (3366355773277/50000000000000000000000 : ℝ) ≤
      ((261 : ℝ)/512)^2 *
        (∫ x in (261/512:ℝ)..(131/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_262 :
    (17990873 : ℝ) / 1000000000000000000 ≤
      ((262 : ℝ)/512)^2 *
        (∫ x in (131/256:ℝ)..(263/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_262).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((262 : ℝ)/512)^2 by positivity)
  have hn :
      (17990873 : ℝ) / 1000000000000000000 ≤
        ((262 : ℝ)/512)^2 *
          (6870519708311/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((262 : ℝ)/512)^2 *
        (6870519708311/100000000000000000000000 : ℝ) ≤
      ((262 : ℝ)/512)^2 *
        (∫ x in (131/256:ℝ)..(263/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_263 :
    (18493302 : ℝ) / 1000000000000000000 ≤
      ((263 : ℝ)/512)^2 *
        (∫ x in (263/512:ℝ)..(33/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_263).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((263 : ℝ)/512)^2 by positivity)
  have hn :
      (18493302 : ℝ) / 1000000000000000000 ≤
        ((263 : ℝ)/512)^2 *
          (3504393736059/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((263 : ℝ)/512)^2 *
        (3504393736059/50000000000000000000000 : ℝ) ≤
      ((263 : ℝ)/512)^2 *
        (∫ x in (263/512:ℝ)..(33/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_264 :
    (19002830 : ℝ) / 1000000000000000000 ≤
      ((264 : ℝ)/512)^2 *
        (∫ x in (33/64:ℝ)..(265/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_264).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((264 : ℝ)/512)^2 by positivity)
  have hn :
      (19002830 : ℝ) / 1000000000000000000 ≤
        ((264 : ℝ)/512)^2 *
          (7147437284223/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((264 : ℝ)/512)^2 *
        (7147437284223/100000000000000000000000 : ℝ) ≤
      ((264 : ℝ)/512)^2 *
        (∫ x in (33/64:ℝ)..(265/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_265 :
    (19519299 : ℝ) / 1000000000000000000 ≤
      ((265 : ℝ)/512)^2 *
        (∫ x in (265/512:ℝ)..(133/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_265).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((265 : ℝ)/512)^2 by positivity)
  have hn :
      (19519299 : ℝ) / 1000000000000000000 ≤
        ((265 : ℝ)/512)^2 *
          (7286389939077/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((265 : ℝ)/512)^2 *
        (7286389939077/100000000000000000000000 : ℝ) ≤
      ((265 : ℝ)/512)^2 *
        (∫ x in (265/512:ℝ)..(133/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_266 :
    (20042543 : ℝ) / 1000000000000000000 ≤
      ((266 : ℝ)/512)^2 *
        (∫ x in (133/256:ℝ)..(267/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_266).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((266 : ℝ)/512)^2 by positivity)
  have hn :
      (20042543 : ℝ) / 1000000000000000000 ≤
        ((266 : ℝ)/512)^2 *
          (7425564646977/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((266 : ℝ)/512)^2 *
        (7425564646977/100000000000000000000000 : ℝ) ≤
      ((266 : ℝ)/512)^2 *
        (∫ x in (133/256:ℝ)..(267/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_267 :
    (20572382 : ℝ) / 1000000000000000000 ≤
      ((267 : ℝ)/512)^2 *
        (∫ x in (267/512:ℝ)..(67/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_267).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((267 : ℝ)/512)^2 by positivity)
  have hn :
      (20572382 : ℝ) / 1000000000000000000 ≤
        ((267 : ℝ)/512)^2 *
          (7564879104989/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((267 : ℝ)/512)^2 *
        (7564879104989/100000000000000000000000 : ℝ) ≤
      ((267 : ℝ)/512)^2 *
        (∫ x in (267/512:ℝ)..(67/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_268 :
    (21108628 : ℝ) / 1000000000000000000 ≤
      ((268 : ℝ)/512)^2 *
        (∫ x in (67/128:ℝ)..(269/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_268).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((268 : ℝ)/512)^2 by positivity)
  have hn :
      (21108628 : ℝ) / 1000000000000000000 ≤
        ((268 : ℝ)/512)^2 *
          (3852124785541/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((268 : ℝ)/512)^2 *
        (3852124785541/50000000000000000000000 : ℝ) ≤
      ((268 : ℝ)/512)^2 *
        (∫ x in (67/128:ℝ)..(269/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_269 :
    (21651080 : ℝ) / 1000000000000000000 ≤
      ((269 : ℝ)/512)^2 *
        (∫ x in (269/512:ℝ)..(135/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_269).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((269 : ℝ)/512)^2 by positivity)
  have hn :
      (21651080 : ℝ) / 1000000000000000000 ≤
        ((269 : ℝ)/512)^2 *
          (3921795470703/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((269 : ℝ)/512)^2 *
        (3921795470703/50000000000000000000000 : ℝ) ≤
      ((269 : ℝ)/512)^2 *
        (∫ x in (269/512:ℝ)..(135/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_270 :
    (22199529 : ℝ) / 1000000000000000000 ≤
      ((270 : ℝ)/512)^2 *
        (∫ x in (135/256:ℝ)..(271/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_270).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((270 : ℝ)/512)^2 by positivity)
  have hn :
      (22199529 : ℝ) / 1000000000000000000 ≤
        ((270 : ℝ)/512)^2 *
          (498926051913/6250000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((270 : ℝ)/512)^2 *
        (498926051913/6250000000000000000000 : ℝ) ≤
      ((270 : ℝ)/512)^2 *
        (∫ x in (135/256:ℝ)..(271/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_271 :
    (22753754 : ℝ) / 1000000000000000000 ≤
      ((271 : ℝ)/512)^2 *
        (∫ x in (271/512:ℝ)..(17/32:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_271).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((271 : ℝ)/512)^2 by positivity)
  have hn :
      (22753754 : ℝ) / 1000000000000000000 ≤
        ((271 : ℝ)/512)^2 *
          (8121839655099/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((271 : ℝ)/512)^2 *
        (8121839655099/100000000000000000000000 : ℝ) ≤
      ((271 : ℝ)/512)^2 *
        (∫ x in (271/512:ℝ)..(17/32:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_272 :
    (23313524 : ℝ) / 1000000000000000000 ≤
      ((272 : ℝ)/512)^2 *
        (∫ x in (17/32:ℝ)..(273/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_272).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((272 : ℝ)/512)^2 by positivity)
  have hn :
      (23313524 : ℝ) / 1000000000000000000 ≤
        ((272 : ℝ)/512)^2 *
          (1032571339897/12500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((272 : ℝ)/512)^2 *
        (1032571339897/12500000000000000000000 : ℝ) ≤
      ((272 : ℝ)/512)^2 *
        (∫ x in (17/32:ℝ)..(273/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_273 :
    (23878598 : ℝ) / 1000000000000000000 ≤
      ((273 : ℝ)/512)^2 *
        (∫ x in (273/512:ℝ)..(137/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_273).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((273 : ℝ)/512)^2 by positivity)
  have hn :
      (23878598 : ℝ) / 1000000000000000000 ≤
        ((273 : ℝ)/512)^2 *
          (67191362431/800000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((273 : ℝ)/512)^2 *
        (67191362431/800000000000000000000 : ℝ) ≤
      ((273 : ℝ)/512)^2 *
        (∫ x in (273/512:ℝ)..(137/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_274 :
    (24448723 : ℝ) / 1000000000000000000 ≤
      ((274 : ℝ)/512)^2 *
        (∫ x in (137/256:ℝ)..(275/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_274).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((274 : ℝ)/512)^2 by positivity)
  have hn :
      (24448723 : ℝ) / 1000000000000000000 ≤
        ((274 : ℝ)/512)^2 *
          (426839887923/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((274 : ℝ)/512)^2 *
        (426839887923/5000000000000000000000 : ℝ) ≤
      ((274 : ℝ)/512)^2 *
        (∫ x in (137/256:ℝ)..(275/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_275 :
    (25023639 : ℝ) / 1000000000000000000 ≤
      ((275 : ℝ)/512)^2 *
        (∫ x in (275/512:ℝ)..(69/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_275).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((275 : ℝ)/512)^2 by positivity)
  have hn :
      (25023639 : ℝ) / 1000000000000000000 ≤
        ((275 : ℝ)/512)^2 *
          (1734822318881/20000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((275 : ℝ)/512)^2 *
        (1734822318881/20000000000000000000000 : ℝ) ≤
      ((275 : ℝ)/512)^2 *
        (∫ x in (275/512:ℝ)..(69/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_276 :
    (25603072 : ℝ) / 1000000000000000000 ≤
      ((276 : ℝ)/512)^2 *
        (∫ x in (69/128:ℝ)..(277/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_276).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((276 : ℝ)/512)^2 by positivity)
  have hn :
      (25603072 : ℝ) / 1000000000000000000 ≤
        ((276 : ℝ)/512)^2 *
          (4405384790881/50000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((276 : ℝ)/512)^2 *
        (4405384790881/50000000000000000000000 : ℝ) ≤
      ((276 : ℝ)/512)^2 *
        (∫ x in (69/128:ℝ)..(277/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_277 :
    (26186741 : ℝ) / 1000000000000000000 ≤
      ((277 : ℝ)/512)^2 *
        (∫ x in (277/512:ℝ)..(139/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_277).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((277 : ℝ)/512)^2 by positivity)
  have hn :
      (26186741 : ℝ) / 1000000000000000000 ≤
        ((277 : ℝ)/512)^2 *
          (2236669711941/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((277 : ℝ)/512)^2 *
        (2236669711941/25000000000000000000000 : ℝ) ≤
      ((277 : ℝ)/512)^2 *
        (∫ x in (277/512:ℝ)..(139/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_278 :
    (26774355 : ℝ) / 1000000000000000000 ≤
      ((278 : ℝ)/512)^2 *
        (∫ x in (139/256:ℝ)..(279/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_278).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((278 : ℝ)/512)^2 by positivity)
  have hn :
      (26774355 : ℝ) / 1000000000000000000 ≤
        ((278 : ℝ)/512)^2 *
          (9081745977537/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((278 : ℝ)/512)^2 *
        (9081745977537/100000000000000000000000 : ℝ) ≤
      ((278 : ℝ)/512)^2 *
        (∫ x in (139/256:ℝ)..(279/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_279 :
    (27365611 : ℝ) / 1000000000000000000 ≤
      ((279 : ℝ)/512)^2 *
        (∫ x in (279/512:ℝ)..(35/64:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_279).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((279 : ℝ)/512)^2 by positivity)
  have hn :
      (27365611 : ℝ) / 1000000000000000000 ≤
        ((279 : ℝ)/512)^2 *
          (2303969279191/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((279 : ℝ)/512)^2 *
        (2303969279191/25000000000000000000000 : ℝ) ≤
      ((279 : ℝ)/512)^2 *
        (∫ x in (279/512:ℝ)..(35/64:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_280 :
    (27960200 : ℝ) / 1000000000000000000 ≤
      ((280 : ℝ)/512)^2 *
        (∫ x in (35/64:ℝ)..(281/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_280).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((280 : ℝ)/512)^2 by positivity)
  have hn :
      (27960200 : ℝ) / 1000000000000000000 ≤
        ((280 : ℝ)/512)^2 *
          (3651944561/39062500000000000000 : ℝ) := by
    norm_num
  have ht :
      ((280 : ℝ)/512)^2 *
        (3651944561/39062500000000000000 : ℝ) ≤
      ((280 : ℝ)/512)^2 *
        (∫ x in (35/64:ℝ)..(281/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_281 :
    (28557801 : ℝ) / 1000000000000000000 ≤
      ((281 : ℝ)/512)^2 *
        (∫ x in (281/512:ℝ)..(141/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_281).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((281 : ℝ)/512)^2 by positivity)
  have hn :
      (28557801 : ℝ) / 1000000000000000000 ≤
        ((281 : ℝ)/512)^2 *
          (2370238609401/25000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((281 : ℝ)/512)^2 *
        (2370238609401/25000000000000000000000 : ℝ) ≤
      ((281 : ℝ)/512)^2 *
        (∫ x in (281/512:ℝ)..(141/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_282 :
    (29158087 : ℝ) / 1000000000000000000 ≤
      ((282 : ℝ)/512)^2 *
        (∫ x in (141/256:ℝ)..(283/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_282).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((282 : ℝ)/512)^2 by positivity)
  have hn :
      (29158087 : ℝ) / 1000000000000000000 ≤
        ((282 : ℝ)/512)^2 *
          (9611711661749/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((282 : ℝ)/512)^2 *
        (9611711661749/100000000000000000000000 : ℝ) ≤
      ((282 : ℝ)/512)^2 *
        (∫ x in (141/256:ℝ)..(283/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_283 :
    (29760718 : ℝ) / 1000000000000000000 ≤
      ((283 : ℝ)/512)^2 *
        (∫ x in (283/512:ℝ)..(71/128:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_283).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((283 : ℝ)/512)^2 by positivity)
  have hn :
      (29760718 : ℝ) / 1000000000000000000 ≤
        ((283 : ℝ)/512)^2 *
          (487057759849/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((283 : ℝ)/512)^2 *
        (487057759849/5000000000000000000000 : ℝ) ≤
      ((283 : ℝ)/512)^2 *
        (∫ x in (283/512:ℝ)..(71/128:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_284 :
    (30365350 : ℝ) / 1000000000000000000 ≤
      ((284 : ℝ)/512)^2 *
        (∫ x in (71/128:ℝ)..(285/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_284).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((284 : ℝ)/512)^2 by positivity)
  have hn :
      (30365350 : ℝ) / 1000000000000000000 ≤
        ((284 : ℝ)/512)^2 *
          (9869190589513/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((284 : ℝ)/512)^2 *
        (9869190589513/100000000000000000000000 : ℝ) ≤
      ((284 : ℝ)/512)^2 *
        (∫ x in (71/128:ℝ)..(285/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_285 :
    (30971628 : ℝ) / 1000000000000000000 ≤
      ((285 : ℝ)/512)^2 *
        (∫ x in (285/512:ℝ)..(143/256:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_285).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((285 : ℝ)/512)^2 by positivity)
  have hn :
      (30971628 : ℝ) / 1000000000000000000 ≤
        ((285 : ℝ)/512)^2 *
          (9995723594489/100000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((285 : ℝ)/512)^2 *
        (9995723594489/100000000000000000000000 : ℝ) ≤
      ((285 : ℝ)/512)^2 *
        (∫ x in (285/512:ℝ)..(143/256:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_286 :
    (31579190 : ℝ) / 1000000000000000000 ≤
      ((286 : ℝ)/512)^2 *
        (∫ x in (143/256:ℝ)..(287/512:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_286).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((286 : ℝ)/512)^2 by positivity)
  have hn :
      (31579190 : ℝ) / 1000000000000000000 ≤
        ((286 : ℝ)/512)^2 *
          (253016507197/2500000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((286 : ℝ)/512)^2 *
        (253016507197/2500000000000000000000 : ℝ) ≤
      ((286 : ℝ)/512)^2 *
        (∫ x in (143/256:ℝ)..(287/512:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

theorem theta16_floor_cell_287 :
    (32187667 : ℝ) / 1000000000000000000 ≤
      ((287 : ℝ)/512)^2 *
        (∫ x in (287/512:ℝ)..(9/16:ℝ), x^14*thetaFirstMode x) := by
  have h := (thetaFourteenth_cell_bounds_14_287).1
  have hs := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ ((287 : ℝ)/512)^2 by positivity)
  have hn :
      (32187667 : ℝ) / 1000000000000000000 ≤
        ((287 : ℝ)/512)^2 *
          (512195358951/5000000000000000000000 : ℝ) := by
    norm_num
  have ht :
      ((287 : ℝ)/512)^2 *
        (512195358951/5000000000000000000000 : ℝ) ≤
      ((287 : ℝ)/512)^2 *
        (∫ x in (287/512:ℝ)..(9/16:ℝ), x^14*thetaFirstMode x) := by
    simpa using hs
  exact hn.trans ht

end
end CarrySelfAdjointOperator
