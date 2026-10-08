import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature08
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative12
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative13

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_256 :
    (240239527712217/250000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(257/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-80922674616230204865423/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (1/2:ℝ) (257/512:ℝ)-(257/512:ℝ)*thetaPowerMass 10 (1/2:ℝ) (257/512:ℝ)) ≤
      thetaFirstModeFirst (257/512:ℝ)*(thetaPowerMass 11 (1/2:ℝ) (257/512:ℝ)-(257/512:ℝ)*thetaPowerMass 10 (1/2:ℝ) (257/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0389.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (1/2:ℝ) (257/512:ℝ)
    (257/512:ℝ) (48612974743/100000000000000:ℝ) (-80922674616230204865423/10000000000000000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_256
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0769).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_256 :
    (∫ x in (1/2:ℝ)..(257/512:ℝ), x^10*thetaFirstMode x) ≤ (3843849891571/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/2:ℝ) (257/512:ℝ)
    (50216326329/100000000000000:ℝ) (9722621481/20000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_256 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0769).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_257 :
    (967124330749591/1000000000000000000000000:ℝ) ≤ ∫ x in (257/512:ℝ)..(129/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-80899005738204708052923487899/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 10 (257/512:ℝ) (129/256:ℝ)) ≤
      thetaFirstModeFirst (859903185597392841993/1713045360379148700160:ℝ)*(thetaPowerMass 11 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 10 (257/512:ℝ) (129/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0390.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (257/512:ℝ) (129/256:ℝ)
    (859903185597392841993/1713045360379148700160:ℝ) (3037286171/6250000000000:ℝ) (-80899005738204708052923487899/10000000000000000000000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_257
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0773).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_257 :
    (∫ x in (257/512:ℝ)..(129/256:ℝ), x^10*thetaFirstMode x) ≤ (967130513725119/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (257/512:ℝ) (129/256:ℝ)
    (9722621481/20000000000000:ℝ) (47054917301/100000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_257 (thetaFirstMode_refined_node_0769).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_258 :
    (486529664154893/500000000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(259/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-191051690789112102990023/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (129/256:ℝ) (259/512:ℝ)-(259/512:ℝ)*thetaPowerMass 10 (129/256:ℝ) (259/512:ℝ)) ≤
      thetaFirstModeFirst (259/512:ℝ)*(thetaPowerMass 11 (129/256:ℝ) (259/512:ℝ)-(259/512:ℝ)*thetaPowerMass 10 (129/256:ℝ) (259/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0392.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (129/256:ℝ) (259/512:ℝ)
    (259/512:ℝ) (22770282629/50000000000000:ℝ) (-191051690789112102990023/25000000000000000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_258
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0775).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_258 :
    (∫ x in (129/256:ℝ)..(259/512:ℝ), x^10*thetaFirstMode x) ≤ (973063817058631/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (129/256:ℝ) (259/512:ℝ)
    (47054917301/100000000000000:ℝ) (45540690511/100000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_258 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0775).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_259 :
    (24468796098289/25000000000000000000000:ℝ) ≤ ∫ x in (259/512:ℝ)..(65/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-190995732180727575413904541487/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 10 (259/512:ℝ) (65/128:ℝ)) ≤
      thetaFirstModeFirst (922036494355905427191/1822640620152625231360:ℝ)*(thetaPowerMass 11 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 10 (259/512:ℝ) (65/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0393.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (259/512:ℝ) (65/128:ℝ)
    (922036494355905427191/1822640620152625231360:ℝ) (5690650121/12500000000000:ℝ) (-190995732180727575413904541487/25000000000000000000000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_259
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0779).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_259 :
    (∫ x in (259/512:ℝ)..(65/128:ℝ), x^10*thetaFirstMode x) ≤ (978758225743397/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (259/512:ℝ) (65/128:ℝ)
    (45540690511/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_259 (thetaFirstMode_refined_node_0775).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_260 :
    (98420514176661/100000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(261/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-180327385626682680938823/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (65/128:ℝ) (261/512:ℝ)-(261/512:ℝ)*thetaPowerMass 10 (65/128:ℝ) (261/512:ℝ)) ≤
      thetaFirstModeFirst (261/512:ℝ)*(thetaPowerMass 11 (65/128:ℝ) (261/512:ℝ)-(261/512:ℝ)*thetaPowerMass 10 (65/128:ℝ) (261/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0395.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (65/128:ℝ) (261/512:ℝ)
    (261/512:ℝ) (42639843507/100000000000000:ℝ) (-180327385626682680938823/25000000000000000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_260
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0781).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_260 :
    (∫ x in (65/128:ℝ)..(261/512:ℝ), x^10*thetaFirstMode x) ≤ (984209756035797/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (65/128:ℝ) (261/512:ℝ)
    (44069380939/100000000000000:ℝ) (42639961701/100000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_260 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0781).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_261 :
    (989408021882119/1000000000000000000000000:ℝ) ≤ ∫ x in (261/512:ℝ)..(131/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-180274491621043331871067780681/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 10 (261/512:ℝ) (131/256:ℝ)) ≤
      thetaFirstModeFirst (988128929174544916209/1938322640485932981760:ℝ)*(thetaPowerMass 11 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 10 (261/512:ℝ) (131/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0396.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (261/512:ℝ) (131/256:ℝ)
    (988128929174544916209/1938322640485932981760:ℝ) (42625452771/100000000000000:ℝ) (-180274491621043331871067780681/25000000000000000000000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_261
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0785).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_261 :
    (∫ x in (261/512:ℝ)..(131/256:ℝ), x^10*thetaFirstMode x) ≤ (197882920404309/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (261/512:ℝ) (131/256:ℝ)
    (42639961701/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_261 (thetaFirstMode_refined_node_0781).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_262 :
    (497182200716273/500000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(263/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-13609144864202792869397/2000000000000000000000000:ℝ)*(thetaPowerMass 11 (131/256:ℝ) (263/512:ℝ)-(263/512:ℝ)*thetaPowerMass 10 (131/256:ℝ) (263/512:ℝ)) ≤
      thetaFirstModeFirst (263/512:ℝ)*(thetaPowerMass 11 (131/256:ℝ) (263/512:ℝ)-(263/512:ℝ)*thetaPowerMass 10 (131/256:ℝ) (263/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0398.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (131/256:ℝ) (263/512:ℝ)
    (263/512:ℝ) (1596106801/4000000000000:ℝ) (-13609144864202792869397/2000000000000000000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_262
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0787).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_262 :
    (∫ x in (131/256:ℝ)..(263/512:ℝ), x^10*thetaFirstMode x) ≤ (198873827965341/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (131/256:ℝ) (263/512:ℝ)
    (8250284983/20000000000000:ℝ) (79805563/200000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_262 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0787).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_263 :
    (999063154122901/1000000000000000000000000:ℝ) ≤ ∫ x in (263/512:ℝ)..(33/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-170064337945951876666314350811/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 10 (263/512:ℝ) (33/64:ℝ)) ≤
      thetaFirstModeFirst (1058399498889348955407/2060378912321919132160:ℝ)*(thetaPowerMass 11 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 10 (263/512:ℝ) (33/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0399.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (263/512:ℝ) (33/64:ℝ)
    (1058399498889348955407/2060378912321919132160:ℝ) (39889197553/100000000000000:ℝ) (-170064337945951876666314350811/25000000000000000000000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_263
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0791).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_263 :
    (∫ x in (263/512:ℝ)..(33/64:ℝ), x^10*thetaFirstMode x) ≤ (999069931617109/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (263/512:ℝ) (33/64:ℝ)
    (79805563/200000000000:ℝ) (9648265241/25000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_263 (thetaFirstMode_refined_node_0787).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_264 :
    (1003508868570133/1000000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(265/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-20049178650430955229361/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (33/64:ℝ) (265/512:ℝ)-(265/512:ℝ)*thetaPowerMass 10 (33/64:ℝ) (265/512:ℝ)) ≤
      thetaFirstModeFirst (265/512:ℝ)*(thetaPowerMass 11 (33/64:ℝ) (265/512:ℝ)-(265/512:ℝ)*thetaPowerMass 10 (33/64:ℝ) (265/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0401.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (33/64:ℝ) (265/512:ℝ)
    (265/512:ℝ) (37321206119/100000000000000:ℝ) (-20049178650430955229361/3125000000000000000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_264
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0793).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_264 :
    (∫ x in (33/64:ℝ)..(265/512:ℝ), x^10*thetaFirstMode x) ≤ (1003513729369369/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (33/64:ℝ) (265/512:ℝ)
    (9648265241/25000000000000:ℝ) (46651639/125000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_264 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0793).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_265 :
    (50384525246411/50000000000000000000000:ℝ) ≤ ∫ x in (265/512:ℝ)..(133/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-64138495771534099639337229171/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 10 (265/512:ℝ) (133/256:ℝ)) ≤
      thetaFirstModeFirst (226615503159325427085/437821630895601469952:ℝ)*(thetaPowerMass 11 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 10 (265/512:ℝ) (133/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0402.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (265/512:ℝ) (133/256:ℝ)
    (226615503159325427085/437821630895601469952:ℝ) (7461719873/20000000000000:ℝ) (-64138495771534099639337229171/10000000000000000000000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_265
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0797).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_265 :
    (∫ x in (265/512:ℝ)..(133/256:ℝ), x^10*thetaFirstMode x) ≤ (50384873921407/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (265/512:ℝ) (133/256:ℝ)
    (46651639/125000000000:ℝ) (36086598273/100000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_265 (thetaFirstMode_refined_node_0793).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_266 :
    (1011613339598513/1000000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(267/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-37786532893148897920281/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (133/256:ℝ) (267/512:ℝ)-(267/512:ℝ)*thetaPowerMass 10 (133/256:ℝ) (267/512:ℝ)) ≤
      thetaFirstModeFirst (267/512:ℝ)*(thetaPowerMass 11 (133/256:ℝ) (267/512:ℝ)-(267/512:ℝ)*thetaPowerMass 10 (133/256:ℝ) (267/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0404.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (133/256:ℝ) (267/512:ℝ)
    (267/512:ℝ) (8721976803/25000000000000:ℝ) (-37786532893148897920281/6250000000000000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_266
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0799).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_266 :
    (∫ x in (133/256:ℝ)..(267/512:ℝ), x^10*thetaFirstMode x) ≤ (1011618320805841/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (133/256:ℝ) (267/512:ℝ)
    (36086598273/100000000000000:ℝ) (8722001553/25000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_266 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0799).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_267 :
    (1015266430571641/1000000000000000000000000:ℝ) ≤ ∫ x in (267/512:ℝ)..(67/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-151101592043496668191229170167/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 10 (267/512:ℝ) (67/128:ℝ)) ≤
      thetaFirstModeFirst (1212402996478512506943/2324820661745853468160:ℝ)*(thetaPowerMass 11 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 10 (267/512:ℝ) (67/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0405.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (267/512:ℝ) (67/128:ℝ)
    (1212402996478512506943/2324820661745853468160:ℝ) (4359514533/12500000000000:ℝ) (-151101592043496668191229170167/25000000000000000000000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_267
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0803).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_267 :
    (∫ x in (267/512:ℝ)..(67/128:ℝ), x^10*thetaFirstMode x) ≤ (507636799133729/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (267/512:ℝ) (67/128:ℝ)
    (8722001553/25000000000000:ℝ) (33724636797/100000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_267 (thetaFirstMode_refined_node_0799).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_268 :
    (203731151150491/200000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(269/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-17794280061090830197647/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (67/128:ℝ) (269/512:ℝ)-(269/512:ℝ)*thetaPowerMass 10 (67/128:ℝ) (269/512:ℝ)) ≤
      thetaFirstModeFirst (269/512:ℝ)*(thetaPowerMass 11 (67/128:ℝ) (269/512:ℝ)-(269/512:ℝ)*thetaPowerMass 10 (67/128:ℝ) (269/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0407.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (67/128:ℝ) (269/512:ℝ)
    (269/512:ℝ) (16297758063/50000000000000:ℝ) (-17794280061090830197647/3125000000000000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_268
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0805).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_268 :
    (∫ x in (67/128:ℝ)..(269/512:ℝ), x^10*thetaFirstMode x) ≤ (1018660855139957/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (67/128:ℝ) (269/512:ℝ)
    (33724636797/100000000000000:ℝ) (32595609347/100000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_268 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0805).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_269 :
    (204354096255641/200000000000000000000000:ℝ) ≤ ∫ x in (269/512:ℝ)..(135/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2846244469767174472472746191/500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 10 (269/512:ℝ) (135/256:ℝ)) ≤
      thetaFirstModeFirst (1296627075007226251641/2467838661023287068160:ℝ)*(thetaPowerMass 11 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 10 (269/512:ℝ) (135/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0408.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (269/512:ℝ) (135/256:ℝ)
    (1296627075007226251641/2467838661023287068160:ℝ) (32584493593/100000000000000:ℝ) (-2846244469767174472472746191/500000000000000000000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_269
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0809).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_269 :
    (∫ x in (269/512:ℝ)..(135/256:ℝ), x^10*thetaFirstMode x) ≤ (1021777840941469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (269/512:ℝ) (135/256:ℝ)
    (32595609347/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_269 (thetaFirstMode_refined_node_0805).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_270 :
    (512308648848591/500000000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(271/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-33500003403649176955953/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (135/256:ℝ) (271/512:ℝ)-(271/512:ℝ)*thetaPowerMass 10 (135/256:ℝ) (271/512:ℝ)) ≤
      thetaFirstModeFirst (271/512:ℝ)*(thetaPowerMass 11 (135/256:ℝ) (271/512:ℝ)-(271/512:ℝ)*thetaPowerMass 10 (135/256:ℝ) (271/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0410.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (135/256:ℝ) (271/512:ℝ)
    (271/512:ℝ) (15218528157/50000000000000:ℝ) (-33500003403649176955953/6250000000000000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_270
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0811).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_270 :
    (∫ x in (135/256:ℝ)..(271/512:ℝ), x^10*thetaFirstMode x) ≤ (512311256337637/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (135/256:ℝ) (271/512:ℝ)
    (3150006051/10000000000000:ℝ) (7609286011/25000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_270 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0811).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_271 :
    (256796371995957/250000000000000000000000:ℝ) ≤ ∫ x in (271/512:ℝ)..(17/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1339603963847844488296349709/250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 10 (271/512:ℝ) (17/32:ℝ)) ≤
      thetaFirstModeFirst (1386012428812593345159/2618496675601163368960:ℝ)*(thetaPowerMass 11 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 10 (271/512:ℝ) (17/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0411.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (271/512:ℝ) (17/32:ℝ)
    (1386012428812593345159/2618496675601163368960:ℝ) (950836163/3125000000000:ℝ) (-1339603963847844488296349709/250000000000000000000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_271
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0815).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_271 :
    (∫ x in (271/512:ℝ)..(17/32:ℝ), x^10*thetaFirstMode x) ≤ (256798259233377/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (271/512:ℝ) (17/32:ℝ)
    (7609286011/25000000000000:ℝ) (2940603061/10000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_271 (thetaFirstMode_refined_node_0811).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_272 :
    (1029482463984401/1000000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(273/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-126066146149654497588761/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (17/32:ℝ) (273/512:ℝ)-(273/512:ℝ)*thetaPowerMass 10 (17/32:ℝ) (273/512:ℝ)) ≤
      thetaFirstModeFirst (273/512:ℝ)*(thetaPowerMass 11 (17/32:ℝ) (273/512:ℝ)-(273/512:ℝ)*thetaPowerMass 10 (17/32:ℝ) (273/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0413.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (17/32:ℝ) (273/512:ℝ)
    (273/512:ℝ) (14202912517/50000000000000:ℝ) (-126066146149654497588761/25000000000000000000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_272
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0817).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_272 :
    (∫ x in (17/32:ℝ)..(273/512:ℝ), x^10*thetaFirstMode x) ≤ (1029487791746389/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/32:ℝ) (273/512:ℝ)
    (2940603061/10000000000000:ℝ) (887684611/3125000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_272 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0817).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_273 :
    (103149763290573/100000000000000000000000:ℝ) ≤ ∫ x in (273/512:ℝ)..(137/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-126028810762700441259518644517/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 10 (273/512:ℝ) (137/256:ℝ)) ≤
      thetaFirstModeFirst (1480833717501674392857/2777141897728678812160:ℝ)*(thetaPowerMass 11 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 10 (273/512:ℝ) (137/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0414.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (273/512:ℝ) (137/256:ℝ)
    (1480833717501674392857/2777141897728678812160:ℝ) (28396206701/100000000000000:ℝ) (-126028810762700441259518644517/25000000000000000000000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_273
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0821).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_273 :
    (∫ x in (273/512:ℝ)..(137/256:ℝ), x^10*thetaFirstMode x) ≤ (1031505368065197/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (273/512:ℝ) (137/256:ℝ)
    (887684611/3125000000000:ℝ) (27435978683/100000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_273 (thetaFirstMode_refined_node_0817).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_274 :
    (1033239133678011/1000000000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(275/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-29633943154107415486181/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (137/256:ℝ) (275/512:ℝ)-(275/512:ℝ)*thetaPowerMass 10 (137/256:ℝ) (275/512:ℝ)) ≤
      thetaFirstModeFirst (275/512:ℝ)*(thetaPowerMass 11 (137/256:ℝ) (275/512:ℝ)-(275/512:ℝ)*thetaPowerMass 10 (137/256:ℝ) (275/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0416.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (137/256:ℝ) (275/512:ℝ)
    (275/512:ℝ) (13247693251/50000000000000:ℝ) (-29633943154107415486181/6250000000000000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_274
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0823).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_274 :
    (∫ x in (137/256:ℝ)..(275/512:ℝ), x^10*thetaFirstMode x) ≤ (129155571393623/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (137/256:ℝ) (275/512:ℝ)
    (27435978683/100000000000000:ℝ) (13247732037/50000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_274 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0823).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_275 :
    (1034696503838683/1000000000000000000000000:ℝ) ≤ ∫ x in (275/512:ℝ)..(69/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-237001211691605884081506846923/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 10 (275/512:ℝ) (69/128:ℝ)) ≤
      thetaFirstModeFirst (316275606984747764475/588826913916326538752:ℝ)*(thetaPowerMass 11 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 10 (275/512:ℝ) (69/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0417.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (275/512:ℝ) (69/128:ℝ)
    (316275606984747764475/588826913916326538752:ℝ) (26486408473/100000000000000:ℝ) (-237001211691605884081506846923/50000000000000000000000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_275
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0827).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_275 :
    (∫ x in (275/512:ℝ)..(69/128:ℝ), x^10*thetaFirstMode x) ≤ (1034704421616293/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (275/512:ℝ) (69/128:ℝ)
    (13247732037/50000000000000:ℝ) (5116719967/20000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_275 (thetaFirstMode_refined_node_0823).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_276 :
    (1035878612410893/1000000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(277/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2227849358687339713131/500000000000000000000000:ℝ)*(thetaPowerMass 11 (69/128:ℝ) (277/512:ℝ)-(277/512:ℝ)*thetaPowerMass 10 (69/128:ℝ) (277/512:ℝ)) ≤
      thetaFirstModeFirst (277/512:ℝ)*(thetaPowerMass 11 (69/128:ℝ) (277/512:ℝ)-(277/512:ℝ)*thetaPowerMass 10 (69/128:ℝ) (277/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0419.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (69/128:ℝ) (277/512:ℝ)
    (277/512:ℝ) (1234978251/5000000000000:ℝ) (-2227849358687339713131/500000000000000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_276
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0829).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_276 :
    (∫ x in (69/128:ℝ)..(277/512:ℝ), x^10*thetaFirstMode x) ≤ (1035884156180101/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (69/128:ℝ) (277/512:ℝ)
    (5116719967/20000000000000:ℝ) (24699637901/100000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_276 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0829).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_277 :
    (1036775131750309/1000000000000000000000000:ℝ) ≤ ∫ x in (277/512:ℝ)..(139/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4454374444447249812042543297/1000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 10 (277/512:ℝ) (139/256:ℝ)) ≤
      thetaFirstModeFirst (1687945374778197279393/3119848372759046172160:ℝ)*(thetaPowerMass 11 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 10 (277/512:ℝ) (139/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0420.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (277/512:ℝ) (139/256:ℝ)
    (1687945374778197279393/3119848372759046172160:ℝ) (24691188943/100000000000000:ℝ) (-4454374444447249812042543297/1000000000000000000000000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_277
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0833).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_277 :
    (∫ x in (277/512:ℝ)..(139/256:ℝ), x^10*thetaFirstMode x) ≤ (1036783228173311/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (277/512:ℝ) (139/256:ℝ)
    (24699637901/100000000000000:ℝ) (2980355727/12500000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_277 (thetaFirstMode_refined_node_0829).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_278 :
    (1037395661344191/1000000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(279/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1307753097178921545909/312500000000000000000000:ℝ)*(thetaPowerMass 11 (139/256:ℝ) (279/512:ℝ)-(279/512:ℝ)*thetaPowerMass 10 (139/256:ℝ) (279/512:ℝ)) ≤
      thetaFirstModeFirst (279/512:ℝ)*(thetaPowerMass 11 (139/256:ℝ) (279/512:ℝ)-(279/512:ℝ)*thetaPowerMass 10 (139/256:ℝ) (279/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0422.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (139/256:ℝ) (279/512:ℝ)
    (279/512:ℝ) (5753109521/25000000000000:ℝ) (-1307753097178921545909/312500000000000000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_278
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0835).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_278 :
    (∫ x in (139/256:ℝ)..(279/512:ℝ), x^10*thetaFirstMode x) ≤ (518700653916921/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (139/256:ℝ) (279/512:ℝ)
    (2980355727/12500000000000:ℝ) (575312663/2500000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_278 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0835).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_279 :
    (207546002332127/200000000000000000000000:ℝ) ≤ ∫ x in (279/512:ℝ)..(35/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-209178193349719400826863010881/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 10 (279/512:ℝ) (35/64:ℝ)) ≤
      thetaFirstModeFirst (1800849110067536394591/3304670826434478952960:ℝ)*(thetaPowerMass 11 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 10 (279/512:ℝ) (35/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0423.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (279/512:ℝ) (35/64:ℝ)
    (1800849110067536394591/3304670826434478952960:ℝ) (5751156907/25000000000000:ℝ) (-209178193349719400826863010881/50000000000000000000000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_279
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0839).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_279 :
    (∫ x in (279/512:ℝ)..(35/64:ℝ), x^10*thetaFirstMode x) ≤ (518869141140431/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (279/512:ℝ) (35/64:ℝ)
    (575312663/2500000000000:ℝ) (22207918131/100000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_279 (thetaFirstMode_refined_node_0835).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_280 :
    (16215445468057/15625000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(281/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-24550892082273800344127/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (35/64:ℝ) (281/512:ℝ)-(281/512:ℝ)*thetaPowerMass 10 (35/64:ℝ) (281/512:ℝ)) ≤
      thetaFirstModeFirst (281/512:ℝ)*(thetaPowerMass 11 (35/64:ℝ) (281/512:ℝ)-(281/512:ℝ)*thetaPowerMass 10 (35/64:ℝ) (281/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0425.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (35/64:ℝ) (281/512:ℝ)
    (281/512:ℝ) (5357082377/25000000000000:ℝ) (-24550892082273800344127/6250000000000000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_280
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0841).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_280 :
    (∫ x in (35/64:ℝ)..(281/512:ℝ), x^10*thetaFirstMode x) ≤ (103779425524081/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (35/64:ℝ) (281/512:ℝ)
    (22207918131/100000000000000:ℝ) (21428393733/100000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_280 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0841).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_281 :
    (518780553265507/500000000000000000000000:ℝ) ≤ ∫ x in (281/512:ℝ)..(141/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4908713650861315539022996177/1250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 10 (281/512:ℝ) (141/256:ℝ)) ≤
      thetaFirstModeFirst (1920416486701757070609/3499003694289312924160:ℝ)*(thetaPowerMass 11 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 10 (281/512:ℝ) (141/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0426.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (281/512:ℝ) (141/256:ℝ)
    (1920416486701757070609/3499003694289312924160:ℝ) (21421050267/100000000000000:ℝ) (-4908713650861315539022996177/1250000000000000000000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_281
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0845).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_281 :
    (∫ x in (281/512:ℝ)..(141/256:ℝ), x^10*thetaFirstMode x) ≤ (1037569546520817/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (281/512:ℝ) (141/256:ℝ)
    (21428393733/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_281 (thetaFirstMode_refined_node_0841).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_282 :
    (518529425606997/500000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(283/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-184254650728803337278867/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (141/256:ℝ) (283/512:ℝ)-(283/512:ℝ)*thetaPowerMass 10 (141/256:ℝ) (283/512:ℝ)) ≤
      thetaFirstModeFirst (283/512:ℝ)*(thetaPowerMass 11 (141/256:ℝ) (283/512:ℝ)-(283/512:ℝ)*thetaPowerMass 10 (141/256:ℝ) (283/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0428.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (141/256:ℝ) (283/512:ℝ)
    (283/512:ℝ) (19941802539/100000000000000:ℝ) (-184254650728803337278867/50000000000000000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_282
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0847).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_282 :
    (∫ x in (141/256:ℝ)..(283/512:ℝ), x^10*thetaFirstMode x) ≤ (518532345578033/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (141/256:ℝ) (283/512:ℝ)
    (20673261159/100000000000000:ℝ) (19941862777/100000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_282 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0847).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_283 :
    (1036271834498829/1000000000000000000000000:ℝ) ≤ ∫ x in (283/512:ℝ)..(71/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-18419958018692515473673247019/5000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 10 (283/512:ℝ) (71/128:ℝ)) ≤
      thetaFirstModeFirst (2046989131565308077807/3703263400356200988160:ℝ)*(thetaPowerMass 11 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 10 (283/512:ℝ) (71/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0429.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (283/512:ℝ) (71/128:ℝ)
    (2046989131565308077807/3703263400356200988160:ℝ) (398700439/2000000000000:ℝ) (-18419958018692515473673247019/5000000000000000000000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_283
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0851).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_283 :
    (∫ x in (283/512:ℝ)..(71/128:ℝ), x^10*thetaFirstMode x) ≤ (1036280438475797/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (283/512:ℝ) (71/128:ℝ)
    (19941862777/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_283 (thetaFirstMode_refined_node_0847).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_284 :
    (517605910271303/500000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(285/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-21594213178210310429903/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (71/128:ℝ) (285/512:ℝ)-(285/512:ℝ)*thetaPowerMass 10 (71/128:ℝ) (285/512:ℝ)) ≤
      thetaFirstModeFirst (285/512:ℝ)*(thetaPowerMass 11 (71/128:ℝ) (285/512:ℝ)-(285/512:ℝ)*thetaPowerMass 10 (71/128:ℝ) (285/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0431.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (71/128:ℝ) (285/512:ℝ)
    (285/512:ℝ) (4636913251/25000000000000:ℝ) (-21594213178210310429903/6250000000000000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_284
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0853).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_284 :
    (∫ x in (71/128:ℝ)..(285/512:ℝ), x^10*thetaFirstMode x) ≤ (258804437686527/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (71/128:ℝ) (285/512:ℝ)
    (19233555281/100000000000000:ℝ) (18547709471/100000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_284 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0853).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_285 :
    (1033869039168293/1000000000000000000000000:ℝ) ≤ ∫ x in (285/512:ℝ)..(143/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-172701971547548303234881112397/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 10 (285/512:ℝ) (143/256:ℝ)) ≤
      thetaFirstModeFirst (436184715072406009365/783576290780361661952:ℝ)*(thetaPowerMass 11 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 10 (285/512:ℝ) (143/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0432.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (285/512:ℝ) (143/256:ℝ)
    (436184715072406009365/783576290780361661952:ℝ) (927067013/5000000000000:ℝ) (-172701971547548303234881112397/50000000000000000000000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_285
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0857).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_285 :
    (∫ x in (285/512:ℝ)..(143/256:ℝ), x^10*thetaFirstMode x) ≤ (1033877801490879/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (285/512:ℝ) (143/256:ℝ)
    (18547709471/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_285 (thetaFirstMode_refined_node_0853).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_286 :
    (1032255958003361/1000000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(287/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2023448003795163738991/625000000000000000000000:ℝ)*(thetaPowerMass 11 (143/256:ℝ) (287/512:ℝ)-(287/512:ℝ)*thetaPowerMass 10 (143/256:ℝ) (287/512:ℝ)) ≤
      thetaFirstModeFirst (287/512:ℝ)*(thetaPowerMass 11 (143/256:ℝ) (287/512:ℝ)-(287/512:ℝ)*thetaPowerMass 10 (143/256:ℝ) (287/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0434.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (143/256:ℝ) (287/512:ℝ)
    (287/512:ℝ) (215511281/1250000000000:ℝ) (-2023448003795163738991/625000000000000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_286
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0859).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_286 :
    (∫ x in (143/256:ℝ)..(287/512:ℝ), x^10*thetaFirstMode x) ≤ (516130986911017/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (143/256:ℝ) (287/512:ℝ)
    (17883710043/100000000000000:ℝ) (862047769/5000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_286 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0859).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_287 :
    (515181471929607/500000000000000000000000:ℝ) ≤ ∫ x in (287/512:ℝ)..(9/16:ℝ), x^10*thetaFirstMode x := by
  have hd : (-32365453507474057315971426559/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 10 (287/512:ℝ) (9/16:ℝ)) ≤
      thetaFirstModeFirst (2322591790558180904343/4143304883478902172160:ℝ)*(thetaPowerMass 11 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 10 (287/512:ℝ) (9/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0435.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (287/512:ℝ) (9/16:ℝ)
    (2322591790558180904343/4143304883478902172160:ℝ) (17235028451/100000000000000:ℝ) (-32365453507474057315971426559/10000000000000000000000000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_287
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0863).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_287 :
    (∫ x in (287/512:ℝ)..(9/16:ℝ), x^10*thetaFirstMode x) ≤ (515185929164577/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (287/512:ℝ) (9/16:ℝ)
    (862047769/5000000000000:ℝ) (2077357167/12500000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_287 (thetaFirstMode_refined_node_0859).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
