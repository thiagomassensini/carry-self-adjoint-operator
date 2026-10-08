import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature08
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative12
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative13

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_12_256 :
    (60295052644853/250000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(257/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-80922674616230204865423/10000000000000000000000000:ℝ)*(thetaPowerMass 13 (1/2:ℝ) (257/512:ℝ)-(257/512:ℝ)*thetaPowerMass 12 (1/2:ℝ) (257/512:ℝ)) ≤
      thetaFirstModeFirst (257/512:ℝ)*(thetaPowerMass 13 (1/2:ℝ) (257/512:ℝ)-(257/512:ℝ)*thetaPowerMass 12 (1/2:ℝ) (257/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0389.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (1/2:ℝ) (257/512:ℝ)
    (257/512:ℝ) (48612974743/100000000000000:ℝ) (-80922674616230204865423/10000000000000000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_256
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0769).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_256 :
    (∫ x in (1/2:ℝ)..(257/512:ℝ), x^12*thetaFirstMode x) ≤ (241181304798597/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (1/2:ℝ) (257/512:ℝ)
    (50216326329/100000000000000:ℝ) (9722621481/20000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_256 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0769).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_257 :
    (122312026277091/500000000000000000000000:ℝ) ≤ ∫ x in (257/512:ℝ)..(129/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-80899005738204708052923487899/10000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 12 (257/512:ℝ) (129/256:ℝ)) ≤
      thetaFirstModeFirst (859903185597392841993/1713045360379148700160:ℝ)*(thetaPowerMass 13 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 12 (257/512:ℝ) (129/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0390.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (257/512:ℝ) (129/256:ℝ)
    (859903185597392841993/1713045360379148700160:ℝ) (3037286171/6250000000000:ℝ) (-80899005738204708052923487899/10000000000000000000000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_257
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0773).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_257 :
    (∫ x in (257/512:ℝ)..(129/256:ℝ), x^12*thetaFirstMode x) ≤ (244625617645141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (257/512:ℝ) (129/256:ℝ)
    (9722621481/20000000000000:ℝ) (47054917301/100000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_257 (thetaFirstMode_refined_node_0769).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_258 :
    (248040563350547/1000000000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(259/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-191051690789112102990023/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (129/256:ℝ) (259/512:ℝ)-(259/512:ℝ)*thetaPowerMass 12 (129/256:ℝ) (259/512:ℝ)) ≤
      thetaFirstModeFirst (259/512:ℝ)*(thetaPowerMass 13 (129/256:ℝ) (259/512:ℝ)-(259/512:ℝ)*thetaPowerMass 12 (129/256:ℝ) (259/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0392.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (129/256:ℝ) (259/512:ℝ)
    (259/512:ℝ) (22770282629/50000000000000:ℝ) (-191051690789112102990023/25000000000000000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_258
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0775).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_258 :
    (∫ x in (129/256:ℝ)..(259/512:ℝ), x^12*thetaFirstMode x) ≤ (248041706978561/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (129/256:ℝ) (259/512:ℝ)
    (47054917301/100000000000000:ℝ) (45540690511/100000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_258 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0775).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_259 :
    (12571280697279/50000000000000000000000:ℝ) ≤ ∫ x in (259/512:ℝ)..(65/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-190995732180727575413904541487/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 12 (259/512:ℝ) (65/128:ℝ)) ≤
      thetaFirstModeFirst (922036494355905427191/1822640620152625231360:ℝ)*(thetaPowerMass 13 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 12 (259/512:ℝ) (65/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0393.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (259/512:ℝ) (65/128:ℝ)
    (922036494355905427191/1822640620152625231360:ℝ) (5690650121/12500000000000:ℝ) (-190995732180727575413904541487/25000000000000000000000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_259
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0779).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_259 :
    (∫ x in (259/512:ℝ)..(65/128:ℝ), x^12*thetaFirstMode x) ≤ (31428406819999/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (259/512:ℝ) (65/128:ℝ)
    (45540690511/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_259 (thetaFirstMode_refined_node_0775).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_260 :
    (31847343680521/125000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(261/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-180327385626682680938823/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (65/128:ℝ) (261/512:ℝ)-(261/512:ℝ)*thetaPowerMass 12 (65/128:ℝ) (261/512:ℝ)) ≤
      thetaFirstModeFirst (261/512:ℝ)*(thetaPowerMass 13 (65/128:ℝ) (261/512:ℝ)-(261/512:ℝ)*thetaPowerMass 12 (65/128:ℝ) (261/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0395.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (65/128:ℝ) (261/512:ℝ)
    (261/512:ℝ) (42639843507/100000000000000:ℝ) (-180327385626682680938823/25000000000000000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_260
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0781).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_260 :
    (∫ x in (65/128:ℝ)..(261/512:ℝ), x^12*thetaFirstMode x) ≤ (127389971655119/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (65/128:ℝ) (261/512:ℝ)
    (44069380939/100000000000000:ℝ) (42639961701/100000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_260 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0781).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_261 :
    (129047871048519/500000000000000000000000:ℝ) ≤ ∫ x in (261/512:ℝ)..(131/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-180274491621043331871067780681/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 12 (261/512:ℝ) (131/256:ℝ)) ≤
      thetaFirstModeFirst (988128929174544916209/1938322640485932981760:ℝ)*(thetaPowerMass 13 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 12 (261/512:ℝ) (131/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0396.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (261/512:ℝ) (131/256:ℝ)
    (988128929174544916209/1938322640485932981760:ℝ) (42625452771/100000000000000:ℝ) (-180274491621043331871067780681/25000000000000000000000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_261
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0785).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_261 :
    (∫ x in (261/512:ℝ)..(131/256:ℝ), x^12*thetaFirstMode x) ≤ (129048729936419/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (261/512:ℝ) (131/256:ℝ)
    (42639961701/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_261 (thetaFirstMode_refined_node_0781).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_262 :
    (8168007884967/31250000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(263/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-13609144864202792869397/2000000000000000000000000:ℝ)*(thetaPowerMass 13 (131/256:ℝ) (263/512:ℝ)-(263/512:ℝ)*thetaPowerMass 12 (131/256:ℝ) (263/512:ℝ)) ≤
      thetaFirstModeFirst (263/512:ℝ)*(thetaPowerMass 13 (131/256:ℝ) (263/512:ℝ)-(263/512:ℝ)*thetaPowerMass 12 (131/256:ℝ) (263/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0398.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (131/256:ℝ) (263/512:ℝ)
    (263/512:ℝ) (1596106801/4000000000000:ℝ) (-13609144864202792869397/2000000000000000000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_262
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0787).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_262 :
    (∫ x in (131/256:ℝ)..(263/512:ℝ), x^12*thetaFirstMode x) ≤ (261377497194359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (131/256:ℝ) (263/512:ℝ)
    (8250284983/20000000000000:ℝ) (79805563/200000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_262 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0787).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_263 :
    (132307980327699/500000000000000000000000:ℝ) ≤ ∫ x in (263/512:ℝ)..(33/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-170064337945951876666314350811/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 12 (263/512:ℝ) (33/64:ℝ)) ≤
      thetaFirstModeFirst (1058399498889348955407/2060378912321919132160:ℝ)*(thetaPowerMass 13 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 12 (263/512:ℝ) (33/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0399.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (263/512:ℝ) (33/64:ℝ)
    (1058399498889348955407/2060378912321919132160:ℝ) (39889197553/100000000000000:ℝ) (-170064337945951876666314350811/25000000000000000000000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_263
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0791).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_263 :
    (∫ x in (263/512:ℝ)..(33/64:ℝ), x^12*thetaFirstMode x) ≤ (26461775711961/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (263/512:ℝ) (33/64:ℝ)
    (79805563/200000000000:ℝ) (9648265241/25000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_263 (thetaFirstMode_refined_node_0787).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_264 :
    (53562931286201/200000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(265/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-20049178650430955229361/3125000000000000000000000:ℝ)*(thetaPowerMass 13 (33/64:ℝ) (265/512:ℝ)-(265/512:ℝ)*thetaPowerMass 12 (33/64:ℝ) (265/512:ℝ)) ≤
      thetaFirstModeFirst (265/512:ℝ)*(thetaPowerMass 13 (33/64:ℝ) (265/512:ℝ)-(265/512:ℝ)*thetaPowerMass 12 (33/64:ℝ) (265/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0401.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (33/64:ℝ) (265/512:ℝ)
    (265/512:ℝ) (37321206119/100000000000000:ℝ) (-20049178650430955229361/3125000000000000000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_264
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0793).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_264 :
    (∫ x in (33/64:ℝ)..(265/512:ℝ), x^12*thetaFirstMode x) ≤ (33476994124393/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (33/64:ℝ) (265/512:ℝ)
    (9648265241/25000000000000:ℝ) (46651639/125000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_264 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0793).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_265 :
    (67741983924371/250000000000000000000000:ℝ) ≤ ∫ x in (265/512:ℝ)..(133/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-64138495771534099639337229171/10000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 12 (265/512:ℝ) (133/256:ℝ)) ≤
      thetaFirstModeFirst (226615503159325427085/437821630895601469952:ℝ)*(thetaPowerMass 13 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 12 (265/512:ℝ) (133/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0402.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (265/512:ℝ) (133/256:ℝ)
    (226615503159325427085/437821630895601469952:ℝ) (7461719873/20000000000000:ℝ) (-64138495771534099639337229171/10000000000000000000000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_265
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0797).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_265 :
    (∫ x in (265/512:ℝ)..(133/256:ℝ), x^12*thetaFirstMode x) ≤ (54193962456449/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (265/512:ℝ) (133/256:ℝ)
    (46651639/125000000000:ℝ) (36086598273/100000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_265 (thetaFirstMode_refined_node_0793).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_266 :
    (5481514606351/20000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(267/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-37786532893148897920281/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (133/256:ℝ) (267/512:ℝ)-(267/512:ℝ)*thetaPowerMass 12 (133/256:ℝ) (267/512:ℝ)) ≤
      thetaFirstModeFirst (267/512:ℝ)*(thetaPowerMass 13 (133/256:ℝ) (267/512:ℝ)-(267/512:ℝ)*thetaPowerMass 12 (133/256:ℝ) (267/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0404.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (133/256:ℝ) (267/512:ℝ)
    (267/512:ℝ) (8721976803/25000000000000:ℝ) (-37786532893148897920281/6250000000000000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_266
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0799).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_266 :
    (∫ x in (133/256:ℝ)..(267/512:ℝ), x^12*thetaFirstMode x) ≤ (27407707916523/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (133/256:ℝ) (267/512:ℝ)
    (36086598273/100000000000000:ℝ) (8722001553/25000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_266 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0799).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_267 :
    (277133559150311/1000000000000000000000000:ℝ) ≤ ∫ x in (267/512:ℝ)..(67/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-151101592043496668191229170167/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 12 (267/512:ℝ) (67/128:ℝ)) ≤
      thetaFirstModeFirst (1212402996478512506943/2324820661745853468160:ℝ)*(thetaPowerMass 13 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 12 (267/512:ℝ) (67/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0405.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (267/512:ℝ) (67/128:ℝ)
    (1212402996478512506943/2324820661745853468160:ℝ) (4359514533/12500000000000:ℝ) (-151101592043496668191229170167/25000000000000000000000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_267
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0803).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_267 :
    (∫ x in (267/512:ℝ)..(67/128:ℝ), x^12*thetaFirstMode x) ≤ (138567758581753/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (267/512:ℝ) (67/128:ℝ)
    (8722001553/25000000000000:ℝ) (33724636797/100000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_267 (thetaFirstMode_refined_node_0799).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_268 :
    (70035377519733/250000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(269/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-17794280061090830197647/3125000000000000000000000:ℝ)*(thetaPowerMass 13 (67/128:ℝ) (269/512:ℝ)-(269/512:ℝ)*thetaPowerMass 12 (67/128:ℝ) (269/512:ℝ)) ≤
      thetaFirstModeFirst (269/512:ℝ)*(thetaPowerMass 13 (67/128:ℝ) (269/512:ℝ)-(269/512:ℝ)*thetaPowerMass 12 (67/128:ℝ) (269/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0407.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (67/128:ℝ) (269/512:ℝ)
    (269/512:ℝ) (16297758063/50000000000000:ℝ) (-17794280061090830197647/3125000000000000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_268
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0805).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_268 :
    (∫ x in (67/128:ℝ)..(269/512:ℝ), x^12*thetaFirstMode x) ≤ (14007145586413/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (67/128:ℝ) (269/512:ℝ)
    (33724636797/100000000000000:ℝ) (32595609347/100000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_268 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0805).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_269 :
    (283095032217561/1000000000000000000000000:ℝ) ≤ ∫ x in (269/512:ℝ)..(135/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-2846244469767174472472746191/500000000000000000000000000000:ℝ)*(thetaPowerMass 13 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 12 (269/512:ℝ) (135/256:ℝ)) ≤
      thetaFirstModeFirst (1296627075007226251641/2467838661023287068160:ℝ)*(thetaPowerMass 13 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 12 (269/512:ℝ) (135/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0408.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (269/512:ℝ) (135/256:ℝ)
    (1296627075007226251641/2467838661023287068160:ℝ) (32584493593/100000000000000:ℝ) (-2846244469767174472472746191/500000000000000000000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_269
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0809).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_269 :
    (∫ x in (269/512:ℝ)..(135/256:ℝ), x^12*thetaFirstMode x) ≤ (283097072846683/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (269/512:ℝ) (135/256:ℝ)
    (32595609347/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_269 (thetaFirstMode_refined_node_0805).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_270 :
    (8937324461141/31250000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(271/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-33500003403649176955953/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (135/256:ℝ) (271/512:ℝ)-(271/512:ℝ)*thetaPowerMass 12 (135/256:ℝ) (271/512:ℝ)) ≤
      thetaFirstModeFirst (271/512:ℝ)*(thetaPowerMass 13 (135/256:ℝ) (271/512:ℝ)-(271/512:ℝ)*thetaPowerMass 12 (135/256:ℝ) (271/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0410.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (135/256:ℝ) (271/512:ℝ)
    (271/512:ℝ) (15218528157/50000000000000:ℝ) (-33500003403649176955953/6250000000000000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_270
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0811).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_270 :
    (∫ x in (135/256:ℝ)..(271/512:ℝ), x^12*thetaFirstMode x) ≤ (285995837608241/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (135/256:ℝ) (271/512:ℝ)
    (3150006051/10000000000000:ℝ) (7609286011/25000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_270 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0811).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_271 :
    (288834948474141/1000000000000000000000000:ℝ) ≤ ∫ x in (271/512:ℝ)..(17/32:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1339603963847844488296349709/250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 12 (271/512:ℝ) (17/32:ℝ)) ≤
      thetaFirstModeFirst (1386012428812593345159/2618496675601163368960:ℝ)*(thetaPowerMass 13 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 12 (271/512:ℝ) (17/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0411.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (271/512:ℝ) (17/32:ℝ)
    (1386012428812593345159/2618496675601163368960:ℝ) (950836163/3125000000000:ℝ) (-1339603963847844488296349709/250000000000000000000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_271
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0815).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_271 :
    (∫ x in (271/512:ℝ)..(17/32:ℝ), x^12*thetaFirstMode x) ≤ (288837072769497/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (271/512:ℝ) (17/32:ℝ)
    (7609286011/25000000000000:ℝ) (2940603061/10000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_271 (thetaFirstMode_refined_node_0811).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_272 :
    (72904292231141/250000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(273/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-126066146149654497588761/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (17/32:ℝ) (273/512:ℝ)-(273/512:ℝ)*thetaPowerMass 12 (17/32:ℝ) (273/512:ℝ)) ≤
      thetaFirstModeFirst (273/512:ℝ)*(thetaPowerMass 13 (17/32:ℝ) (273/512:ℝ)-(273/512:ℝ)*thetaPowerMass 12 (17/32:ℝ) (273/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0413.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (17/32:ℝ) (273/512:ℝ)
    (273/512:ℝ) (14202912517/50000000000000:ℝ) (-126066146149654497588761/25000000000000000000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_272
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0817).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_272 :
    (∫ x in (17/32:ℝ)..(273/512:ℝ), x^12*thetaFirstMode x) ≤ (145809338648323/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (17/32:ℝ) (273/512:ℝ)
    (2940603061/10000000000000:ℝ) (887684611/3125000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_272 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0817).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_273 :
    (73584093991927/250000000000000000000000:ℝ) ≤ ∫ x in (273/512:ℝ)..(137/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-126028810762700441259518644517/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 12 (273/512:ℝ) (137/256:ℝ)) ≤
      thetaFirstModeFirst (1480833717501674392857/2777141897728678812160:ℝ)*(thetaPowerMass 13 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 12 (273/512:ℝ) (137/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0414.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (273/512:ℝ) (137/256:ℝ)
    (1480833717501674392857/2777141897728678812160:ℝ) (28396206701/100000000000000:ℝ) (-126028810762700441259518644517/25000000000000000000000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_273
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0821).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_273 :
    (∫ x in (273/512:ℝ)..(137/256:ℝ), x^12*thetaFirstMode x) ≤ (147169292425369/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (273/512:ℝ) (137/256:ℝ)
    (887684611/3125000000000:ℝ) (27435978683/100000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_273 (thetaFirstMode_refined_node_0817).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_274 :
    (74248301044811/250000000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(275/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-29633943154107415486181/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (137/256:ℝ) (275/512:ℝ)-(275/512:ℝ)*thetaPowerMass 12 (137/256:ℝ) (275/512:ℝ)) ≤
      thetaFirstModeFirst (275/512:ℝ)*(thetaPowerMass 13 (137/256:ℝ) (275/512:ℝ)-(275/512:ℝ)*thetaPowerMass 12 (137/256:ℝ) (275/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0416.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (137/256:ℝ) (275/512:ℝ)
    (275/512:ℝ) (13247693251/50000000000000:ℝ) (-29633943154107415486181/6250000000000000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_274
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0823).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_274 :
    (∫ x in (137/256:ℝ)..(275/512:ℝ), x^12*thetaFirstMode x) ≤ (296994766288017/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (137/256:ℝ) (275/512:ℝ)
    (27435978683/100000000000000:ℝ) (13247732037/50000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_274 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0823).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_275 :
    (59916587576687/200000000000000000000000:ℝ) ≤ ∫ x in (275/512:ℝ)..(69/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-237001211691605884081506846923/50000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 12 (275/512:ℝ) (69/128:ℝ)) ≤
      thetaFirstModeFirst (316275606984747764475/588826913916326538752:ℝ)*(thetaPowerMass 13 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 12 (275/512:ℝ) (69/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0417.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (275/512:ℝ) (69/128:ℝ)
    (316275606984747764475/588826913916326538752:ℝ) (26486408473/100000000000000:ℝ) (-237001211691605884081506846923/50000000000000000000000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_275
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0827).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_275 :
    (∫ x in (275/512:ℝ)..(69/128:ℝ), x^12*thetaFirstMode x) ≤ (59917046421003/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (275/512:ℝ) (69/128:ℝ)
    (13247732037/50000000000000:ℝ) (5116719967/20000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_275 (thetaFirstMode_refined_node_0823).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_276 :
    (12084256755747/40000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(277/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-2227849358687339713131/500000000000000000000000:ℝ)*(thetaPowerMass 13 (69/128:ℝ) (277/512:ℝ)-(277/512:ℝ)*thetaPowerMass 12 (69/128:ℝ) (277/512:ℝ)) ≤
      thetaFirstModeFirst (277/512:ℝ)*(thetaPowerMass 13 (69/128:ℝ) (277/512:ℝ)-(277/512:ℝ)*thetaPowerMass 12 (69/128:ℝ) (277/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0419.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (69/128:ℝ) (277/512:ℝ)
    (277/512:ℝ) (1234978251/5000000000000:ℝ) (-2227849358687339713131/500000000000000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_276
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0829).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_276 :
    (∫ x in (69/128:ℝ)..(277/512:ℝ), x^12*thetaFirstMode x) ≤ (302108034829161/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (69/128:ℝ) (277/512:ℝ)
    (5116719967/20000000000000:ℝ) (24699637901/100000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_276 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0829).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_277 :
    (152279445605631/500000000000000000000000:ℝ) ≤ ∫ x in (277/512:ℝ)..(139/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-4454374444447249812042543297/1000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 12 (277/512:ℝ) (139/256:ℝ)) ≤
      thetaFirstModeFirst (1687945374778197279393/3119848372759046172160:ℝ)*(thetaPowerMass 13 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 12 (277/512:ℝ) (139/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0420.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (277/512:ℝ) (139/256:ℝ)
    (1687945374778197279393/3119848372759046172160:ℝ) (24691188943/100000000000000:ℝ) (-4454374444447249812042543297/1000000000000000000000000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_277
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0833).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_277 :
    (∫ x in (277/512:ℝ)..(139/256:ℝ), x^12*thetaFirstMode x) ≤ (38070158922721/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (277/512:ℝ) (139/256:ℝ)
    (24699637901/100000000000000:ℝ) (2980355727/12500000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_277 (thetaFirstMode_refined_node_0829).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_278 :
    (306941415631789/1000000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(279/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1307753097178921545909/312500000000000000000000:ℝ)*(thetaPowerMass 13 (139/256:ℝ) (279/512:ℝ)-(279/512:ℝ)*thetaPowerMass 12 (139/256:ℝ) (279/512:ℝ)) ≤
      thetaFirstModeFirst (279/512:ℝ)*(thetaPowerMass 13 (139/256:ℝ) (279/512:ℝ)-(279/512:ℝ)*thetaPowerMass 12 (139/256:ℝ) (279/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0422.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (139/256:ℝ) (279/512:ℝ)
    (279/512:ℝ) (5753109521/25000000000000:ℝ) (-1307753097178921545909/312500000000000000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_278
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0835).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_278 :
    (∫ x in (139/256:ℝ)..(279/512:ℝ), x^12*thetaFirstMode x) ≤ (306943085401359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (139/256:ℝ) (279/512:ℝ)
    (2980355727/12500000000000:ℝ) (575312663/2500000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_278 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0835).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_279 :
    (309249202949233/1000000000000000000000000:ℝ) ≤ ∫ x in (279/512:ℝ)..(35/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-209178193349719400826863010881/50000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 12 (279/512:ℝ) (35/64:ℝ)) ≤
      thetaFirstModeFirst (1800849110067536394591/3304670826434478952960:ℝ)*(thetaPowerMass 13 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 12 (279/512:ℝ) (35/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0423.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (279/512:ℝ) (35/64:ℝ)
    (1800849110067536394591/3304670826434478952960:ℝ) (5751156907/25000000000000:ℝ) (-209178193349719400826863010881/50000000000000000000000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_279
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0839).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_279 :
    (∫ x in (279/512:ℝ)..(35/64:ℝ), x^12*thetaFirstMode x) ≤ (154625834751653/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (279/512:ℝ) (35/64:ℝ)
    (575312663/2500000000000:ℝ) (22207918131/100000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_279 (thetaFirstMode_refined_node_0835).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_280 :
    (311483544018119/1000000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(281/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-24550892082273800344127/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (35/64:ℝ) (281/512:ℝ)-(281/512:ℝ)*thetaPowerMass 12 (35/64:ℝ) (281/512:ℝ)) ≤
      thetaFirstModeFirst (281/512:ℝ)*(thetaPowerMass 13 (35/64:ℝ) (281/512:ℝ)-(281/512:ℝ)*thetaPowerMass 12 (35/64:ℝ) (281/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0425.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (35/64:ℝ) (281/512:ℝ)
    (281/512:ℝ) (5357082377/25000000000000:ℝ) (-24550892082273800344127/6250000000000000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_280
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0841).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_280 :
    (∫ x in (35/64:ℝ)..(281/512:ℝ), x^12*thetaFirstMode x) ≤ (311485267488983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (35/64:ℝ) (281/512:ℝ)
    (22207918131/100000000000000:ℝ) (21428393733/100000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_280 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0841).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_281 :
    (313639623283089/1000000000000000000000000:ℝ) ≤ ∫ x in (281/512:ℝ)..(141/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-4908713650861315539022996177/1250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 12 (281/512:ℝ) (141/256:ℝ)) ≤
      thetaFirstModeFirst (1920416486701757070609/3499003694289312924160:ℝ)*(thetaPowerMass 13 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 12 (281/512:ℝ) (141/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0426.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (281/512:ℝ) (141/256:ℝ)
    (1920416486701757070609/3499003694289312924160:ℝ) (21421050267/100000000000000:ℝ) (-4908713650861315539022996177/1250000000000000000000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_281
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0845).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_281 :
    (∫ x in (281/512:ℝ)..(141/256:ℝ), x^12*thetaFirstMode x) ≤ (3920527206247/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (281/512:ℝ) (141/256:ℝ)
    (21428393733/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_281 (thetaFirstMode_refined_node_0841).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_282 :
    (315718972156591/1000000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(283/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-184254650728803337278867/50000000000000000000000000:ℝ)*(thetaPowerMass 13 (141/256:ℝ) (283/512:ℝ)-(283/512:ℝ)*thetaPowerMass 12 (141/256:ℝ) (283/512:ℝ)) ≤
      thetaFirstModeFirst (283/512:ℝ)*(thetaPowerMass 13 (141/256:ℝ) (283/512:ℝ)-(283/512:ℝ)*thetaPowerMass 12 (141/256:ℝ) (283/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0428.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (141/256:ℝ) (283/512:ℝ)
    (283/512:ℝ) (19941802539/100000000000000:ℝ) (-184254650728803337278867/50000000000000000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_282
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0847).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_282 :
    (∫ x in (141/256:ℝ)..(283/512:ℝ), x^12*thetaFirstMode x) ≤ (157860374544897/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (141/256:ℝ) (283/512:ℝ)
    (20673261159/100000000000000:ℝ) (19941862777/100000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_282 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0847).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_283 :
    (158858377672999/500000000000000000000000:ℝ) ≤ ∫ x in (283/512:ℝ)..(71/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-18419958018692515473673247019/5000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 12 (283/512:ℝ) (71/128:ℝ)) ≤
      thetaFirstModeFirst (2046989131565308077807/3703263400356200988160:ℝ)*(thetaPowerMass 13 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 12 (283/512:ℝ) (71/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0429.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (283/512:ℝ) (71/128:ℝ)
    (2046989131565308077807/3703263400356200988160:ℝ) (398700439/2000000000000:ℝ) (-18419958018692515473673247019/5000000000000000000000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_283
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0851).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_283 :
    (∫ x in (283/512:ℝ)..(71/128:ℝ), x^12*thetaFirstMode x) ≤ (158859697643787/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (283/512:ℝ) (71/128:ℝ)
    (19941862777/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_283 (thetaFirstMode_refined_node_0847).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_284 :
    (319634754506419/1000000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(285/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-21594213178210310429903/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (71/128:ℝ) (285/512:ℝ)-(285/512:ℝ)*thetaPowerMass 12 (71/128:ℝ) (285/512:ℝ)) ≤
      thetaFirstModeFirst (285/512:ℝ)*(thetaPowerMass 13 (71/128:ℝ) (285/512:ℝ)-(285/512:ℝ)*thetaPowerMass 12 (71/128:ℝ) (285/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0431.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (71/128:ℝ) (285/512:ℝ)
    (285/512:ℝ) (4636913251/25000000000000:ℝ) (-21594213178210310429903/6250000000000000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_284
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0853).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_284 :
    (∫ x in (71/128:ℝ)..(285/512:ℝ), x^12*thetaFirstMode x) ≤ (319636584539139/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (71/128:ℝ) (285/512:ℝ)
    (19233555281/100000000000000:ℝ) (18547709471/100000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_284 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0853).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_285 :
    (321468120964751/1000000000000000000000000:ℝ) ≤ ∫ x in (285/512:ℝ)..(143/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-172701971547548303234881112397/50000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 12 (285/512:ℝ) (143/256:ℝ)) ≤
      thetaFirstModeFirst (436184715072406009365/783576290780361661952:ℝ)*(thetaPowerMass 13 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 12 (285/512:ℝ) (143/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0432.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (285/512:ℝ) (143/256:ℝ)
    (436184715072406009365/783576290780361661952:ℝ) (927067013/5000000000000:ℝ) (-172701971547548303234881112397/50000000000000000000000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_285
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0857).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_285 :
    (∫ x in (285/512:ℝ)..(143/256:ℝ), x^12*thetaFirstMode x) ≤ (160735423779111/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (285/512:ℝ) (143/256:ℝ)
    (18547709471/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_285 (thetaFirstMode_refined_node_0853).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_286 :
    (323218895539481/1000000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(287/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-2023448003795163738991/625000000000000000000000:ℝ)*(thetaPowerMass 13 (143/256:ℝ) (287/512:ℝ)-(287/512:ℝ)*thetaPowerMass 12 (143/256:ℝ) (287/512:ℝ)) ≤
      thetaFirstModeFirst (287/512:ℝ)*(thetaPowerMass 13 (143/256:ℝ) (287/512:ℝ)-(287/512:ℝ)*thetaPowerMass 12 (143/256:ℝ) (287/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0434.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (143/256:ℝ) (287/512:ℝ)
    (287/512:ℝ) (215511281/1250000000000:ℝ) (-2023448003795163738991/625000000000000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_286
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0859).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_286 :
    (∫ x in (143/256:ℝ)..(287/512:ℝ), x^12*thetaFirstMode x) ≤ (40402597272703/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (143/256:ℝ) (287/512:ℝ)
    (17883710043/100000000000000:ℝ) (862047769/5000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_286 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0859).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_287 :
    (162441111075051/500000000000000000000000:ℝ) ≤ ∫ x in (287/512:ℝ)..(9/16:ℝ), x^12*thetaFirstMode x := by
  have hd : (-32365453507474057315971426559/10000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 12 (287/512:ℝ) (9/16:ℝ)) ≤
      thetaFirstModeFirst (2322591790558180904343/4143304883478902172160:ℝ)*(thetaPowerMass 13 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 12 (287/512:ℝ) (9/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0435.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (287/512:ℝ) (9/16:ℝ)
    (2322591790558180904343/4143304883478902172160:ℝ) (17235028451/100000000000000:ℝ) (-32365453507474057315971426559/10000000000000000000000000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_287
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0863).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_287 :
    (∫ x in (287/512:ℝ)..(9/16:ℝ), x^12*thetaFirstMode x) ≤ (324885035087797/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (287/512:ℝ) (9/16:ℝ)
    (862047769/5000000000000:ℝ) (2077357167/12500000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_287 (thetaFirstMode_refined_node_0859).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
