import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature08
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative12
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative13

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_256 :
    (965051706470914757/1000000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(257/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-20814002309616788849570414031/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/2:ℝ) (257/512:ℝ)-(1/2:ℝ)*thetaPowerMass 0 (1/2:ℝ) (257/512:ℝ)) ≤
      thetaFirstModeFirst (1/2:ℝ)*(thetaPowerMass 1 (1/2:ℝ) (257/512:ℝ)-(1/2:ℝ)*thetaPowerMass 0 (1/2:ℝ) (257/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0388.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/2:ℝ) (257/512:ℝ)
    (1/2:ℝ) (25108094913/50000000000000:ℝ) (-20814002309616788849570414031/2500000000000000000000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_256
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0768).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_256 :
    (∫ x in (1/2:ℝ)..(257/512:ℝ), x^0*thetaFirstMode x) ≤ (482528951286473431/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/2:ℝ) (257/512:ℝ)
    (50216326329/100000000000000:ℝ) (9722621481/20000000000000:ℝ) (118035744506376289043701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_256 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0769).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_257 :
    (29193142241682389/31250000000000000000000:ℝ) ≤ ∫ x in (257/512:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-80899005738204708052923487899/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 0 (257/512:ℝ) (129/256:ℝ)) ≤
      thetaFirstModeFirst (859903185597392841993/1713045360379148700160:ℝ)*(thetaPowerMass 1 (257/512:ℝ) (129/256:ℝ)-(859903185597392841993/1713045360379148700160:ℝ)*thetaPowerMass 0 (257/512:ℝ) (129/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0390.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (257/512:ℝ) (129/256:ℝ)
    (859903185597392841993/1713045360379148700160:ℝ) (3037286171/6250000000000:ℝ) (-80899005738204708052923487899/10000000000000000000000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_257
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0773).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_257 :
    (∫ x in (257/512:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x) ≤ (7473492013811613/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (257/512:ℝ) (129/256:ℝ)
    (9722621481/20000000000000:ℝ) (47054917301/100000000000000:ℝ) (3601332245964550280819/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_257 (thetaFirstMode_refined_node_0769).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_258 :
    (5651113827763459/6250000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(259/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15728977823405558655240299919/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (129/256:ℝ) (259/512:ℝ)-(129/256:ℝ)*thetaPowerMass 0 (129/256:ℝ) (259/512:ℝ)) ≤
      thetaFirstModeFirst (129/256:ℝ)*(thetaPowerMass 1 (129/256:ℝ) (259/512:ℝ)-(129/256:ℝ)*thetaPowerMass 0 (129/256:ℝ) (259/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0391.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (129/256:ℝ) (259/512:ℝ)
    (129/256:ℝ) (47054788389/100000000000000:ℝ) (-15728977823405558655240299919/2000000000000000000000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_258
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0774).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_258 :
    (∫ x in (129/256:ℝ)..(259/512:ℝ), x^0*thetaFirstMode x) ≤ (113023016636570153/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (129/256:ℝ) (259/512:ℝ)
    (47054917301/100000000000000:ℝ) (45540690511/100000000000000:ℝ) (14062551017188329061533/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_258 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0775).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_259 :
    (875024491810822627/1000000000000000000000000:ℝ) ≤ ∫ x in (259/512:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-190995732180727575413904541487/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 0 (259/512:ℝ) (65/128:ℝ)) ≤
      thetaFirstModeFirst (922036494355905427191/1822640620152625231360:ℝ)*(thetaPowerMass 1 (259/512:ℝ) (65/128:ℝ)-(922036494355905427191/1822640620152625231360:ℝ)*thetaPowerMass 0 (259/512:ℝ) (65/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0393.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (259/512:ℝ) (65/128:ℝ)
    (922036494355905427191/1822640620152625231360:ℝ) (5690650121/12500000000000:ℝ) (-190995732180727575413904541487/25000000000000000000000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_259
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0779).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_259 :
    (∫ x in (259/512:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x) ≤ (437515087944374307/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (259/512:ℝ) (65/128:ℝ)
    (45540690511/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21961708117872834527779/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_259 (thetaFirstMode_refined_node_0775).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_260 :
    (423349365815339111/500000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(261/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-371250002749962386403365926677/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (65/128:ℝ) (261/512:ℝ)-(65/128:ℝ)*thetaPowerMass 0 (65/128:ℝ) (261/512:ℝ)) ≤
      thetaFirstModeFirst (65/128:ℝ)*(thetaPowerMass 1 (65/128:ℝ) (261/512:ℝ)-(65/128:ℝ)*thetaPowerMass 0 (65/128:ℝ) (261/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0394.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (65/128:ℝ) (261/512:ℝ)
    (65/128:ℝ) (44069259259/100000000000000:ℝ) (-371250002749962386403365926677/50000000000000000000000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_260
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0780).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_260 :
    (∫ x in (65/128:ℝ)..(261/512:ℝ), x^0*thetaFirstMode x) ≤ (211676096625703747/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (65/128:ℝ) (261/512:ℝ)
    (44069380939/100000000000000:ℝ) (42639961701/100000000000000:ℝ) (107166492709281556516387/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_260 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0781).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_261 :
    (12799710420734519/15625000000000000000000:ℝ) ≤ ∫ x in (261/512:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-180274491621043331871067780681/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 0 (261/512:ℝ) (131/256:ℝ)) ≤
      thetaFirstModeFirst (988128929174544916209/1938322640485932981760:ℝ)*(thetaPowerMass 1 (261/512:ℝ) (131/256:ℝ)-(988128929174544916209/1938322640485932981760:ℝ)*thetaPowerMass 0 (261/512:ℝ) (131/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0396.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (261/512:ℝ) (131/256:ℝ)
    (988128929174544916209/1938322640485932981760:ℝ) (42625452771/100000000000000:ℝ) (-180274491621043331871067780681/25000000000000000000000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_261
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0785).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_261 :
    (∫ x in (261/512:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x) ≤ (819186894508351579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (261/512:ℝ) (131/256:ℝ)
    (42639961701/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (20914744888545789878073/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_261 (thetaFirstMode_refined_node_0781).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_262 :
    (396226400059496897/500000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(263/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-35031737807591648008498859663/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (131/256:ℝ) (263/512:ℝ)-(131/256:ℝ)*thetaPowerMass 0 (131/256:ℝ) (263/512:ℝ)) ≤
      thetaFirstModeFirst (131/256:ℝ)*(thetaPowerMass 1 (131/256:ℝ) (263/512:ℝ)-(131/256:ℝ)*thetaPowerMass 0 (131/256:ℝ) (263/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0397.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (131/256:ℝ) (263/512:ℝ)
    (131/256:ℝ) (20625655061/50000000000000:ℝ) (-35031737807591648008498859663/5000000000000000000000000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_262
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0786).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_262 :
    (∫ x in (131/256:ℝ)..(263/512:ℝ), x^0*thetaFirstMode x) ≤ (792458198650908139/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (131/256:ℝ) (263/512:ℝ)
    (8250284983/20000000000000:ℝ) (79805563/200000000000:ℝ) (10202969245493449972949/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_262 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0787).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_263 :
    (766493982576063/1000000000000000000000:ℝ) ≤ ∫ x in (263/512:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-170064337945951876666314350811/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 0 (263/512:ℝ) (33/64:ℝ)) ≤
      thetaFirstModeFirst (1058399498889348955407/2060378912321919132160:ℝ)*(thetaPowerMass 1 (263/512:ℝ) (33/64:ℝ)-(1058399498889348955407/2060378912321919132160:ℝ)*thetaPowerMass 0 (263/512:ℝ) (33/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0399.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (263/512:ℝ) (33/64:ℝ)
    (1058399498889348955407/2060378912321919132160:ℝ) (39889197553/100000000000000:ℝ) (-170064337945951876666314350811/25000000000000000000000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_263
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0791).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_263 :
    (∫ x in (263/512:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x) ≤ (383249581407321081/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (263/512:ℝ) (33/64:ℝ)
    (79805563/200000000000:ℝ) (9648265241/25000000000000:ℝ) (99533850368687691784589/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_263 (thetaFirstMode_refined_node_0787).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_264 :
    (370642930278659047/500000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(265/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-41298509106952788516264014647/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (33/64:ℝ) (265/512:ℝ)-(33/64:ℝ)*thetaPowerMass 0 (33/64:ℝ) (265/512:ℝ)) ≤
      thetaFirstModeFirst (33/64:ℝ)*(thetaPowerMass 1 (33/64:ℝ) (265/512:ℝ)-(33/64:ℝ)*thetaPowerMass 0 (33/64:ℝ) (265/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0400.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (33/64:ℝ) (265/512:ℝ)
    (33/64:ℝ) (19296476363/50000000000000:ℝ) (-41298509106952788516264014647/6250000000000000000000000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_264
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0792).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_264 :
    (∫ x in (33/64:ℝ)..(265/512:ℝ), x^0*thetaFirstMode x) ≤ (29651640478386397/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/64:ℝ) (265/512:ℝ)
    (9648265241/25000000000000:ℝ) (46651639/125000000000:ℝ) (24271412255091984402549/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_264 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0793).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_265 :
    (5600081142049089/7812500000000000000000:ℝ) ≤ ∫ x in (265/512:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-64138495771534099639337229171/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 0 (265/512:ℝ) (133/256:ℝ)) ≤
      thetaFirstModeFirst (226615503159325427085/437821630895601469952:ℝ)*(thetaPowerMass 1 (265/512:ℝ) (133/256:ℝ)-(226615503159325427085/437821630895601469952:ℝ)*thetaPowerMass 0 (265/512:ℝ) (133/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0402.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (265/512:ℝ) (133/256:ℝ)
    (226615503159325427085/437821630895601469952:ℝ) (7461719873/20000000000000:ℝ) (-64138495771534099639337229171/10000000000000000000000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_265
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0797).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_265 :
    (∫ x in (265/512:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x) ≤ (179203832012400233/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (265/512:ℝ) (133/256:ℝ)
    (46651639/125000000000:ℝ) (36086598273/100000000000000:ℝ) (47342268350709783552843/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_265 (thetaFirstMode_refined_node_0793).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_266 :
    (138609826536011667/200000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(267/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-311424439556492252570717187369/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (133/256:ℝ) (267/512:ℝ)-(133/256:ℝ)*thetaPowerMass 0 (133/256:ℝ) (267/512:ℝ)) ≤
      thetaFirstModeFirst (133/256:ℝ)*(thetaPowerMass 1 (133/256:ℝ) (267/512:ℝ)-(133/256:ℝ)*thetaPowerMass 0 (133/256:ℝ) (267/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0403.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (133/256:ℝ) (267/512:ℝ)
    (133/256:ℝ) (36086496271/100000000000000:ℝ) (-311424439556492252570717187369/50000000000000000000000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_266
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0798).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_266 :
    (∫ x in (133/256:ℝ)..(267/512:ℝ), x^0*thetaFirstMode x) ≤ (693054045940158587/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (133/256:ℝ) (267/512:ℝ)
    (36086598273/100000000000000:ℝ) (8722001553/25000000000000:ℝ) (18465991880377238857269/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_266 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0799).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_267 :
    (167496184260514369/250000000000000000000000:ℝ) ≤ ∫ x in (267/512:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-151101592043496668191229170167/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 0 (267/512:ℝ) (67/128:ℝ)) ≤
      thetaFirstModeFirst (1212402996478512506943/2324820661745853468160:ℝ)*(thetaPowerMass 1 (267/512:ℝ) (67/128:ℝ)-(1212402996478512506943/2324820661745853468160:ℝ)*thetaPowerMass 0 (267/512:ℝ) (67/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0405.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (267/512:ℝ) (67/128:ℝ)
    (1212402996478512506943/2324820661745853468160:ℝ) (4359514533/12500000000000:ℝ) (-151101592043496668191229170167/25000000000000000000000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_267
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0803).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_267 :
    (∫ x in (267/512:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x) ≤ (334994724633802019/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (267/512:ℝ) (67/128:ℝ)
    (8722001553/25000000000000:ℝ) (33724636797/100000000000000:ℝ) (11252670131103088141523/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_267 (thetaFirstMode_refined_node_0799).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_268 :
    (323799741198285827/500000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(269/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-293389690549900393466698630191/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (67/128:ℝ) (269/512:ℝ)-(67/128:ℝ)*thetaPowerMass 0 (67/128:ℝ) (269/512:ℝ)) ≤
      thetaFirstModeFirst (67/128:ℝ)*(thetaPowerMass 1 (67/128:ℝ) (269/512:ℝ)-(67/128:ℝ)*thetaPowerMass 0 (67/128:ℝ) (269/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0406.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (67/128:ℝ) (269/512:ℝ)
    (67/128:ℝ) (33724540723/100000000000000:ℝ) (-293389690549900393466698630191/50000000000000000000000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_268
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0804).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_268 :
    (∫ x in (67/128:ℝ)..(269/512:ℝ), x^0*thetaFirstMode x) ≤ (323802083149122349/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (67/128:ℝ) (269/512:ℝ)
    (33724636797/100000000000000:ℝ) (32595609347/100000000000000:ℝ) (3510327349971007052127/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_268 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0805).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_269 :
    (625876674698651723/1000000000000000000000000:ℝ) ≤ ∫ x in (269/512:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2846244469767174472472746191/500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 0 (269/512:ℝ) (135/256:ℝ)) ≤
      thetaFirstModeFirst (1296627075007226251641/2467838661023287068160:ℝ)*(thetaPowerMass 1 (269/512:ℝ) (135/256:ℝ)-(1296627075007226251641/2467838661023287068160:ℝ)*thetaPowerMass 0 (269/512:ℝ) (135/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0408.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (269/512:ℝ) (135/256:ℝ)
    (1296627075007226251641/2467838661023287068160:ℝ) (32584493593/100000000000000:ℝ) (-2846244469767174472472746191/500000000000000000000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_269
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0809).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_269 :
    (∫ x in (269/512:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x) ≤ (39117572862949171/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (269/512:ℝ) (135/256:ℝ)
    (32595609347/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (42769934010901444689157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_269 (thetaFirstMode_refined_node_0805).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_270 :
    (4838394318464219/8000000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(271/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5524958105821141429457854611/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (135/256:ℝ) (271/512:ℝ)-(135/256:ℝ)*thetaPowerMass 0 (135/256:ℝ) (271/512:ℝ)) ≤
      thetaFirstModeFirst (135/256:ℝ)*(thetaPowerMass 1 (135/256:ℝ) (271/512:ℝ)-(135/256:ℝ)*thetaPowerMass 0 (135/256:ℝ) (271/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0409.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (135/256:ℝ) (271/512:ℝ)
    (135/256:ℝ) (3149997007/10000000000000:ℝ) (-5524958105821141429457854611/1000000000000000000000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_270
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0810).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_270 :
    (∫ x in (135/256:ℝ)..(271/512:ℝ), x^0*thetaFirstMode x) ≤ (302401876444372083/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (135/256:ℝ) (271/512:ℝ)
    (3150006051/10000000000000:ℝ) (7609286011/25000000000000:ℝ) (41682926509208098725461/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_270 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0811).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_271 :
    (116870257300615929/200000000000000000000000:ℝ) ≤ ∫ x in (271/512:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1339603963847844488296349709/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 0 (271/512:ℝ) (17/32:ℝ)) ≤
      thetaFirstModeFirst (1386012428812593345159/2618496675601163368960:ℝ)*(thetaPowerMass 1 (271/512:ℝ) (17/32:ℝ)-(1386012428812593345159/2618496675601163368960:ℝ)*thetaPowerMass 0 (271/512:ℝ) (17/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0411.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (271/512:ℝ) (17/32:ℝ)
    (1386012428812593345159/2618496675601163368960:ℝ) (950836163/3125000000000:ℝ) (-1339603963847844488296349709/250000000000000000000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_271
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0815).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_271 :
    (∫ x in (271/512:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x) ≤ (584355564796128829/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (271/512:ℝ) (17/32:ℝ)
    (7609286011/25000000000000:ℝ) (2940603061/10000000000000:ℝ) (10154447096528143514649/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_271 (thetaFirstMode_refined_node_0811).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_272 :
    (112903263229325607/200000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(273/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6499100901141437094665873439/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (17/32:ℝ) (273/512:ℝ)-(17/32:ℝ)*thetaPowerMass 0 (17/32:ℝ) (273/512:ℝ)) ≤
      thetaFirstModeFirst (17/32:ℝ)*(thetaPowerMass 1 (17/32:ℝ) (273/512:ℝ)-(17/32:ℝ)*thetaPowerMass 0 (17/32:ℝ) (273/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0412.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (17/32:ℝ) (273/512:ℝ)
    (17/32:ℝ) (367574319/1250000000000:ℝ) (-6499100901141437094665873439/1250000000000000000000000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_272
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0816).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_272 :
    (∫ x in (17/32:ℝ)..(273/512:ℝ), x^0*thetaFirstMode x) ≤ (56452056677139619/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/32:ℝ) (273/512:ℝ)
    (2940603061/10000000000000:ℝ) (887684611/3125000000000:ℝ) (79148476410576933329473/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_272 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0817).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_273 :
    (545278974215792083/1000000000000000000000000:ℝ) ≤ ∫ x in (273/512:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-126028810762700441259518644517/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 0 (273/512:ℝ) (137/256:ℝ)) ≤
      thetaFirstModeFirst (1480833717501674392857/2777141897728678812160:ℝ)*(thetaPowerMass 1 (273/512:ℝ) (137/256:ℝ)-(1480833717501674392857/2777141897728678812160:ℝ)*thetaPowerMass 0 (273/512:ℝ) (137/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0414.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (273/512:ℝ) (137/256:ℝ)
    (1480833717501674392857/2777141897728678812160:ℝ) (28396206701/100000000000000:ℝ) (-126028810762700441259518644517/25000000000000000000000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_273
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0821).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_273 :
    (∫ x in (273/512:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x) ≤ (109056609561405271/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (273/512:ℝ) (137/256:ℝ)
    (887684611/3125000000000:ℝ) (27435978683/100000000000000:ℝ) (602374909194395511409/7812500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_273 (thetaFirstMode_refined_node_0817).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_274 :
    (4212988561792159/8000000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(275/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-244503912141744493191631888341/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (137/256:ℝ) (275/512:ℝ)-(137/256:ℝ)*thetaPowerMass 0 (137/256:ℝ) (275/512:ℝ)) ≤
      thetaFirstModeFirst (137/256:ℝ)*(thetaPowerMass 1 (137/256:ℝ) (275/512:ℝ)-(137/256:ℝ)*thetaPowerMass 0 (137/256:ℝ) (275/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0415.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (137/256:ℝ) (275/512:ℝ)
    (137/256:ℝ) (27435898671/100000000000000:ℝ) (-244503912141744493191631888341/50000000000000000000000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_274
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0822).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_274 :
    (∫ x in (137/256:ℝ)..(275/512:ℝ), x^0*thetaFirstMode x) ≤ (526627616495393923/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (137/256:ℝ) (275/512:ℝ)
    (27435978683/100000000000000:ℝ) (13247732037/50000000000000:ℝ) (37550774327671734593993/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_274 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0823).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_275 :
    (508535320077750901/1000000000000000000000000:ℝ) ≤ ∫ x in (275/512:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-237001211691605884081506846923/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 0 (275/512:ℝ) (69/128:ℝ)) ≤
      thetaFirstModeFirst (316275606984747764475/588826913916326538752:ℝ)*(thetaPowerMass 1 (275/512:ℝ) (69/128:ℝ)-(316275606984747764475/588826913916326538752:ℝ)*thetaPowerMass 0 (275/512:ℝ) (69/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0417.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (275/512:ℝ) (69/128:ℝ)
    (316275606984747764475/588826913916326538752:ℝ) (26486408473/100000000000000:ℝ) (-237001211691605884081506846923/50000000000000000000000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_275
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0827).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_275 :
    (∫ x in (275/512:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x) ≤ (63567399603676613/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (275/512:ℝ) (69/128:ℝ)
    (13247732037/50000000000000:ℝ) (5116719967/20000000000000:ℝ) (73140592990518585524131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_275 (thetaFirstMode_refined_node_0823).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_276 :
    (122749793533590257/250000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(277/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-45966848552307114275898296539/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (69/128:ℝ) (277/512:ℝ)-(69/128:ℝ)*thetaPowerMass 0 (69/128:ℝ) (277/512:ℝ)) ≤
      thetaFirstModeFirst (69/128:ℝ)*(thetaPowerMass 1 (69/128:ℝ) (277/512:ℝ)-(69/128:ℝ)*thetaPowerMass 0 (69/128:ℝ) (277/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0418.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (69/128:ℝ) (277/512:ℝ)
    (69/128:ℝ) (159897029/625000000000:ℝ) (-45966848552307114275898296539/10000000000000000000000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_276
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0828).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_276 :
    (∫ x in (69/128:ℝ)..(277/512:ℝ), x^0*thetaFirstMode x) ≤ (3928024191791179/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (69/128:ℝ) (277/512:ℝ)
    (5116719967/20000000000000:ℝ) (24699637901/100000000000000:ℝ) (14244111417319293862651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_276 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0829).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_277 :
    (474000952469920303/1000000000000000000000000:ℝ) ≤ ∫ x in (277/512:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4454374444447249812042543297/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 0 (277/512:ℝ) (139/256:ℝ)) ≤
      thetaFirstModeFirst (1687945374778197279393/3119848372759046172160:ℝ)*(thetaPowerMass 1 (277/512:ℝ) (139/256:ℝ)-(1687945374778197279393/3119848372759046172160:ℝ)*thetaPowerMass 0 (277/512:ℝ) (139/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0420.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (277/512:ℝ) (139/256:ℝ)
    (1687945374778197279393/3119848372759046172160:ℝ) (24691188943/100000000000000:ℝ) (-4454374444447249812042543297/1000000000000000000000000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_277
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0833).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_277 :
    (∫ x in (277/512:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x) ≤ (29625290004137831/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (277/512:ℝ) (139/256:ℝ)
    (24699637901/100000000000000:ℝ) (2980355727/12500000000000:ℝ) (69340876828747818639333/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_277 (thetaFirstMode_refined_node_0829).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_278 :
    (457526228928681419/1000000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(279/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1686895456485791366063307927/390625000000000000000000000000:ℝ)*(thetaPowerMass 1 (139/256:ℝ) (279/512:ℝ)-(139/256:ℝ)*thetaPowerMass 0 (139/256:ℝ) (279/512:ℝ)) ≤
      thetaFirstModeFirst (139/256:ℝ)*(thetaPowerMass 1 (139/256:ℝ) (279/512:ℝ)-(139/256:ℝ)*thetaPowerMass 0 (139/256:ℝ) (279/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0421.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (139/256:ℝ) (279/512:ℝ)
    (139/256:ℝ) (5960693797/25000000000000:ℝ) (-1686895456485791366063307927/390625000000000000000000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_278
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0834).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_278 :
    (∫ x in (139/256:ℝ)..(279/512:ℝ), x^0*thetaFirstMode x) ≤ (457529890026660777/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (139/256:ℝ) (279/512:ℝ)
    (2980355727/12500000000000:ℝ) (575312663/2500000000000:ℝ) (67500988483814460076399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_278 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0835).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_279 :
    (220780705725052681/500000000000000000000000:ℝ) ≤ ∫ x in (279/512:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-209178193349719400826863010881/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 0 (279/512:ℝ) (35/64:ℝ)) ≤
      thetaFirstModeFirst (1800849110067536394591/3304670826434478952960:ℝ)*(thetaPowerMass 1 (279/512:ℝ) (35/64:ℝ)-(1800849110067536394591/3304670826434478952960:ℝ)*thetaPowerMass 0 (279/512:ℝ) (35/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0423.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (279/512:ℝ) (35/64:ℝ)
    (1800849110067536394591/3304670826434478952960:ℝ) (5751156907/25000000000000:ℝ) (-209178193349719400826863010881/50000000000000000000000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_279
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0839).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_279 :
    (∫ x in (279/512:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x) ≤ (441564917349438573/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (279/512:ℝ) (35/64:ℝ)
    (575312663/2500000000000:ℝ) (22207918131/100000000000000:ℝ) (16425082227878102517147/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_279 (thetaFirstMode_refined_node_0835).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_280 :
    (426092680049561499/1000000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(281/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-101368755551022874061675919489/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (35/64:ℝ) (281/512:ℝ)-(35/64:ℝ)*thetaPowerMass 0 (35/64:ℝ) (281/512:ℝ)) ≤
      thetaFirstModeFirst (35/64:ℝ)*(thetaPowerMass 1 (35/64:ℝ) (281/512:ℝ)-(35/64:ℝ)*thetaPowerMass 0 (35/64:ℝ) (281/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0424.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (35/64:ℝ) (281/512:ℝ)
    (35/64:ℝ) (2220785183/10000000000000:ℝ) (-101368755551022874061675919489/25000000000000000000000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_280
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0840).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_280 :
    (∫ x in (35/64:ℝ)..(281/512:ℝ), x^0*thetaFirstMode x) ≤ (426096159903235041/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/64:ℝ) (281/512:ℝ)
    (22207918131/100000000000000:ℝ) (21428393733/100000000000000:ℝ) (63938335742076520490131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_280 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0841).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_281 :
    (205553507131843921/500000000000000000000000:ℝ) ≤ ∫ x in (281/512:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4908713650861315539022996177/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 0 (281/512:ℝ) (141/256:ℝ)) ≤
      thetaFirstModeFirst (1920416486701757070609/3499003694289312924160:ℝ)*(thetaPowerMass 1 (281/512:ℝ) (141/256:ℝ)-(1920416486701757070609/3499003694289312924160:ℝ)*thetaPowerMass 0 (281/512:ℝ) (141/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0426.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (281/512:ℝ) (141/256:ℝ)
    (1920416486701757070609/3499003694289312924160:ℝ) (21421050267/100000000000000:ℝ) (-4908713650861315539022996177/1250000000000000000000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_281
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0845).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_281 :
    (∫ x in (281/512:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x) ≤ (41111034574167659/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (281/512:ℝ) (141/256:ℝ)
    (21428393733/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (2488577903967947656307/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_281 (thetaFirstMode_refined_node_0841).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_282 :
    (198295591504482321/500000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(283/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-38049654596748787736749519491/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (141/256:ℝ) (283/512:ℝ)-(141/256:ℝ)*thetaPowerMass 0 (141/256:ℝ) (283/512:ℝ)) ≤
      thetaFirstModeFirst (141/256:ℝ)*(thetaPowerMass 1 (141/256:ℝ) (283/512:ℝ)-(141/256:ℝ)*thetaPowerMass 0 (141/256:ℝ) (283/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0427.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (141/256:ℝ) (283/512:ℝ)
    (141/256:ℝ) (4134639791/20000000000000:ℝ) (-38049654596748787736749519491/10000000000000000000000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_282
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0846).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_282 :
    (∫ x in (141/256:ℝ)..(283/512:ℝ), x^0*thetaFirstMode x) ≤ (396594488894234721/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (141/256:ℝ) (283/512:ℝ)
    (20673261159/100000000000000:ℝ) (19941862777/100000000000000:ℝ) (12105620852408334193683/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_282 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0847).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_283 :
    (382532721156770741/1000000000000000000000000:ℝ) ≤ ∫ x in (283/512:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-18419958018692515473673247019/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 0 (283/512:ℝ) (71/128:ℝ)) ≤
      thetaFirstModeFirst (2046989131565308077807/3703263400356200988160:ℝ)*(thetaPowerMass 1 (283/512:ℝ) (71/128:ℝ)-(2046989131565308077807/3703263400356200988160:ℝ)*thetaPowerMass 0 (283/512:ℝ) (71/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0429.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (283/512:ℝ) (71/128:ℝ)
    (2046989131565308077807/3703263400356200988160:ℝ) (398700439/2000000000000:ℝ) (-18419958018692515473673247019/5000000000000000000000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_283
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0851).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_283 :
    (∫ x in (283/512:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x) ≤ (4781698565440403/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (283/512:ℝ) (71/128:ℝ)
    (19941862777/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (58878746881719483552821/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_283 (thetaFirstMode_refined_node_0847).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_284 :
    (73783793858245299/200000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(285/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-44606283514090664598901058553/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (71/128:ℝ) (285/512:ℝ)-(71/128:ℝ)*thetaPowerMass 0 (71/128:ℝ) (285/512:ℝ)) ≤
      thetaFirstModeFirst (71/128:ℝ)*(thetaPowerMass 1 (71/128:ℝ) (285/512:ℝ)-(71/128:ℝ)*thetaPowerMass 0 (71/128:ℝ) (285/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0430.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (71/128:ℝ) (285/512:ℝ)
    (71/128:ℝ) (3846699391/20000000000000:ℝ) (-44606283514090664598901058553/12500000000000000000000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_284
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0852).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_284 :
    (∫ x in (71/128:ℝ)..(285/512:ℝ), x^0*thetaFirstMode x) ≤ (92230527073572681/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (71/128:ℝ) (285/512:ℝ)
    (19233555281/100000000000000:ℝ) (18547709471/100000000000000:ℝ) (57265818141404537455609/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_284 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0853).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_285 :
    (177869000747903493/500000000000000000000000:ℝ) ≤ ∫ x in (285/512:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-172701971547548303234881112397/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 0 (285/512:ℝ) (143/256:ℝ)) ≤
      thetaFirstModeFirst (436184715072406009365/783576290780361661952:ℝ)*(thetaPowerMass 1 (285/512:ℝ) (143/256:ℝ)-(436184715072406009365/783576290780361661952:ℝ)*thetaPowerMass 0 (285/512:ℝ) (143/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0432.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (285/512:ℝ) (143/256:ℝ)
    (436184715072406009365/783576290780361661952:ℝ) (927067013/5000000000000:ℝ) (-172701971547548303234881112397/50000000000000000000000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_285
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0857).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_285 :
    (∫ x in (285/512:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x) ≤ (88935251264247887/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (285/512:ℝ) (143/256:ℝ)
    (18547709471/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (6961095306246018997793/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_285 (thetaFirstMode_refined_node_0853).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_286 :
    (171488856451648277/500000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(287/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-41809799623488027101866026693/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (143/256:ℝ) (287/512:ℝ)-(143/256:ℝ)*thetaPowerMass 0 (143/256:ℝ) (287/512:ℝ)) ≤
      thetaFirstModeFirst (143/256:ℝ)*(thetaPowerMass 1 (143/256:ℝ) (287/512:ℝ)-(143/256:ℝ)*thetaPowerMass 0 (143/256:ℝ) (287/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0433.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (143/256:ℝ) (287/512:ℝ)
    (143/256:ℝ) (3576731077/20000000000000:ℝ) (-41809799623488027101866026693/12500000000000000000000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_286
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0858).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_286 :
    (∫ x in (143/256:ℝ)..(287/512:ℝ), x^0*thetaFirstMode x) ≤ (68596138374595149/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (143/256:ℝ) (287/512:ℝ)
    (17883710043/100000000000000:ℝ) (862047769/5000000000000:ℝ) (54147026108292183625617/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_286 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0859).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_287 :
    (165313350315575587/500000000000000000000000:ℝ) ≤ ∫ x in (287/512:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-32365453507474057315971426559/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 0 (287/512:ℝ) (9/16:ℝ)) ≤
      thetaFirstModeFirst (2322591790558180904343/4143304883478902172160:ℝ)*(thetaPowerMass 1 (287/512:ℝ) (9/16:ℝ)-(2322591790558180904343/4143304883478902172160:ℝ)*thetaPowerMass 0 (287/512:ℝ) (9/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0435.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (287/512:ℝ) (9/16:ℝ)
    (2322591790558180904343/4143304883478902172160:ℝ) (17235028451/100000000000000:ℝ) (-32365453507474057315971426559/10000000000000000000000000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_287
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0863).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_287 :
    (∫ x in (287/512:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x) ≤ (330629550305440477/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (287/512:ℝ) (9/16:ℝ)
    (862047769/5000000000000:ℝ) (2077357167/12500000000000:ℝ) (52640057491119030578101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_287 (thetaFirstMode_refined_node_0859).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
