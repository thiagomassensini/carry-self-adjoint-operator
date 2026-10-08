import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature00
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative00
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative01

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_8_000 :
    (0/1:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-12407589923286773782075581/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (0/1:ℝ) (1/512:ℝ)-(1/512:ℝ)*thetaPowerMass 8 (0/1:ℝ) (1/512:ℝ)) ≤
      thetaFirstModeFirst (1/512:ℝ)*(thetaPowerMass 9 (0/1:ℝ) (1/512:ℝ)-(1/512:ℝ)*thetaPowerMass 8 (0/1:ℝ) (1/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0001.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (0/1:ℝ) (1/512:ℝ)
    (1/512:ℝ) (8545502162793/100000000000000:ℝ) (-12407589923286773782075581/25000000000000000000000000:ℝ) (1804357748072860818647303/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_000
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0001).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_000 :
    (∫ x in (0/1:ℝ)..(1/512:ℝ), x^8*thetaFirstMode x) ≤ (1/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (0/1:ℝ) (1/512:ℝ)
    (1080348662699/12500000000000:ℝ) (8545510741773/100000000000000:ℝ) (1804357748072860818647303/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0001).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_001 :
    (1/1000000000000000000000000:ℝ) ≤ ∫ x in (1/512:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3084281961820591115142466947601/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (1/512:ℝ) (1/256:ℝ)-(9/2560:ℝ)*thetaPowerMass 8 (1/512:ℝ) (1/256:ℝ)) ≤
      thetaFirstModeFirst (9/2560:ℝ)*(thetaPowerMass 9 (1/512:ℝ) (1/256:ℝ)-(9/2560:ℝ)*thetaPowerMass 8 (1/512:ℝ) (1/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0005.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (1/512:ℝ) (1/256:ℝ)
    (9/2560:ℝ) (529260934353/6250000000000:ℝ) (-3084281961820591115142466947601/6250000000000000000000000000000:ℝ) (451017805179600933402433/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_001
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0005).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_001 :
    (∫ x in (1/512:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x) ≤ (1/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/512:ℝ) (1/256:ℝ)
    (8545510741773/100000000000000:ℝ) (4224460243163/50000000000000:ℝ) (451017805179600933402433/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_001 (thetaFirstMode_refined_node_0001).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_002 :
    (73/1000000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(3/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-191115830117047295816811/390625000000000000000000:ℝ)*(thetaPowerMass 9 (1/256:ℝ) (3/512:ℝ)-(3/512:ℝ)*thetaPowerMass 8 (1/256:ℝ) (3/512:ℝ)) ≤
      thetaFirstModeFirst (3/512:ℝ)*(thetaPowerMass 9 (1/256:ℝ) (3/512:ℝ)-(3/512:ℝ)*thetaPowerMass 8 (1/256:ℝ) (3/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0007.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (1/256:ℝ) (3/512:ℝ)
    (3/512:ℝ) (1044126246807/12500000000000:ℝ) (-191115830117047295816811/390625000000000000000000:ℝ) (450913435891568441726497/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_002
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0007).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_002 :
    (∫ x in (1/256:ℝ)..(3/512:ℝ), x^8*thetaFirstMode x) ≤ (37/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/256:ℝ) (3/512:ℝ)
    (4224460243163/50000000000000:ℝ) (208825460649/2500000000000:ℝ) (450913435891568441726497/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_002 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0007).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_003 :
    (923/1000000000000000000000000:ℝ) ≤ ∫ x in (3/512:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-12178282541901429276181369128501/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (3/512:ℝ) (1/128:ℝ)-(9207/1308160:ℝ)*thetaPowerMass 8 (3/512:ℝ) (1/128:ℝ)) ≤
      thetaFirstModeFirst (9207/1308160:ℝ)*(thetaPowerMass 9 (3/512:ℝ) (1/128:ℝ)-(9207/1308160:ℝ)*thetaPowerMass 8 (3/512:ℝ) (1/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0009.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (3/512:ℝ) (1/128:ℝ)
    (9207/1308160:ℝ) (8295463900883/100000000000000:ℝ) (-12178282541901429276181369128501/25000000000000000000000000000000:ℝ) (901552761929889255164149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_003
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0011).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_003 :
    (∫ x in (3/512:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x) ≤ (231/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/512:ℝ) (1/128:ℝ)
    (208825460649/2500000000000:ℝ) (4128902200723/50000000000000:ℝ) (901552761929889255164149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_003 (thetaFirstMode_refined_node_0007).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_004 :
    (6369/1000000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(5/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1205533063161105100304469/2500000000000000000000000:ℝ)*(thetaPowerMass 9 (1/128:ℝ) (5/512:ℝ)-(5/512:ℝ)*thetaPowerMass 8 (1/128:ℝ) (5/512:ℝ)) ≤
      thetaFirstModeFirst (5/512:ℝ)*(thetaPowerMass 9 (1/128:ℝ) (5/512:ℝ)-(5/512:ℝ)*thetaPowerMass 8 (1/128:ℝ) (5/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0011.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (1/128:ℝ) (5/512:ℝ)
    (5/512:ℝ) (408163493967/5000000000000:ℝ) (-1205533063161105100304469/2500000000000000000000000:ℝ) (72097071559822197032487/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_004
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0013).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_004 :
    (∫ x in (1/128:ℝ)..(5/512:ℝ), x^8*thetaFirstMode x) ≤ (637/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/128:ℝ) (5/512:ℝ)
    (4128902200723/50000000000000:ℝ) (4081639101823/50000000000000:ℝ) (72097071559822197032487/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_004 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0013).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_005 :
    (15131/500000000000000000000000:ℝ) ≤ ∫ x in (5/512:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-12015916297805974949981445895421/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (5/512:ℝ) (3/256:ℝ)-(104445/9815552:ℝ)*thetaPowerMass 8 (5/512:ℝ) (3/256:ℝ)) ≤
      thetaFirstModeFirst (104445/9815552:ℝ)*(thetaPowerMass 9 (5/512:ℝ) (3/256:ℝ)-(104445/9815552:ℝ)*thetaPowerMass 8 (5/512:ℝ) (3/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0012.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (5/512:ℝ) (3/256:ℝ)
    (104445/9815552:ℝ) (4060569193129/50000000000000:ℝ) (-12015916297805974949981445895421/25000000000000000000000000000000:ℝ) (450404446639052573669741/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_005
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0017).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_005 :
    (∫ x in (5/512:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x) ≤ (30263/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/512:ℝ) (3/256:ℝ)
    (4081639101823/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (450404446639052573669741/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_005 (thetaFirstMode_refined_node_0013).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_006 :
    (111493/1000000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(7/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-23758786829634546915152541/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (3/256:ℝ) (7/512:ℝ)-(7/512:ℝ)*thetaPowerMass 8 (3/256:ℝ) (7/512:ℝ)) ≤
      thetaFirstModeFirst (7/512:ℝ)*(thetaPowerMass 9 (3/256:ℝ) (7/512:ℝ)-(7/512:ℝ)*thetaPowerMass 8 (3/256:ℝ) (7/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0014.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (3/256:ℝ) (7/512:ℝ)
    (7/512:ℝ) (7976280005461/100000000000000:ℝ) (-23758786829634546915152541/50000000000000000000000000:ℝ) (56271212010106046098461/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_006
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0019).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_006 :
    (∫ x in (3/256:ℝ)..(7/512:ℝ), x^8*thetaFirstMode x) ≤ (55747/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/256:ℝ) (7/512:ℝ)
    (504339973353/6250000000000:ℝ) (3988144101441/50000000000000:ℝ) (56271212010106046098461/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_006 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0019).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_007 :
    (341711/1000000000000000000000000:ℝ) ≤ ∫ x in (7/512:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-5924490061524007408140751687359/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (7/512:ℝ) (1/64:ℝ)-(8905743/620700160:ℝ)*thetaPowerMass 8 (7/512:ℝ) (1/64:ℝ)) ≤
      thetaFirstModeFirst (8905743/620700160:ℝ)*(thetaPowerMass 9 (7/512:ℝ) (1/64:ℝ)-(8905743/620700160:ℝ)*thetaPowerMass 8 (7/512:ℝ) (1/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0015.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (7/512:ℝ) (1/64:ℝ)
    (8905743/620700160:ℝ) (7944198133431/100000000000000:ℝ) (-5924490061524007408140751687359/12500000000000000000000000000000:ℝ) (1799610070272661358598833/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_007
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0023).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_007 :
    (∫ x in (7/512:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x) ≤ (341713/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/512:ℝ) (1/64:ℝ)
    (3988144101441/50000000000000:ℝ) (7883823733123/100000000000000:ℝ) (1799610070272661358598833/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_007 (thetaFirstMode_refined_node_0019).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_008 :
    (36447/40000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(9/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-11703652255037366925856809/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (1/64:ℝ) (9/512:ℝ)-(9/512:ℝ)*thetaPowerMass 8 (1/64:ℝ) (9/512:ℝ)) ≤
      thetaFirstModeFirst (9/512:ℝ)*(thetaPowerMass 9 (1/64:ℝ) (9/512:ℝ)-(9/512:ℝ)*thetaPowerMass 8 (1/64:ℝ) (9/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0017.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (1/64:ℝ) (9/512:ℝ)
    (9/512:ℝ) (7792037685867/100000000000000:ℝ) (-11703652255037366925856809/25000000000000000000000000:ℝ) (1798411952607616720394489/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_008
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0025).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_008 :
    (∫ x in (1/64:ℝ)..(9/512:ℝ), x^8*thetaFirstMode x) ≤ (911177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/64:ℝ) (9/512:ℝ)
    (7883823733123/100000000000000:ℝ) (1558409151349/20000000000000:ℝ) (1798411952607616720394489/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_008 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0025).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_009 :
    (1089453/500000000000000000000000:ℝ) ≤ ∫ x in (9/512:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2919791757717824683713562529343/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (9/512:ℝ) (5/256:ℝ)-(78453441/4328911360:ℝ)*thetaPowerMass 8 (9/512:ℝ) (5/256:ℝ)) ≤
      thetaFirstModeFirst (78453441/4328911360:ℝ)*(thetaPowerMass 9 (9/512:ℝ) (5/256:ℝ)-(78453441/4328911360:ℝ)*thetaPowerMass 8 (9/512:ℝ) (5/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0018.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (9/512:ℝ) (5/256:ℝ)
    (78453441/4328911360:ℝ) (388327499893/5000000000000:ℝ) (-2919791757717824683713562529343/6250000000000000000000000000000:ℝ) (4492711899304632377717/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_009
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0029).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_009 :
    (∫ x in (9/512:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x) ≤ (217891/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/512:ℝ) (5/256:ℝ)
    (1558409151349/20000000000000:ℝ) (1925238454167/25000000000000:ℝ) (4492711899304632377717/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_009 (thetaFirstMode_refined_node_0025).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_010 :
    (596737/125000000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(11/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1152815769726243074952243/2500000000000000000000000:ℝ)*(thetaPowerMass 9 (5/256:ℝ) (11/512:ℝ)-(11/512:ℝ)*thetaPowerMass 8 (5/256:ℝ) (11/512:ℝ)) ≤
      thetaFirstModeFirst (11/512:ℝ)*(thetaPowerMass 9 (5/256:ℝ) (11/512:ℝ)-(11/512:ℝ)*thetaPowerMass 8 (5/256:ℝ) (11/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0020.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (5/256:ℝ) (11/512:ℝ)
    (11/512:ℝ) (380526973097/5000000000000:ℝ) (-1152815769726243074952243/2500000000000000000000000:ℝ) (897814420115531328112517/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_010
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0031).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_010 :
    (∫ x in (5/256:ℝ)..(11/512:ℝ), x^8*thetaFirstMode x) ≤ (2386951/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/256:ℝ) (11/512:ℝ)
    (1925238454167/25000000000000:ℝ) (7610547406651/100000000000000:ℝ) (897814420115531328112517/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_010 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0031).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_011 :
    (1216827/125000000000000000000000:ℝ) ≤ ∫ x in (11/512:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-11507771887693290951397866871341/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (11/512:ℝ) (3/128:ℝ)-(456304959/20798901760:ℝ)*thetaPowerMass 8 (11/512:ℝ) (3/128:ℝ)) ≤
      thetaFirstModeFirst (456304959/20798901760:ℝ)*(thetaPowerMass 9 (11/512:ℝ) (3/128:ℝ)-(456304959/20798901760:ℝ)*thetaPowerMass 8 (11/512:ℝ) (3/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0021.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (11/512:ℝ) (3/128:ℝ)
    (456304959/20798901760:ℝ) (7589598806121/100000000000000:ℝ) (-11507771887693290951397866871341/25000000000000000000000000000000:ℝ) (448511140735877500700207/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_011
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0035).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_011 :
    (∫ x in (11/512:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x) ≤ (2433657/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/512:ℝ) (3/128:ℝ)
    (7610547406651/100000000000000:ℝ) (3760412985663/50000000000000:ℝ) (448511140735877500700207/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_011 (thetaFirstMode_refined_node_0031).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_012 :
    (292101/15625000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(13/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2838240005519509665945443/6250000000000000000000000:ℝ)*(thetaPowerMass 9 (3/128:ℝ) (13/512:ℝ)-(13/512:ℝ)*thetaPowerMass 8 (3/128:ℝ) (13/512:ℝ)) ≤
      thetaFirstModeFirst (13/512:ℝ)*(thetaPowerMass 9 (3/128:ℝ) (13/512:ℝ)-(13/512:ℝ)*thetaPowerMass 8 (3/128:ℝ) (13/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0023.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (3/128:ℝ) (13/512:ℝ)
    (13/512:ℝ) (7431781087363/100000000000000:ℝ) (-2838240005519509665945443/6250000000000000000000000:ℝ) (358466463367597438820199/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_012
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0037).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_012 :
    (∫ x in (3/128:ℝ)..(13/512:ℝ), x^8*thetaFirstMode x) ≤ (4673621/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/128:ℝ) (13/512:ℝ)
    (3760412985663/50000000000000:ℝ) (3715894453157/50000000000000:ℝ) (358466463367597438820199/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_012 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0037).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_013 :
    (426513/12500000000000000000000:ℝ) ≤ ∫ x in (13/512:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4534219442057475020351205984021/10000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (13/512:ℝ) (7/256:ℝ)-(1998081657/77506332160:ℝ)*thetaPowerMass 8 (13/512:ℝ) (7/256:ℝ)) ≤
      thetaFirstModeFirst (1998081657/77506332160:ℝ)*(thetaPowerMass 9 (13/512:ℝ) (7/256:ℝ)-(1998081657/77506332160:ℝ)*thetaPowerMass 8 (13/512:ℝ) (7/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0024.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (13/512:ℝ) (7/256:ℝ)
    (1998081657/77506332160:ℝ) (3707065455207/50000000000000:ℝ) (-4534219442057475020351205984021/10000000000000000000000000000000:ℝ) (895246255538171997651203/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_013
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0041).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_013 :
    (∫ x in (13/512:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x) ≤ (34121077/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/512:ℝ) (7/256:ℝ)
    (3715894453157/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (895246255538171997651203/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_013 (thetaFirstMode_refined_node_0037).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_014 :
    (29808691/500000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(15/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4471243685615504445711651/10000000000000000000000000:ℝ)*(thetaPowerMass 9 (7/256:ℝ) (15/512:ℝ)-(15/512:ℝ)*thetaPowerMass 8 (7/256:ℝ) (15/512:ℝ)) ≤
      thetaFirstModeFirst (15/512:ℝ)*(thetaPowerMass 9 (7/256:ℝ) (15/512:ℝ)-(15/512:ℝ)*thetaPowerMass 8 (7/256:ℝ) (15/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0026.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (7/256:ℝ) (15/512:ℝ)
    (15/512:ℝ) (7255757532429/100000000000000:ℝ) (-4471243685615504445711651/10000000000000000000000000:ℝ) (447131393731680061742449/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_014
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0043).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_014 :
    (∫ x in (7/256:ℝ)..(15/512:ℝ), x^8*thetaFirstMode x) ≤ (59617447/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/256:ℝ) (15/512:ℝ)
    (7343435558517/100000000000000:ℝ) (3627882613029/50000000000000:ℝ) (447131393731680061742449/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_014 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0043).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_015 :
    (50146663/500000000000000000000000:ℝ) ≤ ∫ x in (15/512:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4465177701458345224074278940219/10000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (15/512:ℝ) (1/32:ℝ)-(1424279835/48058429952:ℝ)*thetaPowerMass 8 (15/512:ℝ) (1/32:ℝ)) ≤
      thetaFirstModeFirst (1424279835/48058429952:ℝ)*(thetaPowerMass 9 (15/512:ℝ) (1/32:ℝ)-(1424279835/48058429952:ℝ)*thetaPowerMass 8 (15/512:ℝ) (1/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0027.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (15/512:ℝ) (1/32:ℝ)
    (1424279835/48058429952:ℝ) (7240585933229/100000000000000:ℝ) (-4465177701458345224074278940219/10000000000000000000000000000000:ℝ) (893215978893590504222731/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_015
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0047).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_015 :
    (∫ x in (15/512:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x) ≤ (20058687/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/512:ℝ) (1/32:ℝ)
    (3627882613029/50000000000000:ℝ) (7168777158679/100000000000000:ℝ) (893215978893590504222731/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_015 (thetaFirstMode_refined_node_0043).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_016 :
    (81607611/500000000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(17/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-687728433134963525582463/1562500000000000000000000:ℝ)*(thetaPowerMass 9 (1/32:ℝ) (17/512:ℝ)-(17/512:ℝ)*thetaPowerMass 8 (1/32:ℝ) (17/512:ℝ)) ≤
      thetaFirstModeFirst (17/512:ℝ)*(thetaPowerMass 9 (1/32:ℝ) (17/512:ℝ)-(17/512:ℝ)*thetaPowerMass 8 (1/32:ℝ) (17/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0029.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (1/32:ℝ) (17/512:ℝ)
    (17/512:ℝ) (1770615747231/25000000000000:ℝ) (-687728433134963525582463/1562500000000000000000000:ℝ) (1784212129104098141286139/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_016
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0049).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_016 :
    (∫ x in (1/32:ℝ)..(17/512:ℝ), x^8*thetaFirstMode x) ≤ (163215399/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/32:ℝ) (17/512:ℝ)
    (7168777158679/100000000000000:ℝ) (3541235278851/50000000000000:ℝ) (1784212129104098141286139/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_016 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0049).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_017 :
    (257942117/1000000000000000000000000:ℝ) ≤ ∫ x in (17/512:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-21980485586468361132529650697387/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (17/512:ℝ) (9/256:ℝ)-(21717383193/648199068160:ℝ)*thetaPowerMass 8 (17/512:ℝ) (9/256:ℝ)) ≤
      thetaFirstModeFirst (21717383193/648199068160:ℝ)*(thetaPowerMass 9 (17/512:ℝ) (9/256:ℝ)-(21717383193/648199068160:ℝ)*thetaPowerMass 8 (17/512:ℝ) (9/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0030.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (17/512:ℝ) (9/256:ℝ)
    (21717383193/648199068160:ℝ) (7069219913167/100000000000000:ℝ) (-21980485586468361132529650697387/50000000000000000000000000000000:ℝ) (222733322296030593255943/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_017
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0053).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_017 :
    (∫ x in (17/512:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x) ≤ (257942399/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (17/512:ℝ) (9/256:ℝ)
    (3541235278851/50000000000000:ℝ) (6996844576391/100000000000000:ℝ) (222733322296030593255943/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_017 (thetaFirstMode_refined_node_0049).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_018 :
    (99289109/250000000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(19/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4331858587436380298539063/10000000000000000000000000:ℝ)*(thetaPowerMass 9 (9/256:ℝ) (19/512:ℝ)-(19/512:ℝ)*thetaPowerMass 8 (9/256:ℝ) (19/512:ℝ)) ≤
      thetaFirstModeFirst (19/512:ℝ)*(thetaPowerMass 9 (9/256:ℝ) (19/512:ℝ)-(19/512:ℝ)*thetaPowerMass 8 (9/256:ℝ) (19/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0032.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (9/256:ℝ) (19/512:ℝ)
    (19/512:ℝ) (1382378175107/20000000000000:ℝ) (-4331858587436380298539063/10000000000000000000000000:ℝ) (1779395815030052136323121/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_018
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0055).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_018 :
    (∫ x in (9/256:ℝ)..(19/512:ℝ), x^8*thetaFirstMode x) ≤ (397156869/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/256:ℝ) (19/512:ℝ)
    (6996844576391/100000000000000:ℝ) (6911898319961/100000000000000:ℝ) (1779395815030052136323121/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_018 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0055).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_019 :
    (298698431/500000000000000000000000:ℝ) ≤ ∫ x in (19/512:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-86541109736915769008140376073/200000000000000000000000000000:ℝ)*(thetaPowerMass 9 (19/512:ℝ) (5/128:ℝ)-(58618940391/1568203548160:ℝ)*thetaPowerMass 8 (19/512:ℝ) (5/128:ℝ)) ≤
      thetaFirstModeFirst (58618940391/1568203548160:ℝ)*(thetaPowerMass 9 (19/512:ℝ) (5/128:ℝ)-(58618940391/1568203548160:ℝ)*thetaPowerMass 8 (19/512:ℝ) (5/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0033.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (19/512:ℝ) (5/128:ℝ)
    (58618940391/1568203548160:ℝ) (1725047079571/25000000000000:ℝ) (-86541109736915769008140376073/200000000000000000000000000000:ℝ) (1776800368486171250048647/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_019
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0059).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_019 :
    (∫ x in (19/512:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x) ≤ (597397521/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (19/512:ℝ) (5/128:ℝ)
    (6911898319961/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1776800368486171250048647/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_019 (thetaFirstMode_refined_node_0055).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_020 :
    (879901019/1000000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(21/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-21312265474576870512732363/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (5/128:ℝ) (21/512:ℝ)-(21/512:ℝ)*thetaPowerMass 8 (5/128:ℝ) (21/512:ℝ)) ≤
      thetaFirstModeFirst (21/512:ℝ)*(thetaPowerMass 9 (5/128:ℝ) (21/512:ℝ)-(21/512:ℝ)*thetaPowerMass 8 (5/128:ℝ) (21/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0035.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (5/128:ℝ) (21/512:ℝ)
    (21/512:ℝ) (6744033843673/100000000000000:ℝ) (-21312265474576870512732363/50000000000000000000000000:ℝ) (1774080787998504949871369/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_020
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0061).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_020 :
    (∫ x in (5/128:ℝ)..(21/512:ℝ), x^8*thetaFirstMode x) ≤ (439950993/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/128:ℝ) (21/512:ℝ)
    (6827630845943/100000000000000:ℝ) (3372020582139/50000000000000:ℝ) (1774080787998504949871369/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_020 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0061).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_021 :
    (79472807/62500000000000000000000:ℝ) ≤ ∫ x in (21/512:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-21290550011442000564661609608841/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (21/512:ℝ) (11/256:ℝ)-(143436821409/3476346088960:ℝ)*thetaPowerMass 8 (21/512:ℝ) (11/256:ℝ)) ≤
      thetaFirstModeFirst (143436821409/3476346088960:ℝ)*(thetaPowerMass 9 (21/512:ℝ) (11/256:ℝ)-(143436821409/3476346088960:ℝ)*thetaPowerMass 8 (21/512:ℝ) (11/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0036.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (21/512:ℝ) (11/256:ℝ)
    (143436821409/3476346088960:ℝ) (6733588693827/100000000000000:ℝ) (-21290550011442000564661609608841/50000000000000000000000000000000:ℝ) (221404705327917593722827/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_021
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0065).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_021 :
    (∫ x in (21/512:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x) ≤ (1271566329/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (21/512:ℝ) (11/256:ℝ)
    (3372020582139/50000000000000:ℝ) (666112823751/10000000000000:ℝ) (221404705327917593722827/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_021 (thetaFirstMode_refined_node_0061).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_022 :
    (361205233/200000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(23/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-10483162222833069136581091/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (11/256:ℝ) (23/512:ℝ)-(23/512:ℝ)*thetaPowerMass 8 (11/256:ℝ) (23/512:ℝ)) ≤
      thetaFirstModeFirst (23/512:ℝ)*(thetaPowerMass 9 (11/256:ℝ) (23/512:ℝ)-(23/512:ℝ)*thetaPowerMass 8 (11/256:ℝ) (23/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0038.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (11/256:ℝ) (23/512:ℝ)
    (23/512:ℝ) (3289441891889/50000000000000:ℝ) (-10483162222833069136581091/25000000000000000000000000:ℝ) (176827152117764724806041/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_022
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0067).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_022 :
    (∫ x in (11/256:ℝ)..(23/512:ℝ), x^8*thetaFirstMode x) ≤ (1806028167/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/256:ℝ) (23/512:ℝ)
    (666112823751/10000000000000:ℝ) (1644722745281/25000000000000:ℝ) (176827152117764724806041/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_022 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0067).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_023 :
    (2524876841/1000000000000000000000000:ℝ) ≤ ∫ x in (23/512:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-523663174803192504006886623081/1250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (23/512:ℝ) (3/64:ℝ)-(323819456607/7172691612160:ℝ)*thetaPowerMass 8 (23/512:ℝ) (3/64:ℝ)) ≤
      thetaFirstModeFirst (323819456607/7172691612160:ℝ)*(thetaPowerMass 9 (23/512:ℝ) (3/64:ℝ)-(323819456607/7172691612160:ℝ)*thetaPowerMass 8 (23/512:ℝ) (3/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0039.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (23/512:ℝ) (3/64:ℝ)
    (323819456607/7172691612160:ℝ) (6569483518681/100000000000000:ℝ) (-523663174803192504006886623081/1250000000000000000000000000000:ℝ) (220647879015663931023683/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_023
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0071).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_023 :
    (∫ x in (23/512:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x) ≤ (2524879681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (23/512:ℝ) (3/64:ℝ)
    (1644722745281/25000000000000:ℝ) (3248664131823/50000000000000:ℝ) (220647879015663931023683/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_023 (thetaFirstMode_refined_node_0067).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_024 :
    (3479012399/1000000000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(25/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-10310782959610823944320279/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (3/64:ℝ) (25/512:ℝ)-(25/512:ℝ)*thetaPowerMass 8 (3/64:ℝ) (25/512:ℝ)) ≤
      thetaFirstModeFirst (25/512:ℝ)*(thetaPowerMass 9 (3/64:ℝ) (25/512:ℝ)-(25/512:ℝ)*thetaPowerMass 8 (3/64:ℝ) (25/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0041.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (3/64:ℝ) (25/512:ℝ)
    (25/512:ℝ) (3208215916119/50000000000000:ℝ) (-10310782959610823944320279/25000000000000000000000000:ℝ) (880986401761846692876809/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_024
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0073).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_024 :
    (∫ x in (3/64:ℝ)..(25/512:ℝ), x^8*thetaFirstMode x) ≤ (108719259/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/64:ℝ) (25/512:ℝ)
    (3248664131823/50000000000000:ℝ) (6416438906917/100000000000000:ℝ) (880986401761846692876809/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_024 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0073).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_025 :
    (4730120817/1000000000000000000000000:ℝ) ≤ ∫ x in (25/512:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-206033926439249124145660343477/500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (25/512:ℝ) (13/256:ℝ)-(136694029725/2787696138752:ℝ)*thetaPowerMass 8 (25/512:ℝ) (13/256:ℝ)) ≤
      thetaFirstModeFirst (136694029725/2787696138752:ℝ)*(thetaPowerMass 9 (25/512:ℝ) (13/256:ℝ)-(136694029725/2787696138752:ℝ)*thetaPowerMass 8 (25/512:ℝ) (13/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0042.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (25/512:ℝ) (13/256:ℝ)
    (136694029725/2787696138752:ℝ) (3203956520547/50000000000000:ℝ) (-206033926439249124145660343477/500000000000000000000000000000:ℝ) (1758641482928085514001897/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_025
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0077).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_025 :
    (∫ x in (25/512:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x) ≤ (4730126193/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (25/512:ℝ) (13/256:ℝ)
    (6416438906917/100000000000000:ℝ) (1267244337271/20000000000000:ℝ) (1758641482928085514001897/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_025 (thetaFirstMode_refined_node_0073).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_026 :
    (6352318289/1000000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(27/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2534760624729362313169221/6250000000000000000000000:ℝ)*(thetaPowerMass 9 (13/256:ℝ) (27/512:ℝ)-(27/512:ℝ)*thetaPowerMass 8 (13/256:ℝ) (27/512:ℝ)) ≤
      thetaFirstModeFirst (27/512:ℝ)*(thetaPowerMass 9 (13/256:ℝ) (27/512:ℝ)-(27/512:ℝ)*thetaPowerMass 8 (13/256:ℝ) (27/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0044.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (13/256:ℝ) (27/512:ℝ)
    (27/512:ℝ) (6256668378569/100000000000000:ℝ) (-2534760624729362313169221/6250000000000000000000000:ℝ) (877594868655878291542799/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_026
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0079).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_026 :
    (∫ x in (13/256:ℝ)..(27/512:ℝ), x^8*thetaFirstMode x) ≤ (1270465091/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/256:ℝ) (27/512:ℝ)
    (1267244337271/20000000000000:ℝ) (1955211041/31250000000:ℝ) (877594868655878291542799/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_026 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0079).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_027 :
    (8433932893/1000000000000000000000000:ℝ) ≤ ∫ x in (27/512:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2026130524034421173072393168211/5000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (27/512:ℝ) (7/128:ℝ)-(1362565468143/25744761372160:ℝ)*thetaPowerMass 8 (27/512:ℝ) (7/128:ℝ)) ≤
      thetaFirstModeFirst (1362565468143/25744761372160:ℝ)*(thetaPowerMass 9 (27/512:ℝ) (7/128:ℝ)-(1362565468143/25744761372160:ℝ)*thetaPowerMass 8 (27/512:ℝ) (7/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0045.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (27/512:ℝ) (7/128:ℝ)
    (1362565468143/25744761372160:ℝ) (6248902811683/100000000000000:ℝ) (-2026130524034421173072393168211/5000000000000000000000000000000:ℝ) (175161825295770581263389/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_027
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0083).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_027 :
    (∫ x in (27/512:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x) ≤ (8433942579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (27/512:ℝ) (7/128:ℝ)
    (1955211041/31250000000:ℝ) (6177798524727/100000000000000:ℝ) (175161825295770581263389/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_027 (thetaFirstMode_refined_node_0079).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_028 :
    (11079443351/1000000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(29/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4983993939333095022983139/12500000000000000000000000:ℝ)*(thetaPowerMass 9 (7/128:ℝ) (29/512:ℝ)-(29/512:ℝ)*thetaPowerMass 8 (7/128:ℝ) (29/512:ℝ)) ≤
      thetaFirstModeFirst (29/512:ℝ)*(thetaPowerMass 9 (7/128:ℝ) (29/512:ℝ)-(29/512:ℝ)*thetaPowerMass 8 (7/128:ℝ) (29/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0047.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (7/128:ℝ) (29/512:ℝ)
    (29/512:ℝ) (1524895768329/25000000000000:ℝ) (-4983993939333095022983139/12500000000000000000000000:ℝ) (349585547073147977842183/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_028
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0085).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_028 :
    (∫ x in (7/128:ℝ)..(29/512:ℝ), x^8*thetaFirstMode x) ≤ (2769863991/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/128:ℝ) (29/512:ℝ)
    (6177798524727/100000000000000:ℝ) (6099589904549/100000000000000:ℝ) (349585547073147977842183/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_028 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0085).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_029 :
    (2882314031/200000000000000000000000:ℝ) ≤ ∫ x in (29/512:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-796816209155865795231474753921/2000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (29/512:ℝ) (15/256:ℝ)-(2586561620841/45522720232960:ℝ)*thetaPowerMass 8 (29/512:ℝ) (15/256:ℝ)) ≤
      thetaFirstModeFirst (2586561620841/45522720232960:ℝ)*(thetaPowerMass 9 (29/512:ℝ) (15/256:ℝ)-(2586561620841/45522720232960:ℝ)*thetaPowerMass 8 (29/512:ℝ) (15/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0048.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (29/512:ℝ) (15/256:ℝ)
    (2586561620841/45522720232960:ℝ) (6092468283531/100000000000000:ℝ) (-796816209155865795231474753921/2000000000000000000000000000000:ℝ) (1744118909148945553634357/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_029
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0089).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_029 :
    (∫ x in (29/512:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x) ≤ (14411586879/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/512:ℝ) (15/256:ℝ)
    (6099589904549/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (1744118909148945553634357/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_029 (thetaFirstMode_refined_node_0085).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_030 :
    (2321691071/125000000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(31/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-489883279657990947463667/1250000000000000000000000:ℝ)*(thetaPowerMass 9 (15/256:ℝ) (31/512:ℝ)-(31/512:ℝ)*thetaPowerMass 8 (15/256:ℝ) (31/512:ℝ)) ≤
      thetaFirstModeFirst (31/512:ℝ)*(thetaPowerMass 9 (15/256:ℝ) (31/512:ℝ)-(31/512:ℝ)*thetaPowerMass 8 (15/256:ℝ) (31/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0050.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (15/256:ℝ) (31/512:ℝ)
    (31/512:ℝ) (148629120907/2500000000000:ℝ) (-489883279657990947463667/1250000000000000000000000:ℝ) (348038503580446356404579/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_030
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0091).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_030 :
    (∫ x in (15/256:ℝ)..(31/512:ℝ), x^8*thetaFirstMode x) ≤ (18573549907/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/256:ℝ) (31/512:ℝ)
    (6022048062889/100000000000000:ℝ) (2972585773397/50000000000000:ℝ) (348038503580446356404579/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_030 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0091).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_031 :
    (5932858563/250000000000000000000000:ℝ) ≤ ∫ x in (31/512:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2447602546722036932239545475457/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (31/512:ℝ) (1/16:ℝ)-(4705751134359/77506860444160:ℝ)*thetaPowerMass 8 (31/512:ℝ) (1/16:ℝ)) ≤
      thetaFirstModeFirst (4705751134359/77506860444160:ℝ)*(thetaPowerMass 9 (31/512:ℝ) (1/16:ℝ)-(4705751134359/77506860444160:ℝ)*thetaPowerMass 8 (31/512:ℝ) (1/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0051.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (31/512:ℝ) (1/16:ℝ)
    (4705751134359/77506860444160:ℝ) (2969308861029/50000000000000:ℝ) (-2447602546722036932239545475457/6250000000000000000000000000000:ℝ) (1736149324112270662297763/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_031
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0095).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_031 :
    (∫ x in (31/512:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x) ≤ (23731462083/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/512:ℝ) (1/16:ℝ)
    (2972585773397/50000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1736149324112270662297763/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_031 (thetaFirstMode_refined_node_0091).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
