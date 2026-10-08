import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature00
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative00
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative01

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_000 :
    (167853202967357334037/1000000000000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3123928630619789507/6250000000000000000:ℝ)*(thetaPowerMass 1 (0/1:ℝ) (1/512:ℝ)-(0/1:ℝ)*thetaPowerMass 0 (0/1:ℝ) (1/512:ℝ)) ≤
      thetaFirstModeFirst (0/1:ℝ)*(thetaPowerMass 1 (0/1:ℝ) (1/512:ℝ)-(0/1:ℝ)*thetaPowerMass 0 (0/1:ℝ) (1/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0000.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (0/1:ℝ) (1/512:ℝ)
    (0/1:ℝ) (4321390329403/50000000000000:ℝ) (-3123928630619789507/6250000000000000000:ℝ) (1804357748072860818647303/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_000
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0000).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/512:ℝ), x^0*thetaFirstMode x) ≤ (16785337231825068639/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (0/1:ℝ) (1/512:ℝ)
    (1080348662699/12500000000000:ℝ) (8545510741773/100000000000000:ℝ) (1804357748072860818647303/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0001).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_001 :
    (1659599552640000543/10000000000000000000000:ℝ) ≤ ∫ x in (1/512:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-154544454851433773732428733973/312500000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/512:ℝ) (1/256:ℝ)-(3/1024:ℝ)*thetaPowerMass 0 (1/512:ℝ) (1/256:ℝ)) ≤
      thetaFirstModeFirst (3/1024:ℝ)*(thetaPowerMass 1 (1/512:ℝ) (1/256:ℝ)-(3/1024:ℝ)*thetaPowerMass 0 (1/512:ℝ) (1/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0002.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/512:ℝ) (1/256:ℝ)
    (3/1024:ℝ) (8497121034577/100000000000000:ℝ) (-154544454851433773732428733973/312500000000000000000000000000:ℝ) (451017805179600933402433/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_001
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0002).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_001 :
    (∫ x in (1/512:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x) ≤ (82980061173534125387/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/512:ℝ) (1/256:ℝ)
    (8545510741773/100000000000000:ℝ) (4224460243163/50000000000000:ℝ) (451017805179600933402433/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_001 (thetaFirstMode_refined_node_0001).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_002 :
    (32816029531014447499/200000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(3/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12319509604871692689883596905413/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/256:ℝ) (3/512:ℝ)-(1/256:ℝ)*thetaPowerMass 0 (1/256:ℝ) (3/512:ℝ)) ≤
      thetaFirstModeFirst (1/256:ℝ)*(thetaPowerMass 1 (1/256:ℝ) (3/512:ℝ)-(1/256:ℝ)*thetaPowerMass 0 (1/256:ℝ) (3/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0006.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/256:ℝ) (3/512:ℝ)
    (1/256:ℝ) (8448911971117/100000000000000:ℝ) (-12319509604871692689883596905413/25000000000000000000000000000000:ℝ) (450913435891568441726497/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_002
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0006).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_002 :
    (∫ x in (1/256:ℝ)..(3/512:ℝ), x^0*thetaFirstMode x) ≤ (6563212593386434137/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/256:ℝ) (3/512:ℝ)
    (4224460243163/50000000000000:ℝ) (208825460649/2500000000000:ℝ) (450913435891568441726497/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_002 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0007).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_003 :
    (162213782433132933351/1000000000000000000000000:ℝ) ≤ ∫ x in (3/512:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12186168294080635540335707/25000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/512:ℝ) (1/128:ℝ)-(1785/260096:ℝ)*thetaPowerMass 0 (3/512:ℝ) (1/128:ℝ)) ≤
      thetaFirstModeFirst (1785/260096:ℝ)*(thetaPowerMass 1 (3/512:ℝ) (1/128:ℝ)-(1785/260096:ℝ)*thetaPowerMass 0 (3/512:ℝ) (1/128:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0008.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/512:ℝ) (1/128:ℝ)
    (1785/260096:ℝ) (8304005063483/100000000000000:ℝ) (-12186168294080635540335707/25000000000000000000000000:ℝ) (901552761929889255164149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_003
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0010).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_003 :
    (∫ x in (3/512:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x) ≤ (40553486789658548941/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/512:ℝ) (1/128:ℝ)
    (208825460649/2500000000000:ℝ) (4128902200723/50000000000000:ℝ) (901552761929889255164149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_003 (thetaFirstMode_refined_node_0007).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_004 :
    (160360850709488342673/1000000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(5/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12143373430081202768578419622793/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/128:ℝ) (5/512:ℝ)-(1/128:ℝ)*thetaPowerMass 0 (1/128:ℝ) (5/512:ℝ)) ≤
      thetaFirstModeFirst (1/128:ℝ)*(thetaPowerMass 1 (1/128:ℝ) (5/512:ℝ)-(1/128:ℝ)*thetaPowerMass 0 (1/128:ℝ) (5/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0010.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/128:ℝ) (5/512:ℝ)
    (1/128:ℝ) (4128898006789/50000000000000:ℝ) (-12143373430081202768578419622793/25000000000000000000000000000000:ℝ) (72097071559822197032487/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_004
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0012).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_004 :
    (∫ x in (1/128:ℝ)..(5/512:ℝ), x^0*thetaFirstMode x) ≤ (160361015721513107/1000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/128:ℝ) (5/512:ℝ)
    (4128902200723/50000000000000:ℝ) (4081639101823/50000000000000:ℝ) (72097071559822197032487/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_004 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0013).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_005 :
    (19815169186955349667/125000000000000000000000:ℝ) ≤ ∫ x in (5/512:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12015916297805974949981445895421/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/512:ℝ) (3/256:ℝ)-(104445/9815552:ℝ)*thetaPowerMass 0 (5/512:ℝ) (3/256:ℝ)) ≤
      thetaFirstModeFirst (104445/9815552:ℝ)*(thetaPowerMass 1 (5/512:ℝ) (3/256:ℝ)-(104445/9815552:ℝ)*thetaPowerMass 0 (5/512:ℝ) (3/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0012.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/512:ℝ) (3/256:ℝ)
    (104445/9815552:ℝ) (4060569193129/50000000000000:ℝ) (-12015916297805974949981445895421/25000000000000000000000000000000:ℝ) (450404446639052573669741/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_005
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0017).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_005 :
    (∫ x in (5/512:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x) ≤ (158521515952343086371/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/512:ℝ) (3/256:ℝ)
    (4081639101823/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (450404446639052573669741/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_005 (thetaFirstMode_refined_node_0013).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_006 :
    (156695279460138027371/1000000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(7/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1495919633275097234116146675387/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/256:ℝ) (7/512:ℝ)-(3/256:ℝ)*thetaPowerMass 0 (3/256:ℝ) (7/512:ℝ)) ≤
      thetaFirstModeFirst (3/256:ℝ)*(thetaPowerMass 1 (3/256:ℝ) (7/512:ℝ)-(3/256:ℝ)*thetaPowerMass 0 (3/256:ℝ) (7/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0013.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/256:ℝ) (7/512:ℝ)
    (3/256:ℝ) (322777252513/4000000000000:ℝ) (-1495919633275097234116146675387/3125000000000000000000000000000:ℝ) (56271212010106046098461/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_006
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0018).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_006 :
    (∫ x in (3/256:ℝ)..(7/512:ℝ), x^0*thetaFirstMode x) ≤ (31339088461828293379/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/256:ℝ) (7/512:ℝ)
    (504339973353/6250000000000:ℝ) (3988144101441/50000000000000:ℝ) (56271212010106046098461/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_006 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0019).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_007 :
    (15488262793599725681/100000000000000000000000:ℝ) ≤ ∫ x in (7/512:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5924490061524007408140751687359/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/512:ℝ) (1/64:ℝ)-(8905743/620700160:ℝ)*thetaPowerMass 0 (7/512:ℝ) (1/64:ℝ)) ≤
      thetaFirstModeFirst (8905743/620700160:ℝ)*(thetaPowerMass 1 (7/512:ℝ) (1/64:ℝ)-(8905743/620700160:ℝ)*thetaPowerMass 0 (7/512:ℝ) (1/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0015.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/512:ℝ) (1/64:ℝ)
    (8905743/620700160:ℝ) (7944198133431/100000000000000:ℝ) (-5924490061524007408140751687359/12500000000000000000000000000000:ℝ) (1799610070272661358598833/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_007
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0023).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_007 :
    (∫ x in (7/512:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x) ≤ (154882788280059527941/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/512:ℝ) (1/64:ℝ)
    (3988144101441/50000000000000:ℝ) (7883823733123/100000000000000:ℝ) (1799610070272661358598833/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_007 (thetaFirstMode_refined_node_0019).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_008 :
    (76541692847469078937/500000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(9/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9433209116631240031420315857/20000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/64:ℝ) (9/512:ℝ)-(1/64:ℝ)*thetaPowerMass 0 (1/64:ℝ) (9/512:ℝ)) ≤
      thetaFirstModeFirst (1/64:ℝ)*(thetaPowerMass 1 (1/64:ℝ) (9/512:ℝ)-(1/64:ℝ)*thetaPowerMass 0 (1/64:ℝ) (9/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0016.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/64:ℝ) (9/512:ℝ)
    (1/64:ℝ) (3941907799509/50000000000000:ℝ) (-9433209116631240031420315857/20000000000000000000000000000:ℝ) (1798411952607616720394489/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_008
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0024).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_008 :
    (∫ x in (1/64:ℝ)..(9/512:ℝ), x^0*thetaFirstMode x) ≤ (3061670927717844793/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/64:ℝ) (9/512:ℝ)
    (7883823733123/100000000000000:ℝ) (1558409151349/20000000000000:ℝ) (1798411952607616720394489/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_008 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0025).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_009 :
    (9456096872782383019/62500000000000000000000:ℝ) ≤ ∫ x in (9/512:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2919791757717824683713562529343/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (9/512:ℝ) (5/256:ℝ)-(78453441/4328911360:ℝ)*thetaPowerMass 0 (9/512:ℝ) (5/256:ℝ)) ≤
      thetaFirstModeFirst (78453441/4328911360:ℝ)*(thetaPowerMass 1 (9/512:ℝ) (5/256:ℝ)-(78453441/4328911360:ℝ)*thetaPowerMass 0 (9/512:ℝ) (5/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0018.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (9/512:ℝ) (5/256:ℝ)
    (78453441/4328911360:ℝ) (388327499893/5000000000000:ℝ) (-2919791757717824683713562529343/6250000000000000000000000000000:ℝ) (4492711899304632377717/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_009
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0029).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_009 :
    (∫ x in (9/512:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x) ≤ (37824427045510294299/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/512:ℝ) (5/256:ℝ)
    (1558409151349/20000000000000:ℝ) (1925238454167/25000000000000:ℝ) (4492711899304632377717/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_009 (thetaFirstMode_refined_node_0025).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_010 :
    (149525105722774718207/1000000000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(11/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5807943542150341312002137127447/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/256:ℝ) (11/512:ℝ)-(5/256:ℝ)*thetaPowerMass 0 (5/256:ℝ) (11/512:ℝ)) ≤
      thetaFirstModeFirst (5/256:ℝ)*(thetaPowerMass 1 (5/256:ℝ) (11/512:ℝ)-(5/256:ℝ)*thetaPowerMass 0 (5/256:ℝ) (11/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0019.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/256:ℝ) (11/512:ℝ)
    (5/256:ℝ) (3850472904461/50000000000000:ℝ) (-5807943542150341312002137127447/12500000000000000000000000000000:ℝ) (897814420115531328112517/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_010
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0030).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_010 :
    (∫ x in (5/256:ℝ)..(11/512:ℝ), x^0*thetaFirstMode x) ≤ (149525264260858250843/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/256:ℝ) (11/512:ℝ)
    (1925238454167/25000000000000:ℝ) (7610547406651/100000000000000:ℝ) (897814420115531328112517/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_010 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0031).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_011 :
    (147766048167397514029/1000000000000000000000000:ℝ) ≤ ∫ x in (11/512:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11507771887693290951397866871341/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/512:ℝ) (3/128:ℝ)-(456304959/20798901760:ℝ)*thetaPowerMass 0 (11/512:ℝ) (3/128:ℝ)) ≤
      thetaFirstModeFirst (456304959/20798901760:ℝ)*(thetaPowerMass 1 (11/512:ℝ) (3/128:ℝ)-(456304959/20798901760:ℝ)*thetaPowerMass 0 (11/512:ℝ) (3/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0021.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/512:ℝ) (3/128:ℝ)
    (456304959/20798901760:ℝ) (7589598806121/100000000000000:ℝ) (-11507771887693290951397866871341/25000000000000000000000000000000:ℝ) (448511140735877500700207/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_011
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0035).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_011 :
    (∫ x in (11/512:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x) ≤ (73883102127419541829/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/512:ℝ) (3/128:ℝ)
    (7610547406651/100000000000000:ℝ) (3760412985663/50000000000000:ℝ) (448511140735877500700207/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_011 (thetaFirstMode_refined_node_0031).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_012 :
    (730101802235123933/5000000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(13/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11440534548514085349456286997703/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/128:ℝ) (13/512:ℝ)-(3/128:ℝ)*thetaPowerMass 0 (3/128:ℝ) (13/512:ℝ)) ≤
      thetaFirstModeFirst (3/128:ℝ)*(thetaPowerMass 1 (3/128:ℝ) (13/512:ℝ)-(3/128:ℝ)*thetaPowerMass 0 (3/128:ℝ) (13/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0022.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/128:ℝ) (13/512:ℝ)
    (3/128:ℝ) (1880204522387/25000000000000:ℝ) (-11440534548514085349456286997703/25000000000000000000000000000000:ℝ) (358466463367597438820199/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_012
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0036).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_012 :
    (∫ x in (3/128:ℝ)..(13/512:ℝ), x^0*thetaFirstMode x) ≤ (146020516838087868947/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/128:ℝ) (13/512:ℝ)
    (3760412985663/50000000000000:ℝ) (3715894453157/50000000000000:ℝ) (358466463367597438820199/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_012 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0037).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_013 :
    (4509001117833057991/31250000000000000000000:ℝ) ≤ ∫ x in (13/512:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4534219442057475020351205984021/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (13/512:ℝ) (7/256:ℝ)-(1998081657/77506332160:ℝ)*thetaPowerMass 0 (13/512:ℝ) (7/256:ℝ)) ≤
      thetaFirstModeFirst (1998081657/77506332160:ℝ)*(thetaPowerMass 1 (13/512:ℝ) (7/256:ℝ)-(1998081657/77506332160:ℝ)*thetaPowerMass 0 (13/512:ℝ) (7/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0024.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (13/512:ℝ) (7/256:ℝ)
    (1998081657/77506332160:ℝ) (3707065455207/50000000000000:ℝ) (-4534219442057475020351205984021/10000000000000000000000000000000:ℝ) (895246255538171997651203/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_013
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0041).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_013 :
    (∫ x in (13/512:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x) ≤ (144288189730301737473/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/512:ℝ) (7/256:ℝ)
    (3715894453157/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (895246255538171997651203/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_013 (thetaFirstMode_refined_node_0037).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_014 :
    (142569055448648315991/1000000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(15/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-22531007849920397781980934690177/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/256:ℝ) (15/512:ℝ)-(7/256:ℝ)*thetaPowerMass 0 (7/256:ℝ) (15/512:ℝ)) ≤
      thetaFirstModeFirst (7/256:ℝ)*(thetaPowerMass 1 (7/256:ℝ) (15/512:ℝ)-(7/256:ℝ)*thetaPowerMass 0 (7/256:ℝ) (15/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0025.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/256:ℝ) (15/512:ℝ)
    (7/256:ℝ) (1835856950571/25000000000000:ℝ) (-22531007849920397781980934690177/50000000000000000000000000000000:ℝ) (447131393731680061742449/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_014
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0042).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_014 :
    (∫ x in (7/256:ℝ)..(15/512:ℝ), x^0*thetaFirstMode x) ≤ (142569209699036430121/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/256:ℝ) (15/512:ℝ)
    (7343435558517/100000000000000:ℝ) (3627882613029/50000000000000:ℝ) (447131393731680061742449/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_014 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0043).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_015 :
    (35215852681983499163/250000000000000000000000:ℝ) ≤ ∫ x in (15/512:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4465177701458345224074278940219/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/512:ℝ) (1/32:ℝ)-(1424279835/48058429952:ℝ)*thetaPowerMass 0 (15/512:ℝ) (1/32:ℝ)) ≤
      thetaFirstModeFirst (1424279835/48058429952:ℝ)*(thetaPowerMass 1 (15/512:ℝ) (1/32:ℝ)-(1424279835/48058429952:ℝ)*thetaPowerMass 0 (15/512:ℝ) (1/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0027.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/512:ℝ) (1/32:ℝ)
    (1424279835/48058429952:ℝ) (7240585933229/100000000000000:ℝ) (-4465177701458345224074278940219/10000000000000000000000000000000:ℝ) (893215978893590504222731/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_015
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0047).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_015 :
    (∫ x in (15/512:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x) ≤ (70431781281503532237/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/512:ℝ) (1/32:ℝ)
    (3627882613029/50000000000000:ℝ) (7168777158679/100000000000000:ℝ) (893215978893590504222731/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_015 (thetaFirstMode_refined_node_0043).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_016 :
    (69585540539617802029/500000000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(17/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11090845038414560830867190724973/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/32:ℝ) (17/512:ℝ)-(1/32:ℝ)*thetaPowerMass 0 (1/32:ℝ) (17/512:ℝ)) ≤
      thetaFirstModeFirst (1/32:ℝ)*(thetaPowerMass 1 (1/32:ℝ) (17/512:ℝ)-(1/32:ℝ)*thetaPowerMass 0 (1/32:ℝ) (17/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0028.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/32:ℝ) (17/512:ℝ)
    (1/32:ℝ) (448048095471/6250000000000:ℝ) (-11090845038414560830867190724973/25000000000000000000000000000000:ℝ) (1784212129104098141286139/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_016
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0048).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_016 :
    (∫ x in (1/32:ℝ)..(17/512:ℝ), x^0*thetaFirstMode x) ≤ (139171233195594044863/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/32:ℝ) (17/512:ℝ)
    (7168777158679/100000000000000:ℝ) (3541235278851/50000000000000:ℝ) (1784212129104098141286139/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_016 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0049).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_017 :
    (68746027906225820629/500000000000000000000000:ℝ) ≤ ∫ x in (17/512:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-21980485586468361132529650697387/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (17/512:ℝ) (9/256:ℝ)-(21717383193/648199068160:ℝ)*thetaPowerMass 0 (17/512:ℝ) (9/256:ℝ)) ≤
      thetaFirstModeFirst (21717383193/648199068160:ℝ)*(thetaPowerMass 1 (17/512:ℝ) (9/256:ℝ)-(21717383193/648199068160:ℝ)*thetaPowerMass 0 (17/512:ℝ) (9/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0030.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (17/512:ℝ) (9/256:ℝ)
    (21717383193/648199068160:ℝ) (7069219913167/100000000000000:ℝ) (-21980485586468361132529650697387/50000000000000000000000000000000:ℝ) (222733322296030593255943/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_017
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0053).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_017 :
    (∫ x in (17/512:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x) ≤ (137492205527997361667/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/512:ℝ) (9/256:ℝ)
    (3541235278851/50000000000000:ℝ) (6996844576391/100000000000000:ℝ) (222733322296030593255943/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_017 (thetaFirstMode_refined_node_0049).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_018 :
    (135826312563522810187/1000000000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(19/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4366642948177897490225661444281/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (9/256:ℝ) (19/512:ℝ)-(9/256:ℝ)*thetaPowerMass 0 (9/256:ℝ) (19/512:ℝ)) ≤
      thetaFirstModeFirst (9/256:ℝ)*(thetaPowerMass 1 (9/256:ℝ) (19/512:ℝ)-(9/256:ℝ)*thetaPowerMass 0 (9/256:ℝ) (19/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0031.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (9/256:ℝ) (19/512:ℝ)
    (9/256:ℝ) (3498418534927/50000000000000:ℝ) (-4366642948177897490225661444281/10000000000000000000000000000000:ℝ) (1779395815030052136323121/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_018
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0054).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_018 :
    (∫ x in (9/256:ℝ)..(19/512:ℝ), x^0*thetaFirstMode x) ≤ (135826462552859690803/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/256:ℝ) (19/512:ℝ)
    (6996844576391/100000000000000:ℝ) (6911898319961/100000000000000:ℝ) (1779395815030052136323121/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_018 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0055).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_019 :
    (134173838725858362349/1000000000000000000000000:ℝ) ≤ ∫ x in (19/512:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-86541109736915769008140376073/200000000000000000000000000000:ℝ)*(thetaPowerMass 1 (19/512:ℝ) (5/128:ℝ)-(58618940391/1568203548160:ℝ)*thetaPowerMass 0 (19/512:ℝ) (5/128:ℝ)) ≤
      thetaFirstModeFirst (58618940391/1568203548160:ℝ)*(thetaPowerMass 1 (19/512:ℝ) (5/128:ℝ)-(58618940391/1568203548160:ℝ)*thetaPowerMass 0 (19/512:ℝ) (5/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0033.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (19/512:ℝ) (5/128:ℝ)
    (58618940391/1568203548160:ℝ) (1725047079571/25000000000000:ℝ) (-86541109736915769008140376073/200000000000000000000000000000:ℝ) (1776800368486171250048647/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_019
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0059).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_019 :
    (∫ x in (19/512:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x) ≤ (134173986327918745819/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/512:ℝ) (5/128:ℝ)
    (6911898319961/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1776800368486171250048647/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_019 (thetaFirstMode_refined_node_0055).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_020 :
    (26506922022087413621/200000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(21/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-429713601120990297218690516651/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/128:ℝ) (21/512:ℝ)-(5/128:ℝ)*thetaPowerMass 0 (5/128:ℝ) (21/512:ℝ)) ≤
      thetaFirstModeFirst (5/128:ℝ)*(thetaPowerMass 1 (5/128:ℝ) (21/512:ℝ)-(5/128:ℝ)*thetaPowerMass 0 (5/128:ℝ) (21/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0034.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/128:ℝ) (21/512:ℝ)
    (5/128:ℝ) (1365524692699/20000000000000:ℝ) (-429713601120990297218690516651/1000000000000000000000000000000:ℝ) (1774080787998504949871369/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_020
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0060).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_020 :
    (∫ x in (5/128:ℝ)..(21/512:ℝ), x^0*thetaFirstMode x) ≤ (66267378990244875021/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/128:ℝ) (21/512:ℝ)
    (6827630845943/100000000000000:ℝ) (3372020582139/50000000000000:ℝ) (1774080787998504949871369/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_020 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0061).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_021 :
    (2618172244284359769/20000000000000000000000:ℝ) ≤ ∫ x in (21/512:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-21290550011442000564661609608841/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (21/512:ℝ) (11/256:ℝ)-(143436821409/3476346088960:ℝ)*thetaPowerMass 0 (21/512:ℝ) (11/256:ℝ)) ≤
      thetaFirstModeFirst (143436821409/3476346088960:ℝ)*(thetaPowerMass 1 (21/512:ℝ) (11/256:ℝ)-(143436821409/3476346088960:ℝ)*thetaPowerMass 0 (21/512:ℝ) (11/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0036.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (21/512:ℝ) (11/256:ℝ)
    (143436821409/3476346088960:ℝ) (6733588693827/100000000000000:ℝ) (-21290550011442000564661609608841/50000000000000000000000000000000:ℝ) (221404705327917593722827/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_021
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0065).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_021 :
    (∫ x in (21/512:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x) ≤ (130908757710268214953/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/512:ℝ) (11/256:ℝ)
    (3372020582139/50000000000000:ℝ) (666112823751/10000000000000:ℝ) (221404705327917593722827/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_021 (thetaFirstMode_refined_node_0061).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_022 :
    (32323954759057890223/250000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(23/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2113918342479670500154719740877/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/256:ℝ) (23/512:ℝ)-(11/256:ℝ)*thetaPowerMass 0 (11/256:ℝ) (23/512:ℝ)) ≤
      thetaFirstModeFirst (11/256:ℝ)*(thetaPowerMass 1 (11/256:ℝ) (23/512:ℝ)-(11/256:ℝ)*thetaPowerMass 0 (11/256:ℝ) (23/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0037.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/256:ℝ) (23/512:ℝ)
    (11/256:ℝ) (3330560489303/50000000000000:ℝ) (-2113918342479670500154719740877/5000000000000000000000000000000:ℝ) (176827152117764724806041/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_022
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0066).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_022 :
    (∫ x in (11/256:ℝ)..(23/512:ℝ), x^0*thetaFirstMode x) ≤ (129295964794515507987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/256:ℝ) (23/512:ℝ)
    (666112823751/10000000000000:ℝ) (1644722745281/25000000000000:ℝ) (176827152117764724806041/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_022 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0067).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_023 :
    (127696214194953750073/1000000000000000000000000:ℝ) ≤ ∫ x in (23/512:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-523663174803192504006886623081/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (23/512:ℝ) (3/64:ℝ)-(323819456607/7172691612160:ℝ)*thetaPowerMass 0 (23/512:ℝ) (3/64:ℝ)) ≤
      thetaFirstModeFirst (323819456607/7172691612160:ℝ)*(thetaPowerMass 1 (23/512:ℝ) (3/64:ℝ)-(323819456607/7172691612160:ℝ)*thetaPowerMass 0 (23/512:ℝ) (3/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0039.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (23/512:ℝ) (3/64:ℝ)
    (323819456607/7172691612160:ℝ) (6569483518681/100000000000000:ℝ) (-523663174803192504006886623081/1250000000000000000000000000000:ℝ) (220647879015663931023683/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_023
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0071).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_023 :
    (∫ x in (23/512:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x) ≤ (31924089398084066729/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/512:ℝ) (3/64:ℝ)
    (1644722745281/25000000000000:ℝ) (3248664131823/50000000000000:ℝ) (220647879015663931023683/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_023 (thetaFirstMode_refined_node_0067).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_024 :
    (6305488494675904591/50000000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(25/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2599227671987338000656508596003/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/64:ℝ) (25/512:ℝ)-(3/64:ℝ)*thetaPowerMass 0 (3/64:ℝ) (25/512:ℝ)) ≤
      thetaFirstModeFirst (3/64:ℝ)*(thetaPowerMass 1 (3/64:ℝ) (25/512:ℝ)-(3/64:ℝ)*thetaPowerMass 0 (3/64:ℝ) (25/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0040.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/64:ℝ) (25/512:ℝ)
    (3/64:ℝ) (6497321127709/100000000000000:ℝ) (-2599227671987338000656508596003/6250000000000000000000000000000:ℝ) (880986401761846692876809/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_024
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0072).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_024 :
    (∫ x in (3/64:ℝ)..(25/512:ℝ), x^0*thetaFirstMode x) ≤ (126109913548330776783/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/64:ℝ) (25/512:ℝ)
    (3248664131823/50000000000000:ℝ) (6416438906917/100000000000000:ℝ) (880986401761846692876809/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_024 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0073).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_025 :
    (12453646789133345571/100000000000000000000000:ℝ) ≤ ∫ x in (25/512:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-206033926439249124145660343477/500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (25/512:ℝ) (13/256:ℝ)-(136694029725/2787696138752:ℝ)*thetaPowerMass 0 (25/512:ℝ) (13/256:ℝ)) ≤
      thetaFirstModeFirst (136694029725/2787696138752:ℝ)*(thetaPowerMass 1 (25/512:ℝ) (13/256:ℝ)-(136694029725/2787696138752:ℝ)*thetaPowerMass 0 (25/512:ℝ) (13/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0042.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (25/512:ℝ) (13/256:ℝ)
    (136694029725/2787696138752:ℝ) (3203956520547/50000000000000:ℝ) (-206033926439249124145660343477/500000000000000000000000000000:ℝ) (1758641482928085514001897/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_025
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0077).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_025 :
    (∫ x in (25/512:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x) ≤ (62268304598914702111/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/512:ℝ) (13/256:ℝ)
    (6416438906917/100000000000000:ℝ) (1267244337271/20000000000000:ℝ) (1758641482928085514001897/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_025 (thetaFirstMode_refined_node_0073).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_026 :
    (122976278611878663273/1000000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(27/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-255621118784034415451559961067/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (13/256:ℝ) (27/512:ℝ)-(13/256:ℝ)*thetaPowerMass 0 (13/256:ℝ) (27/512:ℝ)) ≤
      thetaFirstModeFirst (13/256:ℝ)*(thetaPowerMass 1 (13/256:ℝ) (27/512:ℝ)-(13/256:ℝ)*thetaPowerMass 0 (13/256:ℝ) (27/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0043.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (13/256:ℝ) (27/512:ℝ)
    (13/256:ℝ) (316810733639/5000000000000:ℝ) (-255621118784034415451559961067/625000000000000000000000000000:ℝ) (877594868655878291542799/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_026
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0078).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_026 :
    (∫ x in (13/256:ℝ)..(27/512:ℝ), x^0*thetaFirstMode x) ≤ (4919056806873752759/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/256:ℝ) (27/512:ℝ)
    (1267244337271/20000000000000:ℝ) (1955211041/31250000000:ℝ) (877594868655878291542799/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_026 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0079).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_027 :
    (121429181977157724673/1000000000000000000000000:ℝ) ≤ ∫ x in (27/512:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2026130524034421173072393168211/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (27/512:ℝ) (7/128:ℝ)-(1362565468143/25744761372160:ℝ)*thetaPowerMass 0 (27/512:ℝ) (7/128:ℝ)) ≤
      thetaFirstModeFirst (1362565468143/25744761372160:ℝ)*(thetaPowerMass 1 (27/512:ℝ) (7/128:ℝ)-(1362565468143/25744761372160:ℝ)*thetaPowerMass 0 (27/512:ℝ) (7/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0045.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (27/512:ℝ) (7/128:ℝ)
    (1362565468143/25744761372160:ℝ) (6248902811683/100000000000000:ℝ) (-2026130524034421173072393168211/5000000000000000000000000000000:ℝ) (175161825295770581263389/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_027
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0083).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_027 :
    (∫ x in (27/512:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x) ≤ (121429321201539717351/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/512:ℝ) (7/128:ℝ)
    (1955211041/31250000000:ℝ) (6177798524727/100000000000000:ℝ) (175161825295770581263389/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_027 (thetaFirstMode_refined_node_0079).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_028 :
    (119895146649192386769/1000000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(29/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-20106882402249366437974215035373/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/128:ℝ) (29/512:ℝ)-(7/128:ℝ)*thetaPowerMass 0 (7/128:ℝ) (29/512:ℝ)) ≤
      thetaFirstModeFirst (7/128:ℝ)*(thetaPowerMass 1 (7/128:ℝ) (29/512:ℝ)-(7/128:ℝ)*thetaPowerMass 0 (7/128:ℝ) (29/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0046.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/128:ℝ) (29/512:ℝ)
    (7/128:ℝ) (3088895816439/50000000000000:ℝ) (-20106882402249366437974215035373/50000000000000000000000000000000:ℝ) (349585547073147977842183/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_028
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0084).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_028 :
    (∫ x in (7/128:ℝ)..(29/512:ℝ), x^0*thetaFirstMode x) ≤ (59947643061637971209/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/128:ℝ) (29/512:ℝ)
    (6177798524727/100000000000000:ℝ) (6099589904549/100000000000000:ℝ) (349585547073147977842183/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_028 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0085).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_029 :
    (23674830146611710589/200000000000000000000000:ℝ) ≤ ∫ x in (29/512:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-796816209155865795231474753921/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (29/512:ℝ) (15/256:ℝ)-(2586561620841/45522720232960:ℝ)*thetaPowerMass 0 (29/512:ℝ) (15/256:ℝ)) ≤
      thetaFirstModeFirst (2586561620841/45522720232960:ℝ)*(thetaPowerMass 1 (29/512:ℝ) (15/256:ℝ)-(2586561620841/45522720232960:ℝ)*thetaPowerMass 0 (29/512:ℝ) (15/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0048.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (29/512:ℝ) (15/256:ℝ)
    (2586561620841/45522720232960:ℝ) (6092468283531/100000000000000:ℝ) (-796816209155865795231474753921/2000000000000000000000000000000:ℝ) (1744118909148945553634357/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_029
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0089).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_029 :
    (∫ x in (29/512:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x) ≤ (5918714394210989133/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/512:ℝ) (15/256:ℝ)
    (6099589904549/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (1744118909148945553634357/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_029 (thetaFirstMode_refined_node_0085).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_030 :
    (116866161149381151347/1000000000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(31/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3953098722851508546114689751313/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/256:ℝ) (31/512:ℝ)-(15/256:ℝ)*thetaPowerMass 0 (15/256:ℝ) (31/512:ℝ)) ≤
      thetaFirstModeFirst (15/256:ℝ)*(thetaPowerMass 1 (15/256:ℝ) (31/512:ℝ)-(15/256:ℝ)*thetaPowerMass 0 (15/256:ℝ) (31/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0049.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/256:ℝ) (31/512:ℝ)
    (15/256:ℝ) (6022041292103/100000000000000:ℝ) (-3953098722851508546114689751313/10000000000000000000000000000000:ℝ) (348038503580446356404579/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_030
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0090).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_030 :
    (∫ x in (15/256:ℝ)..(31/512:ℝ), x^0*thetaFirstMode x) ≤ (116866298547093147343/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/256:ℝ) (31/512:ℝ)
    (6022048062889/100000000000000:ℝ) (2972585773397/50000000000000:ℝ) (348038503580446356404579/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_030 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0091).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_031 :
    (11537115420811441649/100000000000000000000000:ℝ) ≤ ∫ x in (31/512:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2447602546722036932239545475457/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (31/512:ℝ) (1/16:ℝ)-(4705751134359/77506860444160:ℝ)*thetaPowerMass 0 (31/512:ℝ) (1/16:ℝ)) ≤
      thetaFirstModeFirst (4705751134359/77506860444160:ℝ)*(thetaPowerMass 1 (31/512:ℝ) (1/16:ℝ)-(4705751134359/77506860444160:ℝ)*thetaPowerMass 0 (31/512:ℝ) (1/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0051.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (31/512:ℝ) (1/16:ℝ)
    (4705751134359/77506860444160:ℝ) (2969308861029/50000000000000:ℝ) (-2447602546722036932239545475457/6250000000000000000000000000000:ℝ) (1736149324112270662297763/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_031
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0095).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_031 :
    (∫ x in (31/512:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x) ≤ (115371289295807388059/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/512:ℝ) (1/16:ℝ)
    (2972585773397/50000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1736149324112270662297763/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_031 (thetaFirstMode_refined_node_0091).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
