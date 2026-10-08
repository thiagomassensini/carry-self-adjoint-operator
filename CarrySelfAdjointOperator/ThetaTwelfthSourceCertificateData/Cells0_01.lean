import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative02
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative03

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_032 :
    (5694454755519914443/50000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(33/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9712807780648039536783710416019/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/16:ℝ) (33/512:ℝ)-(1/16:ℝ)*thetaPowerMass 0 (1/16:ℝ) (33/512:ℝ)) ≤
      thetaFirstModeFirst (1/16:ℝ)*(thetaPowerMass 1 (1/16:ℝ) (33/512:ℝ)-(1/16:ℝ)*thetaPowerMass 0 (1/16:ℝ) (33/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0052.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/16:ℝ) (33/512:ℝ)
    (1/16:ℝ) (73361902601/1250000000000:ℝ) (-9712807780648039536783710416019/25000000000000000000000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_032
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0096).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_032 :
    (∫ x in (1/16:ℝ)..(33/512:ℝ), x^0*thetaFirstMode x) ≤ (113889230441303234433/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/16:ℝ) (33/512:ℝ)
    (2934479429249/50000000000000:ℝ) (5793408455657/100000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_032 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0097).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_033 :
    (56209979196841948519/500000000000000000000000:ℝ) ≤ ∫ x in (33/512:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 0 (33/512:ℝ) (17/256:ℝ)) ≤
      thetaFirstModeFirst (8248340454057/127663103388160:ℝ)*(thetaPowerMass 1 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 0 (33/512:ℝ) (17/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0054.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (33/512:ℝ) (17/256:ℝ)
    (8248340454057/127663103388160:ℝ) (1157470820943/20000000000000:ℝ) (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_033
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0101).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_033 :
    (∫ x in (33/512:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x) ≤ (112420091427488352887/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/512:ℝ) (17/256:ℝ)
    (5793408455657/100000000000000:ℝ) (2859259375861/50000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_033 (thetaFirstMode_refined_node_0097).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_034 :
    (110963707562170173429/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(35/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4771834872341895137550187393991/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (17/256:ℝ) (35/512:ℝ)-(17/256:ℝ)*thetaPowerMass 0 (17/256:ℝ) (35/512:ℝ)) ≤
      thetaFirstModeFirst (17/256:ℝ)*(thetaPowerMass 1 (17/256:ℝ) (35/512:ℝ)-(17/256:ℝ)*thetaPowerMass 0 (17/256:ℝ) (35/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0055.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (17/256:ℝ) (35/512:ℝ)
    (17/256:ℝ) (2859256110477/50000000000000:ℝ) (-4771834872341895137550187393991/12500000000000000000000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_034
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0102).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_034 :
    (∫ x in (17/256:ℝ)..(35/512:ℝ), x^0*thetaFirstMode x) ≤ (55481920418299394847/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/256:ℝ) (35/512:ℝ)
    (2859259375861/50000000000000:ℝ) (1128857623223/20000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_034 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0103).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_035 :
    (27380078851113815143/250000000000000000000000:ℝ) ≤ ∫ x in (35/512:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 0 (35/512:ℝ) (9/128:ℝ)) ≤
      thetaFirstModeFirst (2798051987115/40842963901952:ℝ)*(thetaPowerMass 1 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 0 (35/512:ℝ) (9/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0057.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (35/512:ℝ) (9/128:ℝ)
    (2798051987115/40842963901952:ℝ) (5638676396401/100000000000000:ℝ) (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_035
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0107).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_035 :
    (∫ x in (35/512:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x) ≤ (109520446395214651711/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/512:ℝ) (9/128:ℝ)
    (1128857623223/20000000000000:ℝ) (5570714874669/100000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_035 (thetaFirstMode_refined_node_0103).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_036 :
    (108089743752614237787/1000000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(37/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4687688852339902010928426547041/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (9/128:ℝ) (37/512:ℝ)-(9/128:ℝ)*thetaPowerMass 0 (9/128:ℝ) (37/512:ℝ)) ≤
      thetaFirstModeFirst (9/128:ℝ)*(thetaPowerMass 1 (9/128:ℝ) (37/512:ℝ)-(9/128:ℝ)*thetaPowerMass 0 (9/128:ℝ) (37/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0058.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (9/128:ℝ) (37/512:ℝ)
    (9/128:ℝ) (13926771157/250000000000:ℝ) (-4687688852339902010928426547041/12500000000000000000000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_036
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0108).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_036 :
    (∫ x in (9/128:ℝ)..(37/512:ℝ), x^0*thetaFirstMode x) ≤ (21617974996228995197/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/128:ℝ) (37/512:ℝ)
    (5570714874669/100000000000000:ℝ) (5497797309893/100000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_036 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0109).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_037 :
    (106671963670742047989/1000000000000000000000000:ℝ) ≤ ∫ x in (37/512:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 0 (37/512:ℝ) (19/256:ℝ)) ≤
      thetaFirstModeFirst (23045391280593/318280722972160:ℝ)*(thetaPowerMass 1 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 0 (37/512:ℝ) (19/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0060.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (37/512:ℝ) (19/256:ℝ)
    (23045391280593/318280722972160:ℝ) (1373145106981/25000000000000:ℝ) (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_037
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0113).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_037 :
    (∫ x in (37/512:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x) ≤ (106672092628750097907/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/512:ℝ) (19/256:ℝ)
    (5497797309893/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_037 (thetaFirstMode_refined_node_0109).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_038 :
    (52633467671452618259/500000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(39/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4603988009807282375485863725769/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (19/256:ℝ) (39/512:ℝ)-(19/256:ℝ)*thetaPowerMass 0 (19/256:ℝ) (39/512:ℝ)) ≤
      thetaFirstModeFirst (19/256:ℝ)*(thetaPowerMass 1 (19/256:ℝ) (39/512:ℝ)-(19/256:ℝ)*thetaPowerMass 0 (19/256:ℝ) (39/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0061.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (19/256:ℝ) (39/512:ℝ)
    (19/256:ℝ) (1356381841877/25000000000000:ℝ) (-4603988009807282375485863725769/12500000000000000000000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_038
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0114).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_038 :
    (∫ x in (19/256:ℝ)..(39/512:ℝ), x^0*thetaFirstMode x) ≤ (6579191533502583311/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/256:ℝ) (39/512:ℝ)
    (1356383415313/25000000000000:ℝ) (2676961062807/50000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_038 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0115).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_039 :
    (12984328516872958451/125000000000000000000000:ℝ) ≤ ∫ x in (39/512:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-569934446770298107902169363121/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 0 (39/512:ℝ) (5/64:ℝ)) ≤
      thetaFirstModeFirst (36980403679791/484639493685760:ℝ)*(thetaPowerMass 1 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 0 (39/512:ℝ) (5/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0063.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (39/512:ℝ) (5/64:ℝ)
    (36980403679791/484639493685760:ℝ) (1069811902989/20000000000000:ℝ) (-569934446770298107902169363121/1562500000000000000000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_039
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0119).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_039 :
    (∫ x in (39/512:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x) ≤ (103874755071438908847/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/512:ℝ) (5/64:ℝ)
    (2676961062807/50000000000000:ℝ) (1056592171499/20000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_039 (thetaFirstMode_refined_node_0115).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_040 :
    (51247500305318378777/500000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(41/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-361660334941576353186998236619/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/64:ℝ) (41/512:ℝ)-(5/64:ℝ)*thetaPowerMass 0 (5/64:ℝ) (41/512:ℝ)) ≤
      thetaFirstModeFirst (5/64:ℝ)*(thetaPowerMass 1 (5/64:ℝ) (41/512:ℝ)-(5/64:ℝ)*thetaPowerMass 0 (5/64:ℝ) (41/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0064.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/64:ℝ) (41/512:ℝ)
    (5/64:ℝ) (2641477340537/50000000000000:ℝ) (-361660334941576353186998236619/1000000000000000000000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_040
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0120).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_040 :
    (∫ x in (5/64:ℝ)..(41/512:ℝ), x^0*thetaFirstMode x) ≤ (51247563889830369617/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/64:ℝ) (41/512:ℝ)
    (1056592171499/20000000000000:ℝ) (5212647969417/100000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_040 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0121).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_041 :
    (101128020462808908051/1000000000000000000000000:ℝ) ≤ ∫ x in (41/512:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 0 (41/512:ℝ) (21/256:ℝ)) ≤
      thetaFirstModeFirst (57958928803809/722636919247360:ℝ)*(thetaPowerMass 1 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 0 (41/512:ℝ) (21/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0066.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (41/512:ℝ) (21/256:ℝ)
    (57958928803809/722636919247360:ℝ) (208324196157/4000000000000:ℝ) (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_041
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0125).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_041 :
    (∫ x in (41/512:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x) ≤ (20225629077846456529/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/512:ℝ) (21/256:ℝ)
    (5212647969417/100000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_041 (thetaFirstMode_refined_node_0121).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_042 :
    (19954728932549511903/200000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(43/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17752035495265020844685534732763/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (21/256:ℝ) (43/512:ℝ)-(21/256:ℝ)*thetaPowerMass 0 (21/256:ℝ) (43/512:ℝ)) ≤
      thetaFirstModeFirst (21/256:ℝ)*(thetaPowerMass 1 (21/256:ℝ) (43/512:ℝ)-(21/256:ℝ)*thetaPowerMass 0 (21/256:ℝ) (43/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0067.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (21/256:ℝ) (43/512:ℝ)
    (21/256:ℝ) (5142975472393/100000000000000:ℝ) (-17752035495265020844685534732763/50000000000000000000000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_042
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0126).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_042 :
    (∫ x in (21/256:ℝ)..(43/512:ℝ), x^0*thetaFirstMode x) ≤ (99773769819195658779/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/256:ℝ) (43/512:ℝ)
    (5142981532319/100000000000000:ℝ) (5073959575833/100000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_042 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0127).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_043 :
    (98431839258112558581/1000000000000000000000000:ℝ) ≤ ∫ x in (43/512:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17165169357063551396899444949/48828125000000000000000000000:ℝ)*(thetaPowerMass 1 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 0 (43/512:ℝ) (11/128:ℝ)) ≤
      thetaFirstModeFirst (88920376319007/1057252278300160:ℝ)*(thetaPowerMass 1 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 0 (43/512:ℝ) (11/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0069.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (43/512:ℝ) (11/128:ℝ)
    (88920376319007/1057252278300160:ℝ) (2534853049781/50000000000000:ℝ) (-17165169357063551396899444949/48828125000000000000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_043
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0131).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_043 :
    (∫ x in (43/512:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x) ≤ (98431962186150752467/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/512:ℝ) (11/128:ℝ)
    (5073959575833/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_043 (thetaFirstMode_refined_node_0127).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_044 :
    (97102559656027981087/1000000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(45/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4355773196367319557647851525227/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/128:ℝ) (45/512:ℝ)-(11/128:ℝ)*thetaPowerMass 0 (11/128:ℝ) (45/512:ℝ)) ≤
      thetaFirstModeFirst (11/128:ℝ)*(thetaPowerMass 1 (11/128:ℝ) (45/512:ℝ)-(11/128:ℝ)*thetaPowerMass 0 (11/128:ℝ) (45/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0070.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/128:ℝ) (45/512:ℝ)
    (11/128:ℝ) (2502787072221/50000000000000:ℝ) (-4355773196367319557647851525227/12500000000000000000000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_044
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0132).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_044 :
    (∫ x in (11/128:ℝ)..(45/512:ℝ), x^0*thetaFirstMode x) ≤ (19420536562368647821/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/128:ℝ) (45/512:ℝ)
    (5005580088729/100000000000000:ℝ) (4937841019247/100000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_044 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0133).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_045 :
    (95785770288044237247/1000000000000000000000000:ℝ) ≤ ∫ x in (45/512:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-539054799777053651949066501611/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 0 (45/512:ℝ) (23/256:ℝ)) ≤
      thetaFirstModeFirst (26759859160005/304068323159552:ℝ)*(thetaPowerMass 1 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 0 (45/512:ℝ) (23/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0072.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (45/512:ℝ) (23/256:ℝ)
    (26759859160005/304068323159552:ℝ) (1233462777513/25000000000000:ℝ) (-539054799777053651949066501611/1562500000000000000000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_045
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0137).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_045 :
    (∫ x in (45/512:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x) ≤ (9578589123009829189/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/512:ℝ) (23/256:ℝ)
    (4937841019247/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_045 (thetaFirstMode_refined_node_0133).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_046 :
    (11810178128386510537/125000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(47/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-170962716049636727657775915129/500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (23/256:ℝ) (47/512:ℝ)-(23/256:ℝ)*thetaPowerMass 0 (23/256:ℝ) (47/512:ℝ)) ≤
      thetaFirstModeFirst (23/256:ℝ)*(thetaPowerMass 1 (23/256:ℝ) (47/512:ℝ)-(23/256:ℝ)*thetaPowerMass 0 (23/256:ℝ) (47/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0073.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (23/256:ℝ) (47/512:ℝ)
    (23/256:ℝ) (97414688919/2000000000000:ℝ) (-170962716049636727657775915129/500000000000000000000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_046
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0138).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_046 :
    (∫ x in (23/256:ℝ)..(47/512:ℝ), x^0*thetaFirstMode x) ≤ (94481546194301177839/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/256:ℝ) (47/512:ℝ)
    (194829611019/4000000000000:ℝ) (4804275725737/100000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_046 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0139).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_047 :
    (93189486716969606667/1000000000000000000000000:ℝ) ≤ ∫ x in (47/512:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 0 (47/512:ℝ) (3/32:ℝ)) ≤
      thetaFirstModeFirst (197791827765543/2152076489628160:ℝ)*(thetaPowerMass 1 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 0 (47/512:ℝ) (3/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0075.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (47/512:ℝ) (3/32:ℝ)
    (197791827765543/2152076489628160:ℝ) (4800526634211/100000000000000:ℝ) (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_047
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0143).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_047 :
    (∫ x in (47/512:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x) ≤ (93189605685307530079/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/512:ℝ) (3/32:ℝ)
    (4804275725737/100000000000000:ℝ) (947689039803/20000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_047 (thetaFirstMode_refined_node_0139).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_048 :
    (2297747693194107599/25000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(49/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3354330674754989163504677392359/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/32:ℝ) (49/512:ℝ)-(3/32:ℝ)*thetaPowerMass 0 (3/32:ℝ) (49/512:ℝ)) ≤
      thetaFirstModeFirst (3/32:ℝ)*(thetaPowerMass 1 (3/32:ℝ) (49/512:ℝ)-(3/32:ℝ)*thetaPowerMass 0 (3/32:ℝ) (49/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0076.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/32:ℝ) (49/512:ℝ)
    (3/32:ℝ) (4738439483347/100000000000000:ℝ) (-3354330674754989163504677392359/10000000000000000000000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_048
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0144).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_048 :
    (∫ x in (3/32:ℝ)..(49/512:ℝ), x^0*thetaFirstMode x) ≤ (45955013459452214093/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/32:ℝ) (49/512:ℝ)
    (947689039803/20000000000000:ℝ) (4673246485291/100000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_048 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0145).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_049 :
    (90642649346156679979/1000000000000000000000000:ℝ) ≤ ∫ x in (49/512:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 0 (49/512:ℝ) (25/256:ℝ)) ≤
      thetaFirstModeFirst (287676456077241/3002597697026560:ℝ)*(thetaPowerMass 1 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 0 (49/512:ℝ) (25/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0078.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (49/512:ℝ) (25/256:ℝ)
    (287676456077241/3002597697026560:ℝ) (2334859103349/50000000000000:ℝ) (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_049
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0149).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_049 :
    (∫ x in (49/512:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x) ≤ (22660691588420403693/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/512:ℝ) (25/256:ℝ)
    (4673246485291/100000000000000:ℝ) (4608677336011/100000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_049 (thetaFirstMode_refined_node_0145).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_050 :
    (44693831235662986903/500000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(51/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-16449317893361112351679343767483/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (25/256:ℝ) (51/512:ℝ)-(25/256:ℝ)*thetaPowerMass 0 (25/256:ℝ) (51/512:ℝ)) ≤
      thetaFirstModeFirst (25/256:ℝ)*(thetaPowerMass 1 (25/256:ℝ) (51/512:ℝ)-(25/256:ℝ)*thetaPowerMass 0 (25/256:ℝ) (51/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0079.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (25/256:ℝ) (51/512:ℝ)
    (25/256:ℝ) (576083966659/12500000000000:ℝ) (-16449317893361112351679343767483/50000000000000000000000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_050
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0150).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_050 :
    (∫ x in (25/256:ℝ)..(51/512:ℝ), x^0*thetaFirstMode x) ≤ (44693889849636910247/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/256:ℝ) (51/512:ℝ)
    (4608677336011/100000000000000:ℝ) (908947092893/20000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_050 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0151).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_051 :
    (22036226716054815143/250000000000000000000000:ℝ) ≤ ∫ x in (51/512:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 0 (51/512:ℝ) (13/128:ℝ)) ≤
      thetaFirstModeFirst (412196976114759/4133904418178560:ℝ)*(thetaPowerMass 1 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 0 (51/512:ℝ) (13/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0081.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (51/512:ℝ) (13/128:ℝ)
    (412196976114759/4133904418178560:ℝ) (567676289121/12500000000000:ℝ) (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_051
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0155).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_051 :
    (∫ x in (51/512:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x) ≤ (22036255480987200889/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/512:ℝ) (13/128:ℝ)
    (908947092893/20000000000000:ℝ) (560177318273/12500000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_051 (thetaFirstMode_refined_node_0151).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_052 :
    (86914331985395030139/1000000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(53/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1008083956031021889749993571771/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (13/128:ℝ) (53/512:ℝ)-(13/128:ℝ)*thetaPowerMass 0 (13/128:ℝ) (53/512:ℝ)) ≤
      thetaFirstModeFirst (13/128:ℝ)*(thetaPowerMass 1 (13/128:ℝ) (53/512:ℝ)-(13/128:ℝ)*thetaPowerMass 0 (13/128:ℝ) (53/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0082.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (13/128:ℝ) (53/512:ℝ)
    (13/128:ℝ) (4481413055423/100000000000000:ℝ) (-1008083956031021889749993571771/3125000000000000000000000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_052
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0156).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_052 :
    (∫ x in (13/128:ℝ)..(53/512:ℝ), x^0*thetaFirstMode x) ≤ (86914447263210986551/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/128:ℝ) (53/512:ℝ)
    (560177318273/12500000000000:ℝ) (138085131857/3125000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_052 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0157).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_053 :
    (17139179220490720441/200000000000000000000000:ℝ) ≤ ∫ x in (53/512:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 0 (53/512:ℝ) (27/256:ℝ)) ≤
      thetaFirstModeFirst (582516327971457/5622000143388160:ℝ)*(thetaPowerMass 1 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 0 (53/512:ℝ) (27/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0084.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (53/512:ℝ) (27/256:ℝ)
    (582516327971457/5622000143388160:ℝ) (4415586481659/100000000000000:ℝ) (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_053
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0161).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_053 :
    (∫ x in (53/512:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x) ≤ (42848004613929135343/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (53/512:ℝ) (27/256:ℝ)
    (138085131857/3125000000000:ℝ) (4356650085507/100000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_053 (thetaFirstMode_refined_node_0157).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_054 :
    (21122386817869277839/250000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(55/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3952951499596753853535160500813/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (27/256:ℝ) (55/512:ℝ)-(27/256:ℝ)*thetaPowerMass 0 (27/256:ℝ) (55/512:ℝ)) ≤
      thetaFirstModeFirst (27/256:ℝ)*(thetaPowerMass 1 (27/256:ℝ) (55/512:ℝ)-(27/256:ℝ)*thetaPowerMass 0 (27/256:ℝ) (55/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0085.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (27/256:ℝ) (55/512:ℝ)
    (27/256:ℝ) (4356644705751/100000000000000:ℝ) (-3952951499596753853535160500813/12500000000000000000000000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_054
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0162).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_054 :
    (∫ x in (27/256:ℝ)..(55/512:ℝ), x^0*thetaFirstMode x) ≤ (10561207576571987621/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/256:ℝ) (55/512:ℝ)
    (4356650085507/100000000000000:ℝ) (53689921367/1250000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_054 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0163).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_055 :
    (83295242299351582491/1000000000000000000000000:ℝ) ≤ ∫ x in (55/512:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 0 (55/512:ℝ) (7/64:ℝ)) ≤
      thetaFirstModeFirst (162550142281395/1511863535831552:ℝ)*(thetaPowerMass 1 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 0 (55/512:ℝ) (7/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0087.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (55/512:ℝ) (7/64:ℝ)
    (162550142281395/1511863535831552:ℝ) (134132167511/3125000000000:ℝ) (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_055
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0167).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_055 :
    (∫ x in (55/512:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x) ≤ (83295353504237435579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (55/512:ℝ) (7/64:ℝ)
    (53689921367/1250000000000:ℝ) (2117176309913/50000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_055 (thetaFirstMode_refined_node_0163).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_056 :
    (82112927872738906919/1000000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(57/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7748390324661775555415589013703/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/64:ℝ) (57/512:ℝ)-(7/64:ℝ)*thetaPowerMass 0 (7/64:ℝ) (57/512:ℝ)) ≤
      thetaFirstModeFirst (7/64:ℝ)*(thetaPowerMass 1 (7/64:ℝ) (57/512:ℝ)-(7/64:ℝ)*thetaPowerMass 0 (7/64:ℝ) (57/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0088.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/64:ℝ) (57/512:ℝ)
    (7/64:ℝ) (2117173675039/50000000000000:ℝ) (-7748390324661775555415589013703/25000000000000000000000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_056
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0168).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_056 :
    (∫ x in (7/64:ℝ)..(57/512:ℝ), x^0*thetaFirstMode x) ≤ (41056519645346962427/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/64:ℝ) (57/512:ℝ)
    (2117176309913/50000000000000:ℝ) (4174124310253/100000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_056 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0169).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_057 :
    (40471279685850658769/500000000000000000000000:ℝ) ≤ ∫ x in (57/512:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 0 (57/512:ℝ) (29/256:ℝ)) ≤
      thetaFirstModeFirst (1120594199442993/10057446457500160:ℝ)*(thetaPowerMass 1 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 0 (57/512:ℝ) (29/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0090.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (57/512:ℝ) (29/256:ℝ)
    (1120594199442993/10057446457500160:ℝ) (4171320778711/100000000000000:ℝ) (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_057
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0173).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_057 :
    (∫ x in (57/512:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x) ≤ (16188533733961459569/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/512:ℝ) (29/256:ℝ)
    (4174124310253/100000000000000:ℝ) (411450623883/10000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_057 (thetaFirstMode_refined_node_0169).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_058 :
    (7978408214869859779/100000000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(59/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1518434008878023581873606322193/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (29/256:ℝ) (59/512:ℝ)-(29/256:ℝ)*thetaPowerMass 0 (29/256:ℝ) (59/512:ℝ)) ≤
      thetaFirstModeFirst (29/256:ℝ)*(thetaPowerMass 1 (29/256:ℝ) (59/512:ℝ)-(29/256:ℝ)*thetaPowerMass 0 (29/256:ℝ) (59/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0091.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (29/256:ℝ) (59/512:ℝ)
    (29/256:ℝ) (514312634759/12500000000000:ℝ) (-1518434008878023581873606322193/5000000000000000000000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_058
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0174).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_058 :
    (∫ x in (29/256:ℝ)..(59/512:ℝ), x^0*thetaFirstMode x) ≤ (79784191657555985303/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/256:ℝ) (59/512:ℝ)
    (411450623883/10000000000000:ℝ) (4055495829081/100000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_058 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0175).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_059 :
    (3931872509584708559/50000000000000000000000:ℝ) ≤ ∫ x in (59/512:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 0 (59/512:ℝ) (15/128:ℝ)) ≤
      thetaFirstModeFirst (1528044900298191/13250186301775360:ℝ)*(thetaPowerMass 1 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 0 (59/512:ℝ) (15/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0093.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (59/512:ℝ) (15/128:ℝ)
    (1528044900298191/13250186301775360:ℝ) (506605225251/12500000000000:ℝ) (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_059
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0179).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_059 :
    (∫ x in (59/512:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x) ≤ (78637557597537028749/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/512:ℝ) (15/128:ℝ)
    (4055495829081/100000000000000:ℝ) (499636308793/12500000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_059 (thetaFirstMode_refined_node_0175).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_060 :
    (77502607556032512031/1000000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(61/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-929659706310126709638653724373/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/128:ℝ) (61/512:ℝ)-(15/128:ℝ)*thetaPowerMass 0 (15/128:ℝ) (61/512:ℝ)) ≤
      thetaFirstModeFirst (15/128:ℝ)*(thetaPowerMass 1 (15/128:ℝ) (61/512:ℝ)-(15/128:ℝ)*thetaPowerMass 0 (15/128:ℝ) (61/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0094.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/128:ℝ) (61/512:ℝ)
    (15/128:ℝ) (1998542708769/50000000000000:ℝ) (-929659706310126709638653724373/3125000000000000000000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_060
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0180).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_060 :
    (∫ x in (15/128:ℝ)..(61/512:ℝ), x^0*thetaFirstMode x) ≤ (77502715170058046137/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/128:ℝ) (61/512:ℝ)
    (499636308793/12500000000000:ℝ) (3939287518223/100000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_060 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0181).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_061 :
    (19094876718277562291/250000000000000000000000:ℝ) ≤ ∫ x in (61/512:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 0 (61/512:ℝ) (31/256:ℝ)) ≤
      thetaFirstModeFirst (2062244582827209/17296952731317760:ℝ)*(thetaPowerMass 1 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 0 (61/512:ℝ) (31/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0096.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (61/512:ℝ) (31/256:ℝ)
    (2062244582827209/17296952731317760:ℝ) (3936772777441/100000000000000:ℝ) (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_061
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0185).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_061 :
    (∫ x in (61/512:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x) ≤ (15275922480210683939/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/512:ℝ) (31/256:ℝ)
    (3939287518223/100000000000000:ℝ) (3882084295049/100000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_061 (thetaFirstMode_refined_node_0181).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_062 :
    (18817022734412851257/250000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(63/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-728374768609252081346732410117/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (31/256:ℝ) (63/512:ℝ)-(31/256:ℝ)*thetaPowerMass 0 (31/256:ℝ) (63/512:ℝ)) ≤
      thetaFirstModeFirst (31/256:ℝ)*(thetaPowerMass 1 (31/256:ℝ) (63/512:ℝ)-(31/256:ℝ)*thetaPowerMass 0 (31/256:ℝ) (63/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0097.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (31/256:ℝ) (63/512:ℝ)
    (31/256:ℝ) (242629959321/6250000000000:ℝ) (-728374768609252081346732410117/2500000000000000000000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_062
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0186).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_062 :
    (∫ x in (31/256:ℝ)..(63/512:ℝ), x^0*thetaFirstMode x) ≤ (1176065572988807549/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/256:ℝ) (63/512:ℝ)
    (3882084295049/100000000000000:ℝ) (3825478090361/100000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_062 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0187).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_063 :
    (37084155530515878541/500000000000000000000000:ℝ) ≤ ∫ x in (63/512:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x := by
  have hd : (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 0 (63/512:ℝ) (1/8:ℝ)) ≤
      thetaFirstModeFirst (2756444578756407/22386559816092160:ℝ)*(thetaPowerMass 1 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 0 (63/512:ℝ) (1/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0099.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (63/512:ℝ) (1/8:ℝ)
    (2756444578756407/22386559816092160:ℝ) (1911546687323/50000000000000:ℝ) (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_063
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0191).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_063 :
    (∫ x in (63/512:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x) ≤ (74168414726032953821/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/512:ℝ) (1/8:ℝ)
    (3825478090361/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_063 (thetaFirstMode_refined_node_0187).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
