import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative02
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative03

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_4_032 :
    (1849624623495137/1000000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(33/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4814060781548974449617637/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (1/16:ℝ) (33/512:ℝ)-(33/512:ℝ)*thetaPowerMass 4 (1/16:ℝ) (33/512:ℝ)) ≤
      thetaFirstModeFirst (33/512:ℝ)*(thetaPowerMass 5 (1/16:ℝ) (33/512:ℝ)-(33/512:ℝ)*thetaPowerMass 4 (1/16:ℝ) (33/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0053.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (1/16:ℝ) (33/512:ℝ)
    (33/512:ℝ) (1448350466289/25000000000000:ℝ) (-4814060781548974449617637/12500000000000000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_032
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0097).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_032 :
    (∫ x in (1/16:ℝ)..(33/512:ℝ), x^4*thetaFirstMode x) ≤ (369925353799447/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (1/16:ℝ) (33/512:ℝ)
    (2934479429249/50000000000000:ℝ) (5793408455657/100000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_032 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0097).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_033 :
    (1030504879170963/500000000000000000000000:ℝ) ≤ ∫ x in (33/512:ℝ)..(17/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 4 (33/512:ℝ) (17/256:ℝ)) ≤
      thetaFirstModeFirst (8248340454057/127663103388160:ℝ)*(thetaPowerMass 5 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 4 (33/512:ℝ) (17/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0054.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (33/512:ℝ) (17/256:ℝ)
    (8248340454057/127663103388160:ℝ) (1157470820943/20000000000000:ℝ) (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_033
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0101).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_033 :
    (∫ x in (33/512:ℝ)..(17/256:ℝ), x^4*thetaFirstMode x) ≤ (64406631224079/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (33/512:ℝ) (17/256:ℝ)
    (5793408455657/100000000000000:ℝ) (2859259375861/50000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_033 (thetaFirstMode_refined_node_0097).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_034 :
    (2288258589549759/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(35/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1182425138294745884210001/3125000000000000000000000:ℝ)*(thetaPowerMass 5 (17/256:ℝ) (35/512:ℝ)-(35/512:ℝ)*thetaPowerMass 4 (17/256:ℝ) (35/512:ℝ)) ≤
      thetaFirstModeFirst (35/512:ℝ)*(thetaPowerMass 5 (17/256:ℝ) (35/512:ℝ)-(35/512:ℝ)*thetaPowerMass 4 (17/256:ℝ) (35/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0056.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (17/256:ℝ) (35/512:ℝ)
    (35/512:ℝ) (1411070411223/25000000000000:ℝ) (-1182425138294745884210001/3125000000000000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_034
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0103).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_034 :
    (∫ x in (17/256:ℝ)..(35/512:ℝ), x^4*thetaFirstMode x) ≤ (2288261268558457/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (17/256:ℝ) (35/512:ℝ)
    (2859259375861/50000000000000:ℝ) (1128857623223/20000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_034 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0103).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_035 :
    (2531902838877539/1000000000000000000000000:ℝ) ≤ ∫ x in (35/512:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 4 (35/512:ℝ) (9/128:ℝ)) ≤
      thetaFirstModeFirst (2798051987115/40842963901952:ℝ)*(thetaPowerMass 5 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 4 (35/512:ℝ) (9/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0057.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (35/512:ℝ) (9/128:ℝ)
    (2798051987115/40842963901952:ℝ) (5638676396401/100000000000000:ℝ) (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_035
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0107).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_035 :
    (∫ x in (35/512:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x) ≤ (1265952934760373/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (35/512:ℝ) (9/128:ℝ)
    (1128857623223/20000000000000:ℝ) (5570714874669/100000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_035 (thetaFirstMode_refined_node_0103).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_036 :
    (2792459187194291/1000000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(37/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-464577445432171790500551/1250000000000000000000000:ℝ)*(thetaPowerMass 5 (9/128:ℝ) (37/512:ℝ)-(37/512:ℝ)*thetaPowerMass 4 (9/128:ℝ) (37/512:ℝ)) ≤
      thetaFirstModeFirst (37/512:ℝ)*(thetaPowerMass 5 (9/128:ℝ) (37/512:ℝ)-(37/512:ℝ)*thetaPowerMass 4 (9/128:ℝ) (37/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0059.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (9/128:ℝ) (37/512:ℝ)
    (37/512:ℝ) (2748895478593/50000000000000:ℝ) (-464577445432171790500551/1250000000000000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_036
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0109).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_036 :
    (∫ x in (9/128:ℝ)..(37/512:ℝ), x^4*thetaFirstMode x) ≤ (2792462487041039/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (9/128:ℝ) (37/512:ℝ)
    (5570714874669/100000000000000:ℝ) (5497797309893/100000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_036 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0109).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_037 :
    (614085490276587/200000000000000000000000:ℝ) ≤ ∫ x in (37/512:ℝ)..(19/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 4 (37/512:ℝ) (19/256:ℝ)) ≤
      thetaFirstModeFirst (23045391280593/318280722972160:ℝ)*(thetaPowerMass 5 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 4 (37/512:ℝ) (19/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0060.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (37/512:ℝ) (19/256:ℝ)
    (23045391280593/318280722972160:ℝ) (1373145106981/25000000000000:ℝ) (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_037
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0113).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_037 :
    (∫ x in (37/512:ℝ)..(19/256:ℝ), x^4*thetaFirstMode x) ≤ (767607791559539/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (37/512:ℝ) (19/256:ℝ)
    (5497797309893/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_037 (thetaFirstMode_refined_node_0109).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_038 :
    (673258104168399/200000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(39/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-9124608994890436277857697/25000000000000000000000000:ℝ)*(thetaPowerMass 5 (19/256:ℝ) (39/512:ℝ)-(39/512:ℝ)*thetaPowerMass 4 (19/256:ℝ) (39/512:ℝ)) ≤
      thetaFirstModeFirst (39/512:ℝ)*(thetaPowerMass 5 (19/256:ℝ) (39/512:ℝ)-(39/512:ℝ)*thetaPowerMass 4 (19/256:ℝ) (39/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0062.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (19/256:ℝ) (39/512:ℝ)
    (39/512:ℝ) (2676957945317/50000000000000:ℝ) (-9124608994890436277857697/25000000000000000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_038
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0115).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_038 :
    (∫ x in (19/256:ℝ)..(39/512:ℝ), x^4*thetaFirstMode x) ≤ (1683147268043671/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (19/256:ℝ) (39/512:ℝ)
    (1356383415313/25000000000000:ℝ) (2676961062807/50000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_038 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0115).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_039 :
    (3680512387303343/1000000000000000000000000:ℝ) ≤ ∫ x in (39/512:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x := by
  have hd : (-569934446770298107902169363121/1562500000000000000000000000000:ℝ)*(thetaPowerMass 5 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 4 (39/512:ℝ) (5/64:ℝ)) ≤
      thetaFirstModeFirst (36980403679791/484639493685760:ℝ)*(thetaPowerMass 5 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 4 (39/512:ℝ) (5/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0063.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (39/512:ℝ) (5/64:ℝ)
    (36980403679791/484639493685760:ℝ) (1069811902989/20000000000000:ℝ) (-569934446770298107902169363121/1562500000000000000000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_039
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0119).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_039 :
    (∫ x in (39/512:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x) ≤ (230032305534813/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (39/512:ℝ) (5/64:ℝ)
    (2676961062807/50000000000000:ℝ) (1056592171499/20000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_039 (thetaFirstMode_refined_node_0115).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_040 :
    (501692310005583/125000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(41/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1119828087648232286063499/3125000000000000000000000:ℝ)*(thetaPowerMass 5 (5/64:ℝ) (41/512:ℝ)-(41/512:ℝ)*thetaPowerMass 4 (5/64:ℝ) (41/512:ℝ)) ≤
      thetaFirstModeFirst (41/512:ℝ)*(thetaPowerMass 5 (5/64:ℝ) (41/512:ℝ)-(41/512:ℝ)*thetaPowerMass 4 (5/64:ℝ) (41/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0065.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (5/64:ℝ) (41/512:ℝ)
    (41/512:ℝ) (1303160462837/25000000000000:ℝ) (-1119828087648232286063499/3125000000000000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_040
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0121).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_040 :
    (∫ x in (5/64:ℝ)..(41/512:ℝ), x^4*thetaFirstMode x) ≤ (160541732494731/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (5/64:ℝ) (41/512:ℝ)
    (1056592171499/20000000000000:ℝ) (5212647969417/100000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_040 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0121).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_041 :
    (873158696622671/200000000000000000000000:ℝ) ≤ ∫ x in (41/512:ℝ)..(21/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 4 (41/512:ℝ) (21/256:ℝ)) ≤
      thetaFirstModeFirst (57958928803809/722636919247360:ℝ)*(thetaPowerMass 5 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 4 (41/512:ℝ) (21/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0066.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (41/512:ℝ) (21/256:ℝ)
    (57958928803809/722636919247360:ℝ) (208324196157/4000000000000:ℝ) (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_041
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0125).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_041 :
    (∫ x in (41/512:ℝ)..(21/256:ℝ), x^4*thetaFirstMode x) ≤ (4365798880675389/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (41/512:ℝ) (21/256:ℝ)
    (5212647969417/100000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_041 (thetaFirstMode_refined_node_0121).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_042 :
    (296105133357367/62500000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(43/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4396819323433717825048221/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (21/256:ℝ) (43/512:ℝ)-(43/512:ℝ)*thetaPowerMass 4 (21/256:ℝ) (43/512:ℝ)) ≤
      thetaFirstModeFirst (43/512:ℝ)*(thetaPowerMass 5 (21/256:ℝ) (43/512:ℝ)-(43/512:ℝ)*thetaPowerMass 4 (21/256:ℝ) (43/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0068.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (21/256:ℝ) (43/512:ℝ)
    (43/512:ℝ) (2536976786917/50000000000000:ℝ) (-4396819323433717825048221/12500000000000000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_042
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0127).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_042 :
    (∫ x in (21/256:ℝ)..(43/512:ℝ), x^4*thetaFirstMode x) ≤ (4737687891795897/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (21/256:ℝ) (43/512:ℝ)
    (5142981532319/100000000000000:ℝ) (5073959575833/100000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_042 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0127).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_043 :
    (2564793375409963/500000000000000000000000:ℝ) ≤ ∫ x in (43/512:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-17165169357063551396899444949/48828125000000000000000000000:ℝ)*(thetaPowerMass 5 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 4 (43/512:ℝ) (11/128:ℝ)) ≤
      thetaFirstModeFirst (88920376319007/1057252278300160:ℝ)*(thetaPowerMass 5 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 4 (43/512:ℝ) (11/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0069.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (43/512:ℝ) (11/128:ℝ)
    (88920376319007/1057252278300160:ℝ) (2534853049781/50000000000000:ℝ) (-17165169357063551396899444949/48828125000000000000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_043
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0131).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_043 :
    (∫ x in (43/512:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x) ≤ (5129593162218173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (43/512:ℝ) (11/128:ℝ)
    (5073959575833/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_043 (thetaFirstMode_refined_node_0127).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_044 :
    (2770934285875513/500000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(45/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4314846353712531568004921/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (11/128:ℝ) (45/512:ℝ)-(45/512:ℝ)*thetaPowerMass 4 (11/128:ℝ) (45/512:ℝ)) ≤
      thetaFirstModeFirst (45/512:ℝ)*(thetaPowerMass 5 (11/128:ℝ) (45/512:ℝ)-(45/512:ℝ)*thetaPowerMass 4 (11/128:ℝ) (45/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0071.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (11/128:ℝ) (45/512:ℝ)
    (45/512:ℝ) (1234458783113/25000000000000:ℝ) (-4314846353712531568004921/12500000000000000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_044
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0133).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_044 :
    (∫ x in (11/128:ℝ)..(45/512:ℝ), x^4*thetaFirstMode x) ≤ (1385468842769561/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (11/128:ℝ) (45/512:ℝ)
    (5005580088729/100000000000000:ℝ) (4937841019247/100000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_044 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0133).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_045 :
    (1194972980987503/200000000000000000000000:ℝ) ≤ ∫ x in (45/512:ℝ)..(23/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-539054799777053651949066501611/1562500000000000000000000000000:ℝ)*(thetaPowerMass 5 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 4 (45/512:ℝ) (23/256:ℝ)) ≤
      thetaFirstModeFirst (26759859160005/304068323159552:ℝ)*(thetaPowerMass 5 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 4 (45/512:ℝ) (23/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0072.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (45/512:ℝ) (23/256:ℝ)
    (26759859160005/304068323159552:ℝ) (1233462777513/25000000000000:ℝ) (-539054799777053651949066501611/1562500000000000000000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_045
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0137).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_045 :
    (∫ x in (45/512:ℝ)..(23/256:ℝ), x^4*thetaFirstMode x) ≤ (5974872455214361/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (45/512:ℝ) (23/256:ℝ)
    (4937841019247/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_045 (thetaFirstMode_refined_node_0133).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_046 :
    (642889109131573/100000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(47/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1693365597577077854118173/5000000000000000000000000:ℝ)*(thetaPowerMass 5 (23/256:ℝ) (47/512:ℝ)-(47/512:ℝ)*thetaPowerMass 4 (23/256:ℝ) (47/512:ℝ)) ≤
      thetaFirstModeFirst (47/512:ℝ)*(thetaPowerMass 5 (23/256:ℝ) (47/512:ℝ)-(47/512:ℝ)*thetaPowerMass 4 (23/256:ℝ) (47/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0074.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (23/256:ℝ) (47/512:ℝ)
    (47/512:ℝ) (960853990651/20000000000000:ℝ) (-1693365597577077854118173/5000000000000000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_046
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0139).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_046 :
    (∫ x in (23/256:ℝ)..(47/512:ℝ), x^4*thetaFirstMode x) ≤ (642889905400459/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (23/256:ℝ) (47/512:ℝ)
    (194829611019/4000000000000:ℝ) (4804275725737/100000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_046 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0139).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_047 :
    (3452118590821347/500000000000000000000000:ℝ) ≤ ∫ x in (47/512:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ)*(thetaPowerMass 5 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 4 (47/512:ℝ) (3/32:ℝ)) ≤
      thetaFirstModeFirst (197791827765543/2152076489628160:ℝ)*(thetaPowerMass 5 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 4 (47/512:ℝ) (3/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0075.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (47/512:ℝ) (3/32:ℝ)
    (197791827765543/2152076489628160:ℝ) (4800526634211/100000000000000:ℝ) (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_047
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0143).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_047 :
    (∫ x in (47/512:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x) ≤ (863030750391891/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (47/512:ℝ) (3/32:ℝ)
    (4804275725737/100000000000000:ℝ) (947689039803/20000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_047 (thetaFirstMode_refined_node_0139).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_048 :
    (925146327731557/125000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(49/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-3322033918695685788842471/10000000000000000000000000:ℝ)*(thetaPowerMass 5 (3/32:ℝ) (49/512:ℝ)-(49/512:ℝ)*thetaPowerMass 4 (3/32:ℝ) (49/512:ℝ)) ≤
      thetaFirstModeFirst (49/512:ℝ)*(thetaPowerMass 5 (3/32:ℝ) (49/512:ℝ)-(49/512:ℝ)*thetaPowerMass 4 (3/32:ℝ) (49/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0077.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (3/32:ℝ) (49/512:ℝ)
    (49/512:ℝ) (934648165241/20000000000000:ℝ) (-3322033918695685788842471/10000000000000000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_048
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0145).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_048 :
    (∫ x in (3/32:ℝ)..(49/512:ℝ), x^4*thetaFirstMode x) ≤ (7401179876370763/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (3/32:ℝ) (49/512:ℝ)
    (947689039803/20000000000000:ℝ) (4673246485291/100000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_048 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0145).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_049 :
    (247497885697597/31250000000000000000000:ℝ) ≤ ∫ x in (49/512:ℝ)..(25/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ)*(thetaPowerMass 5 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 4 (49/512:ℝ) (25/256:ℝ)) ≤
      thetaFirstModeFirst (287676456077241/3002597697026560:ℝ)*(thetaPowerMass 5 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 4 (49/512:ℝ) (25/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0078.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (49/512:ℝ) (25/256:ℝ)
    (287676456077241/3002597697026560:ℝ) (2334859103349/50000000000000:ℝ) (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_049
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0149).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_049 :
    (∫ x in (49/512:ℝ)..(25/256:ℝ), x^4*thetaFirstMode x) ≤ (1583988514899971/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (49/512:ℝ) (25/256:ℝ)
    (4673246485291/100000000000000:ℝ) (4608677336011/100000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_049 (thetaFirstMode_refined_node_0145).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_050 :
    (4230370139841861/500000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(51/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4072251310286375767761627/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (25/256:ℝ) (51/512:ℝ)-(51/512:ℝ)*thetaPowerMass 4 (25/256:ℝ) (51/512:ℝ)) ≤
      thetaFirstModeFirst (51/512:ℝ)*(thetaPowerMass 5 (25/256:ℝ) (51/512:ℝ)-(51/512:ℝ)*thetaPowerMass 4 (25/256:ℝ) (51/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0080.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (25/256:ℝ) (51/512:ℝ)
    (51/512:ℝ) (1136182479459/25000000000000:ℝ) (-4072251310286375767761627/12500000000000000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_050
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0151).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_050 :
    (∫ x in (25/256:ℝ)..(51/512:ℝ), x^4*thetaFirstMode x) ≤ (4230375480283581/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (25/256:ℝ) (51/512:ℝ)
    (4608677336011/100000000000000:ℝ) (908947092893/20000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_050 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0151).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_051 :
    (2255946187805467/250000000000000000000000:ℝ) ≤ ∫ x in (51/512:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 4 (51/512:ℝ) (13/128:ℝ)) ≤
      thetaFirstModeFirst (412196976114759/4133904418178560:ℝ)*(thetaPowerMass 5 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 4 (51/512:ℝ) (13/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0081.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (51/512:ℝ) (13/128:ℝ)
    (412196976114759/4133904418178560:ℝ) (567676289121/12500000000000:ℝ) (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_051
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0155).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_051 :
    (∫ x in (51/512:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x) ≤ (1127974567550623/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (51/512:ℝ) (13/128:ℝ)
    (908947092893/20000000000000:ℝ) (560177318273/12500000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_051 (thetaFirstMode_refined_node_0151).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_052 :
    (960923294014143/100000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(53/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-3992560049659117735503699/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (13/128:ℝ) (53/512:ℝ)-(53/512:ℝ)*thetaPowerMass 4 (13/128:ℝ) (53/512:ℝ)) ≤
      thetaFirstModeFirst (53/512:ℝ)*(thetaPowerMass 5 (13/128:ℝ) (53/512:ℝ)-(53/512:ℝ)*thetaPowerMass 4 (13/128:ℝ) (53/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0083.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (13/128:ℝ) (53/512:ℝ)
    (53/512:ℝ) (4418718784289/100000000000000:ℝ) (-3992560049659117735503699/12500000000000000000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_052
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0157).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_052 :
    (∫ x in (13/128:ℝ)..(53/512:ℝ), x^4*thetaFirstMode x) ≤ (9609245187694987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (13/128:ℝ) (53/512:ℝ)
    (560177318273/12500000000000:ℝ) (138085131857/3125000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_052 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0157).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_053 :
    (2554305853345603/250000000000000000000000:ℝ) ≤ ∫ x in (53/512:ℝ)..(27/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 4 (53/512:ℝ) (27/256:ℝ)) ≤
      thetaFirstModeFirst (582516327971457/5622000143388160:ℝ)*(thetaPowerMass 5 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 4 (53/512:ℝ) (27/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0084.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (53/512:ℝ) (27/256:ℝ)
    (582516327971457/5622000143388160:ℝ) (4415586481659/100000000000000:ℝ) (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_053
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0161).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_053 :
    (∫ x in (53/512:ℝ)..(27/256:ℝ), x^4*thetaFirstMode x) ≤ (10217236912500527/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (53/512:ℝ) (27/256:ℝ)
    (138085131857/3125000000000:ℝ) (4356650085507/100000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_053 (thetaFirstMode_refined_node_0157).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_054 :
    (10847871712517919/1000000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(55/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-15653950004432657253999/50000000000000000000000:ℝ)*(thetaPowerMass 5 (27/256:ℝ) (55/512:ℝ)-(55/512:ℝ)*thetaPowerMass 4 (27/256:ℝ) (55/512:ℝ)) ≤
      thetaFirstModeFirst (55/512:ℝ)*(thetaPowerMass 5 (27/256:ℝ) (55/512:ℝ)-(55/512:ℝ)*thetaPowerMass 4 (27/256:ℝ) (55/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0086.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (27/256:ℝ) (55/512:ℝ)
    (55/512:ℝ) (2147594192367/50000000000000:ℝ) (-15653950004432657253999/50000000000000000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_054
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0163).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_054 :
    (∫ x in (27/256:ℝ)..(55/512:ℝ), x^4*thetaFirstMode x) ≤ (10847885672449631/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (27/256:ℝ) (55/512:ℝ)
    (4356650085507/100000000000000:ℝ) (53689921367/1250000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_054 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0163).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_055 :
    (11501263857256939/1000000000000000000000000:ℝ) ≤ ∫ x in (55/512:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x := by
  have hd : (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 4 (55/512:ℝ) (7/64:ℝ)) ≤
      thetaFirstModeFirst (162550142281395/1511863535831552:ℝ)*(thetaPowerMass 5 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 4 (55/512:ℝ) (7/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0087.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (55/512:ℝ) (7/64:ℝ)
    (162550142281395/1511863535831552:ℝ) (134132167511/3125000000000:ℝ) (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_055
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0167).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_055 :
    (∫ x in (55/512:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x) ≤ (2300255845106733/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (55/512:ℝ) (7/64:ℝ)
    (53689921367/1250000000000:ℝ) (2117176309913/50000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_055 (thetaFirstMode_refined_node_0163).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_056 :
    (12177463200603771/1000000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(57/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1917526051108501105680521/6250000000000000000000000:ℝ)*(thetaPowerMass 5 (7/64:ℝ) (57/512:ℝ)-(57/512:ℝ)*thetaPowerMass 4 (7/64:ℝ) (57/512:ℝ)) ≤
      thetaFirstModeFirst (57/512:ℝ)*(thetaPowerMass 5 (7/64:ℝ) (57/512:ℝ)-(57/512:ℝ)*thetaPowerMass 4 (7/64:ℝ) (57/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0089.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (7/64:ℝ) (57/512:ℝ)
    (57/512:ℝ) (4174119095129/100000000000000:ℝ) (-1917526051108501105680521/6250000000000000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_056
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0169).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_056 :
    (∫ x in (7/64:ℝ)..(57/512:ℝ), x^4*thetaFirstMode x) ≤ (12177479023680397/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (7/64:ℝ) (57/512:ℝ)
    (2117176309913/50000000000000:ℝ) (4174124310253/100000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_056 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0169).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_057 :
    (6438251371781423/500000000000000000000000:ℝ) ≤ ∫ x in (57/512:ℝ)..(29/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 4 (57/512:ℝ) (29/256:ℝ)) ≤
      thetaFirstModeFirst (1120594199442993/10057446457500160:ℝ)*(thetaPowerMass 5 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 4 (57/512:ℝ) (29/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0090.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (57/512:ℝ) (29/256:ℝ)
    (1120594199442993/10057446457500160:ℝ) (4171320778711/100000000000000:ℝ) (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_057
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0173).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_057 :
    (∫ x in (57/512:ℝ)..(29/256:ℝ), x^4*thetaFirstMode x) ≤ (321913003653067/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (57/512:ℝ) (29/256:ℝ)
    (4174124310253/100000000000000:ℝ) (411450623883/10000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_057 (thetaFirstMode_refined_node_0169).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_058 :
    (3399598357458621/250000000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(59/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-751454366461280770506813/2500000000000000000000000:ℝ)*(thetaPowerMass 5 (29/256:ℝ) (59/512:ℝ)-(59/512:ℝ)*thetaPowerMass 4 (29/256:ℝ) (59/512:ℝ)) ≤
      thetaFirstModeFirst (59/512:ℝ)*(thetaPowerMass 5 (29/256:ℝ) (59/512:ℝ)-(59/512:ℝ)*thetaPowerMass 4 (29/256:ℝ) (59/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0092.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (29/256:ℝ) (59/512:ℝ)
    (59/512:ℝ) (405549072243/10000000000000:ℝ) (-751454366461280770506813/2500000000000000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_058
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0175).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_058 :
    (∫ x in (29/256:ℝ)..(59/512:ℝ), x^4*thetaFirstMode x) ≤ (6799205635716643/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (29/256:ℝ) (59/512:ℝ)
    (411450623883/10000000000000:ℝ) (4055495829081/100000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_058 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0175).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_059 :
    (7171557539983767/500000000000000000000000:ℝ) ≤ ∫ x in (59/512:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 4 (59/512:ℝ) (15/128:ℝ)) ≤
      thetaFirstModeFirst (1528044900298191/13250186301775360:ℝ)*(thetaPowerMass 5 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 4 (59/512:ℝ) (15/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0093.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (59/512:ℝ) (15/128:ℝ)
    (1528044900298191/13250186301775360:ℝ) (506605225251/12500000000000:ℝ) (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_059
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0179).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_059 :
    (∫ x in (59/512:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x) ≤ (2868626937519071/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (59/512:ℝ) (15/128:ℝ)
    (4055495829081/100000000000000:ℝ) (499636308793/12500000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_059 (thetaFirstMode_refined_node_0175).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_060 :
    (7555313159595349/500000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(61/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1472065680580774860715491/5000000000000000000000000:ℝ)*(thetaPowerMass 5 (15/128:ℝ) (61/512:ℝ)-(61/512:ℝ)*thetaPowerMass 4 (15/128:ℝ) (61/512:ℝ)) ≤
      thetaFirstModeFirst (61/512:ℝ)*(thetaPowerMass 5 (15/128:ℝ) (61/512:ℝ)-(61/512:ℝ)*thetaPowerMass 4 (15/128:ℝ) (61/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0095.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (15/128:ℝ) (61/512:ℝ)
    (61/512:ℝ) (3939282518997/100000000000000:ℝ) (-1472065680580774860715491/5000000000000000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_060
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0181).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_060 :
    (∫ x in (15/128:ℝ)..(61/512:ℝ), x^4*thetaFirstMode x) ≤ (236103849045231/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (15/128:ℝ) (61/512:ℝ)
    (499636308793/12500000000000:ℝ) (3939287518223/100000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_060 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0181).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_061 :
    (15900853920062001/1000000000000000000000000:ℝ) ≤ ∫ x in (61/512:ℝ)..(31/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 4 (61/512:ℝ) (31/256:ℝ)) ≤
      thetaFirstModeFirst (2062244582827209/17296952731317760:ℝ)*(thetaPowerMass 5 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 4 (61/512:ℝ) (31/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0096.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (61/512:ℝ) (31/256:ℝ)
    (2062244582827209/17296952731317760:ℝ) (3936772777441/100000000000000:ℝ) (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_061
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0185).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_061 :
    (∫ x in (61/512:ℝ)..(31/256:ℝ), x^4*thetaFirstMode x) ≤ (7950437954335591/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (61/512:ℝ) (31/256:ℝ)
    (3939287518223/100000000000000:ℝ) (3882084295049/100000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_061 (thetaFirstMode_refined_node_0181).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_062 :
    (4178426143960951/250000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(63/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-360374624006484139939341/1250000000000000000000000:ℝ)*(thetaPowerMass 5 (31/256:ℝ) (63/512:ℝ)-(63/512:ℝ)*thetaPowerMass 4 (31/256:ℝ) (63/512:ℝ)) ≤
      thetaFirstModeFirst (63/512:ℝ)*(thetaPowerMass 5 (31/256:ℝ) (63/512:ℝ)-(63/512:ℝ)*thetaPowerMass 4 (31/256:ℝ) (63/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0098.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (31/256:ℝ) (63/512:ℝ)
    (63/512:ℝ) (382547319749/10000000000000:ℝ) (-360374624006484139939341/1250000000000000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_062
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0187).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_062 :
    (∫ x in (31/256:ℝ)..(63/512:ℝ), x^4*thetaFirstMode x) ≤ (16713726937025683/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (31/256:ℝ) (63/512:ℝ)
    (3882084295049/100000000000000:ℝ) (3825478090361/100000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_062 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0187).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_063 :
    (17549052422218087/1000000000000000000000000:ℝ) ≤ ∫ x in (63/512:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x := by
  have hd : (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 4 (63/512:ℝ) (1/8:ℝ)) ≤
      thetaFirstModeFirst (2756444578756407/22386559816092160:ℝ)*(thetaPowerMass 5 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 4 (63/512:ℝ) (1/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0099.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (63/512:ℝ) (1/8:ℝ)
    (2756444578756407/22386559816092160:ℝ) (1911546687323/50000000000000:ℝ) (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_063
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0191).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_063 :
    (∫ x in (63/512:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x) ≤ (1754907697257129/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (63/512:ℝ) (1/8:ℝ)
    (3825478090361/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_063 (thetaFirstMode_refined_node_0187).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
