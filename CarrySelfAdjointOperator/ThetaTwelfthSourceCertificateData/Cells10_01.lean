import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative01
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative02
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative03

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_032 :
    (121342317/1000000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(33/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4814060781548974449617637/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (1/16:ℝ) (33/512:ℝ)-(33/512:ℝ)*thetaPowerMass 10 (1/16:ℝ) (33/512:ℝ)) ≤
      thetaFirstModeFirst (33/512:ℝ)*(thetaPowerMass 11 (1/16:ℝ) (33/512:ℝ)-(33/512:ℝ)*thetaPowerMass 10 (1/16:ℝ) (33/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0053.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (1/16:ℝ) (33/512:ℝ)
    (33/512:ℝ) (1448350466289/25000000000000:ℝ) (-4814060781548974449617637/12500000000000000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_032
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0097).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_032 :
    (∫ x in (1/16:ℝ)..(33/512:ℝ), x^10*thetaFirstMode x) ≤ (121342459/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/16:ℝ) (33/512:ℝ)
    (2934479429249/50000000000000:ℝ) (5793408455657/100000000000000:ℝ) (432997527252346110519427/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_032 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0097).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_033 :
    (162144127/1000000000000000000000000:ℝ) ≤ ∫ x in (33/512:ℝ)..(17/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 10 (33/512:ℝ) (17/256:ℝ)) ≤
      thetaFirstModeFirst (8248340454057/127663103388160:ℝ)*(thetaPowerMass 11 (33/512:ℝ) (17/256:ℝ)-(8248340454057/127663103388160:ℝ)*thetaPowerMass 10 (33/512:ℝ) (17/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0054.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (33/512:ℝ) (17/256:ℝ)
    (8248340454057/127663103388160:ℝ) (1157470820943/20000000000000:ℝ) (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_033
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0101).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_033 :
    (∫ x in (33/512:ℝ)..(17/256:ℝ), x^10*thetaFirstMode x) ≤ (506701/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (33/512:ℝ) (17/256:ℝ)
    (5793408455657/100000000000000:ℝ) (2859259375861/50000000000000:ℝ) (215964459059113710098031/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_033 (thetaFirstMode_refined_node_0097).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_034 :
    (214734783/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(35/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1182425138294745884210001/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (17/256:ℝ) (35/512:ℝ)-(35/512:ℝ)*thetaPowerMass 10 (17/256:ℝ) (35/512:ℝ)) ≤
      thetaFirstModeFirst (35/512:ℝ)*(thetaPowerMass 11 (17/256:ℝ) (35/512:ℝ)-(35/512:ℝ)*thetaPowerMass 10 (17/256:ℝ) (35/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0056.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (17/256:ℝ) (35/512:ℝ)
    (35/512:ℝ) (1411070411223/25000000000000:ℝ) (-1182425138294745884210001/3125000000000000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_034
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0103).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_034 :
    (∫ x in (17/256:ℝ)..(35/512:ℝ), x^10*thetaFirstMode x) ≤ (42947007/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/256:ℝ) (35/512:ℝ)
    (2859259375861/50000000000000:ℝ) (1128857623223/20000000000000:ℝ) (1723326832846077234256913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_034 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0103).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_035 :
    (56398313/200000000000000000000000:ℝ) ≤ ∫ x in (35/512:ℝ)..(9/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 10 (35/512:ℝ) (9/128:ℝ)) ≤
      thetaFirstModeFirst (2798051987115/40842963901952:ℝ)*(thetaPowerMass 11 (35/512:ℝ) (9/128:ℝ)-(2798051987115/40842963901952:ℝ)*thetaPowerMass 10 (35/512:ℝ) (9/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0057.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (35/512:ℝ) (9/128:ℝ)
    (2798051987115/40842963901952:ℝ) (5638676396401/100000000000000:ℝ) (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_035
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0107).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_035 :
    (∫ x in (35/512:ℝ)..(9/128:ℝ), x^10*thetaFirstMode x) ≤ (8812247/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (35/512:ℝ) (9/128:ℝ)
    (1128857623223/20000000000000:ℝ) (5570714874669/100000000000000:ℝ) (859412213423130417653039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_035 (thetaFirstMode_refined_node_0103).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_036 :
    (183685317/500000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(37/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-464577445432171790500551/1250000000000000000000000:ℝ)*(thetaPowerMass 11 (9/128:ℝ) (37/512:ℝ)-(37/512:ℝ)*thetaPowerMass 10 (9/128:ℝ) (37/512:ℝ)) ≤
      thetaFirstModeFirst (37/512:ℝ)*(thetaPowerMass 11 (9/128:ℝ) (37/512:ℝ)-(37/512:ℝ)*thetaPowerMass 10 (9/128:ℝ) (37/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0059.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (9/128:ℝ) (37/512:ℝ)
    (37/512:ℝ) (2748895478593/50000000000000:ℝ) (-464577445432171790500551/1250000000000000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_036
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0109).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_036 :
    (∫ x in (9/128:ℝ)..(37/512:ℝ), x^10*thetaFirstMode x) ≤ (367371069/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/128:ℝ) (37/512:ℝ)
    (5570714874669/100000000000000:ℝ) (5497797309893/100000000000000:ℝ) (13713674475179974256373/8000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_036 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0109).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_037 :
    (118749827/250000000000000000000000:ℝ) ≤ ∫ x in (37/512:ℝ)..(19/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 10 (37/512:ℝ) (19/256:ℝ)) ≤
      thetaFirstModeFirst (23045391280593/318280722972160:ℝ)*(thetaPowerMass 11 (37/512:ℝ) (19/256:ℝ)-(23045391280593/318280722972160:ℝ)*thetaPowerMass 10 (37/512:ℝ) (19/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0060.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (37/512:ℝ) (19/256:ℝ)
    (23045391280593/318280722972160:ℝ) (1373145106981/25000000000000:ℝ) (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_037
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0113).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_037 :
    (∫ x in (37/512:ℝ)..(19/256:ℝ), x^10*thetaFirstMode x) ≤ (118749971/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (37/512:ℝ) (19/256:ℝ)
    (5497797309893/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1709482353465349946201123/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_037 (thetaFirstMode_refined_node_0109).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_038 :
    (609779469/1000000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(39/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-9124608994890436277857697/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (19/256:ℝ) (39/512:ℝ)-(39/512:ℝ)*thetaPowerMass 10 (19/256:ℝ) (39/512:ℝ)) ≤
      thetaFirstModeFirst (39/512:ℝ)*(thetaPowerMass 11 (19/256:ℝ) (39/512:ℝ)-(39/512:ℝ)*thetaPowerMass 10 (19/256:ℝ) (39/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0062.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (19/256:ℝ) (39/512:ℝ)
    (39/512:ℝ) (2676957945317/50000000000000:ℝ) (-9124608994890436277857697/25000000000000000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_038
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0115).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_038 :
    (∫ x in (19/256:ℝ)..(39/512:ℝ), x^10*thetaFirstMode x) ≤ (609780197/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (19/256:ℝ) (39/512:ℝ)
    (1356383415313/25000000000000:ℝ) (2676961062807/50000000000000:ℝ) (1704644449940327522104199/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_038 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0115).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_039 :
    (777502407/1000000000000000000000000:ℝ) ≤ ∫ x in (39/512:ℝ)..(5/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-569934446770298107902169363121/1562500000000000000000000000000:ℝ)*(thetaPowerMass 11 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 10 (39/512:ℝ) (5/64:ℝ)) ≤
      thetaFirstModeFirst (36980403679791/484639493685760:ℝ)*(thetaPowerMass 11 (39/512:ℝ) (5/64:ℝ)-(36980403679791/484639493685760:ℝ)*thetaPowerMass 10 (39/512:ℝ) (5/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0063.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (39/512:ℝ) (5/64:ℝ)
    (36980403679791/484639493685760:ℝ) (1069811902989/20000000000000:ℝ) (-569934446770298107902169363121/1562500000000000000000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_039
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0119).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_039 :
    (∫ x in (39/512:ℝ)..(5/64:ℝ), x^10*thetaFirstMode x) ≤ (1214849/1562500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (39/512:ℝ) (5/64:ℝ)
    (2676961062807/50000000000000:ℝ) (1056592171499/20000000000000:ℝ) (849848253722663298519713/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_039 (thetaFirstMode_refined_node_0115).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_040 :
    (984976589/1000000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(41/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1119828087648232286063499/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (5/64:ℝ) (41/512:ℝ)-(41/512:ℝ)*thetaPowerMass 10 (5/64:ℝ) (41/512:ℝ)) ≤
      thetaFirstModeFirst (41/512:ℝ)*(thetaPowerMass 11 (5/64:ℝ) (41/512:ℝ)-(41/512:ℝ)*thetaPowerMass 10 (5/64:ℝ) (41/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0065.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (5/64:ℝ) (41/512:ℝ)
    (41/512:ℝ) (1303160462837/25000000000000:ℝ) (-1119828087648232286063499/3125000000000000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_040
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0121).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_040 :
    (∫ x in (5/64:ℝ)..(41/512:ℝ), x^10*thetaFirstMode x) ≤ (39399111/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/64:ℝ) (41/512:ℝ)
    (1056592171499/20000000000000:ℝ) (5212647969417/100000000000000:ℝ) (1694639452171312002093737/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_040 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0121).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_041 :
    (1240168303/1000000000000000000000000:ℝ) ≤ ∫ x in (41/512:ℝ)..(21/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 10 (41/512:ℝ) (21/256:ℝ)) ≤
      thetaFirstModeFirst (57958928803809/722636919247360:ℝ)*(thetaPowerMass 11 (41/512:ℝ) (21/256:ℝ)-(57958928803809/722636919247360:ℝ)*thetaPowerMass 10 (41/512:ℝ) (21/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0066.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (41/512:ℝ) (21/256:ℝ)
    (57958928803809/722636919247360:ℝ) (208324196157/4000000000000:ℝ) (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_041
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0125).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_041 :
    (∫ x in (41/512:ℝ)..(21/256:ℝ), x^10*thetaFirstMode x) ≤ (1240169839/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (41/512:ℝ) (21/256:ℝ)
    (5212647969417/100000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1689474227727350749544013/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_041 (thetaFirstMode_refined_node_0121).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_042 :
    (1552357211/1000000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(43/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4396819323433717825048221/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (21/256:ℝ) (43/512:ℝ)-(43/512:ℝ)*thetaPowerMass 10 (21/256:ℝ) (43/512:ℝ)) ≤
      thetaFirstModeFirst (43/512:ℝ)*(thetaPowerMass 11 (21/256:ℝ) (43/512:ℝ)-(43/512:ℝ)*thetaPowerMass 10 (21/256:ℝ) (43/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0068.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (21/256:ℝ) (43/512:ℝ)
    (43/512:ℝ) (2536976786917/50000000000000:ℝ) (-4396819323433717825048221/12500000000000000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_042
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0127).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_042 :
    (∫ x in (21/256:ℝ)..(43/512:ℝ), x^10*thetaFirstMode x) ≤ (776179549/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (21/256:ℝ) (43/512:ℝ)
    (5142981532319/100000000000000:ℝ) (5073959575833/100000000000000:ℝ) (1684201794927974646282499/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_042 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0127).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_043 :
    (1932306063/1000000000000000000000000:ℝ) ≤ ∫ x in (43/512:ℝ)..(11/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-17165169357063551396899444949/48828125000000000000000000000:ℝ)*(thetaPowerMass 11 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 10 (43/512:ℝ) (11/128:ℝ)) ≤
      thetaFirstModeFirst (88920376319007/1057252278300160:ℝ)*(thetaPowerMass 11 (43/512:ℝ) (11/128:ℝ)-(88920376319007/1057252278300160:ℝ)*thetaPowerMass 10 (43/512:ℝ) (11/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0069.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (43/512:ℝ) (11/128:ℝ)
    (88920376319007/1057252278300160:ℝ) (2534853049781/50000000000000:ℝ) (-17165169357063551396899444949/48828125000000000000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_043
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0131).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_043 :
    (∫ x in (43/512:ℝ)..(11/128:ℝ), x^10*thetaFirstMode x) ≤ (966154241/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (43/512:ℝ) (11/128:ℝ)
    (5073959575833/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (335764626330188313888433/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_043 (thetaFirstMode_refined_node_0127).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_044 :
    (1196223761/500000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(45/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4314846353712531568004921/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (11/128:ℝ) (45/512:ℝ)-(45/512:ℝ)*thetaPowerMass 10 (11/128:ℝ) (45/512:ℝ)) ≤
      thetaFirstModeFirst (45/512:ℝ)*(thetaPowerMass 11 (11/128:ℝ) (45/512:ℝ)-(45/512:ℝ)*thetaPowerMass 10 (11/128:ℝ) (45/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0071.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (11/128:ℝ) (45/512:ℝ)
    (45/512:ℝ) (1234458783113/25000000000000:ℝ) (-4314846353712531568004921/12500000000000000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_044
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0133).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_044 :
    (∫ x in (11/128:ℝ)..(45/512:ℝ), x^10*thetaFirstMode x) ≤ (299056307/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/128:ℝ) (45/512:ℝ)
    (5005580088729/100000000000000:ℝ) (4937841019247/100000000000000:ℝ) (1673339232620103013215101/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_044 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0133).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_045 :
    (2947086197/1000000000000000000000000:ℝ) ≤ ∫ x in (45/512:ℝ)..(23/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-539054799777053651949066501611/1562500000000000000000000000000:ℝ)*(thetaPowerMass 11 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 10 (45/512:ℝ) (23/256:ℝ)) ≤
      thetaFirstModeFirst (26759859160005/304068323159552:ℝ)*(thetaPowerMass 11 (45/512:ℝ) (23/256:ℝ)-(26759859160005/304068323159552:ℝ)*thetaPowerMass 10 (45/512:ℝ) (23/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0072.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (45/512:ℝ) (23/256:ℝ)
    (26759859160005/304068323159552:ℝ) (1233462777513/25000000000000:ℝ) (-539054799777053651949066501611/1562500000000000000000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_045
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0137).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_045 :
    (∫ x in (45/512:ℝ)..(23/256:ℝ), x^10*thetaFirstMode x) ≤ (2947089927/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (45/512:ℝ) (23/256:ℝ)
    (4937841019247/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (416937777305657781247859/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_045 (thetaFirstMode_refined_node_0133).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_046 :
    (3612620267/1000000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(47/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1693365597577077854118173/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (23/256:ℝ) (47/512:ℝ)-(47/512:ℝ)*thetaPowerMass 10 (23/256:ℝ) (47/512:ℝ)) ≤
      thetaFirstModeFirst (47/512:ℝ)*(thetaPowerMass 11 (23/256:ℝ) (47/512:ℝ)-(47/512:ℝ)*thetaPowerMass 10 (23/256:ℝ) (47/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0074.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (23/256:ℝ) (47/512:ℝ)
    (47/512:ℝ) (960853990651/20000000000000:ℝ) (-1693365597577077854118173/5000000000000000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_046
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0139).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_046 :
    (∫ x in (23/256:ℝ)..(47/512:ℝ), x^10*thetaFirstMode x) ≤ (180631237/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/256:ℝ) (47/512:ℝ)
    (194829611019/4000000000000:ℝ) (4804275725737/100000000000000:ℝ) (1662059789304034033005443/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_046 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0139).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_047 :
    (4407778947/1000000000000000000000000:ℝ) ≤ ∫ x in (47/512:ℝ)..(3/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 10 (47/512:ℝ) (3/32:ℝ)) ≤
      thetaFirstModeFirst (197791827765543/2152076489628160:ℝ)*(thetaPowerMass 11 (47/512:ℝ) (3/32:ℝ)-(197791827765543/2152076489628160:ℝ)*thetaPowerMass 10 (47/512:ℝ) (3/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0075.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (47/512:ℝ) (3/32:ℝ)
    (197791827765543/2152076489628160:ℝ) (4800526634211/100000000000000:ℝ) (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_047
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0143).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_047 :
    (∫ x in (47/512:ℝ)..(3/32:ℝ), x^10*thetaFirstMode x) ≤ (4407784587/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (47/512:ℝ) (3/32:ℝ)
    (4804275725737/100000000000000:ℝ) (947689039803/20000000000000:ℝ) (828133158490629237942809/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_047 (thetaFirstMode_refined_node_0139).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_048 :
    (5353882437/1000000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(49/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3322033918695685788842471/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (3/32:ℝ) (49/512:ℝ)-(49/512:ℝ)*thetaPowerMass 10 (3/32:ℝ) (49/512:ℝ)) ≤
      thetaFirstModeFirst (49/512:ℝ)*(thetaPowerMass 11 (3/32:ℝ) (49/512:ℝ)-(49/512:ℝ)*thetaPowerMass 10 (3/32:ℝ) (49/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0077.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (3/32:ℝ) (49/512:ℝ)
    (49/512:ℝ) (934648165241/20000000000000:ℝ) (-3322033918695685788842471/10000000000000000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_048
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0145).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_048 :
    (∫ x in (3/32:ℝ)..(49/512:ℝ), x^10*thetaFirstMode x) ≤ (669236141/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/32:ℝ) (49/512:ℝ)
    (947689039803/20000000000000:ℝ) (4673246485291/100000000000000:ℝ) (1650371752412638040310371/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_048 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0145).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_049 :
    (1295023543/200000000000000000000000:ℝ) ≤ ∫ x in (49/512:ℝ)..(25/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 10 (49/512:ℝ) (25/256:ℝ)) ≤
      thetaFirstModeFirst (287676456077241/3002597697026560:ℝ)*(thetaPowerMass 11 (49/512:ℝ) (25/256:ℝ)-(287676456077241/3002597697026560:ℝ)*thetaPowerMass 10 (49/512:ℝ) (25/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0078.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (49/512:ℝ) (25/256:ℝ)
    (287676456077241/3002597697026560:ℝ) (2334859103349/50000000000000:ℝ) (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_049
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0149).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_049 :
    (∫ x in (49/512:ℝ)..(25/256:ℝ), x^10*thetaFirstMode x) ≤ (1618781523/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (49/512:ℝ) (25/256:ℝ)
    (4673246485291/100000000000000:ℝ) (4608677336011/100000000000000:ℝ) (411094292900009968783053/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_049 (thetaFirstMode_refined_node_0145).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_050 :
    (7798840289/1000000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(51/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4072251310286375767761627/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (25/256:ℝ) (51/512:ℝ)-(51/512:ℝ)*thetaPowerMass 10 (25/256:ℝ) (51/512:ℝ)) ≤
      thetaFirstModeFirst (51/512:ℝ)*(thetaPowerMass 11 (25/256:ℝ) (51/512:ℝ)-(51/512:ℝ)*thetaPowerMass 10 (25/256:ℝ) (51/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0080.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (25/256:ℝ) (51/512:ℝ)
    (51/512:ℝ) (1136182479459/25000000000000:ℝ) (-4072251310286375767761627/12500000000000000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_050
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0151).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_050 :
    (∫ x in (25/256:ℝ)..(51/512:ℝ), x^10*thetaFirstMode x) ≤ (7798850129/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/256:ℝ) (51/512:ℝ)
    (4608677336011/100000000000000:ℝ) (908947092893/20000000000000:ℝ) (819141833083700760937913/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_050 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0151).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_051 :
    (9355890877/1000000000000000000000000:ℝ) ≤ ∫ x in (51/512:ℝ)..(13/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 10 (51/512:ℝ) (13/128:ℝ)) ≤
      thetaFirstModeFirst (412196976114759/4133904418178560:ℝ)*(thetaPowerMass 11 (51/512:ℝ) (13/128:ℝ)-(412196976114759/4133904418178560:ℝ)*thetaPowerMass 10 (51/512:ℝ) (13/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0081.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (51/512:ℝ) (13/128:ℝ)
    (412196976114759/4133904418178560:ℝ) (567676289121/12500000000000:ℝ) (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_051
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0155).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_051 :
    (∫ x in (51/512:ℝ)..(13/128:ℝ), x^10*thetaFirstMode x) ≤ (9355903117/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (51/512:ℝ) (13/128:ℝ)
    (908947092893/20000000000000:ℝ) (560177318273/12500000000000:ℝ) (816046171560470573584681/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_051 (thetaFirstMode_refined_node_0151).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_052 :
    (2795235593/250000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(53/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3992560049659117735503699/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (13/128:ℝ) (53/512:ℝ)-(53/512:ℝ)*thetaPowerMass 10 (13/128:ℝ) (53/512:ℝ)) ≤
      thetaFirstModeFirst (53/512:ℝ)*(thetaPowerMass 11 (13/128:ℝ) (53/512:ℝ)-(53/512:ℝ)*thetaPowerMass 10 (13/128:ℝ) (53/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0083.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (13/128:ℝ) (53/512:ℝ)
    (53/512:ℝ) (4418718784289/100000000000000:ℝ) (-3992560049659117735503699/12500000000000000000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_052
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0157).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_052 :
    (∫ x in (13/128:ℝ)..(53/512:ℝ), x^10*thetaFirstMode x) ≤ (5590478307/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/128:ℝ) (53/512:ℝ)
    (560177318273/12500000000000:ℝ) (138085131857/3125000000000:ℝ) (1625804324653926212111369/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_052 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0157).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_053 :
    (3328214871/250000000000000000000000:ℝ) ≤ ∫ x in (53/512:ℝ)..(27/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 10 (53/512:ℝ) (27/256:ℝ)) ≤
      thetaFirstModeFirst (582516327971457/5622000143388160:ℝ)*(thetaPowerMass 11 (53/512:ℝ) (27/256:ℝ)-(582516327971457/5622000143388160:ℝ)*thetaPowerMass 10 (53/512:ℝ) (27/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0084.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (53/512:ℝ) (27/256:ℝ)
    (582516327971457/5622000143388160:ℝ) (4415586481659/100000000000000:ℝ) (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_053
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0161).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_053 :
    (∫ x in (53/512:ℝ)..(27/256:ℝ), x^10*thetaFirstMode x) ≤ (13312877097/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/512:ℝ) (27/256:ℝ)
    (138085131857/3125000000000:ℝ) (4356650085507/100000000000000:ℝ) (323884149573414225604271/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_053 (thetaFirstMode_refined_node_0157).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_054 :
    (3159018853/200000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(55/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-15653950004432657253999/50000000000000000000000:ℝ)*(thetaPowerMass 11 (27/256:ℝ) (55/512:ℝ)-(55/512:ℝ)*thetaPowerMass 10 (27/256:ℝ) (55/512:ℝ)) ≤
      thetaFirstModeFirst (55/512:ℝ)*(thetaPowerMass 11 (27/256:ℝ) (55/512:ℝ)-(55/512:ℝ)*thetaPowerMass 10 (27/256:ℝ) (55/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0086.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (27/256:ℝ) (55/512:ℝ)
    (55/512:ℝ) (2147594192367/50000000000000:ℝ) (-15653950004432657253999/50000000000000000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_054
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0163).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_054 :
    (∫ x in (27/256:ℝ)..(55/512:ℝ), x^10*thetaFirstMode x) ≤ (15795114579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/256:ℝ) (55/512:ℝ)
    (4356650085507/100000000000000:ℝ) (53689921367/1250000000000:ℝ) (806471382291507547903069/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_054 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0163).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_055 :
    (18676090169/1000000000000000000000000:ℝ) ≤ ∫ x in (55/512:ℝ)..(7/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 10 (55/512:ℝ) (7/64:ℝ)) ≤
      thetaFirstModeFirst (162550142281395/1511863535831552:ℝ)*(thetaPowerMass 11 (55/512:ℝ) (7/64:ℝ)-(162550142281395/1511863535831552:ℝ)*thetaPowerMass 10 (55/512:ℝ) (7/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0087.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (55/512:ℝ) (7/64:ℝ)
    (162550142281395/1511863535831552:ℝ) (134132167511/3125000000000:ℝ) (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_055
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0167).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_055 :
    (∫ x in (55/512:ℝ)..(7/64:ℝ), x^10*thetaFirstMode x) ≤ (9338057579/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/512:ℝ) (7/64:ℝ)
    (53689921367/1250000000000:ℝ) (2117176309913/50000000000000:ℝ) (1606371541043329696582451/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_055 (thetaFirstMode_refined_node_0163).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_056 :
    (5502432349/250000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(57/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1917526051108501105680521/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (7/64:ℝ) (57/512:ℝ)-(57/512:ℝ)*thetaPowerMass 10 (7/64:ℝ) (57/512:ℝ)) ≤
      thetaFirstModeFirst (57/512:ℝ)*(thetaPowerMass 11 (7/64:ℝ) (57/512:ℝ)-(57/512:ℝ)*thetaPowerMass 10 (7/64:ℝ) (57/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0089.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (7/64:ℝ) (57/512:ℝ)
    (57/512:ℝ) (4174119095129/100000000000000:ℝ) (-1917526051108501105680521/6250000000000000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_056
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0169).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_056 :
    (∫ x in (7/64:ℝ)..(57/512:ℝ), x^10*thetaFirstMode x) ≤ (2751219747/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/64:ℝ) (57/512:ℝ)
    (2117176309913/50000000000000:ℝ) (4174124310253/100000000000000:ℝ) (1599708257720913572858011/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_056 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0169).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_057 :
    (5171156407/200000000000000000000000:ℝ) ≤ ∫ x in (57/512:ℝ)..(29/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 10 (57/512:ℝ) (29/256:ℝ)) ≤
      thetaFirstModeFirst (1120594199442993/10057446457500160:ℝ)*(thetaPowerMass 11 (57/512:ℝ) (29/256:ℝ)-(1120594199442993/10057446457500160:ℝ)*thetaPowerMass 10 (57/512:ℝ) (29/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0090.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (57/512:ℝ) (29/256:ℝ)
    (1120594199442993/10057446457500160:ℝ) (4171320778711/100000000000000:ℝ) (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_057
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0173).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_057 :
    (∫ x in (57/512:ℝ)..(29/256:ℝ), x^10*thetaFirstMode x) ≤ (12927908513/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (57/512:ℝ) (29/256:ℝ)
    (4174124310253/100000000000000:ℝ) (411450623883/10000000000000:ℝ) (24889907953508527837773/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_057 (thetaFirstMode_refined_node_0169).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_058 :
    (6056081693/200000000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(59/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-751454366461280770506813/2500000000000000000000000:ℝ)*(thetaPowerMass 11 (29/256:ℝ) (59/512:ℝ)-(59/512:ℝ)*thetaPowerMass 10 (29/256:ℝ) (59/512:ℝ)) ≤
      thetaFirstModeFirst (59/512:ℝ)*(thetaPowerMass 11 (29/256:ℝ) (59/512:ℝ)-(59/512:ℝ)*thetaPowerMass 10 (29/256:ℝ) (59/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0092.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (29/256:ℝ) (59/512:ℝ)
    (59/512:ℝ) (405549072243/10000000000000:ℝ) (-751454366461280770506813/2500000000000000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_058
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0175).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_058 :
    (∫ x in (29/256:ℝ)..(59/512:ℝ), x^10*thetaFirstMode x) ≤ (3785056021/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/256:ℝ) (59/512:ℝ)
    (411450623883/10000000000000:ℝ) (4055495829081/100000000000000:ℝ) (793055151525239044885573/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_058 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0175).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_059 :
    (7071330649/200000000000000000000000:ℝ) ≤ ∫ x in (59/512:ℝ)..(15/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 10 (59/512:ℝ) (15/128:ℝ)) ≤
      thetaFirstModeFirst (1528044900298191/13250186301775360:ℝ)*(thetaPowerMass 11 (59/512:ℝ) (15/128:ℝ)-(1528044900298191/13250186301775360:ℝ)*thetaPowerMass 10 (59/512:ℝ) (15/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0093.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (59/512:ℝ) (15/128:ℝ)
    (1528044900298191/13250186301775360:ℝ) (506605225251/12500000000000:ℝ) (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_059
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0179).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_059 :
    (∫ x in (59/512:ℝ)..(15/128:ℝ), x^10*thetaFirstMode x) ≤ (8839175411/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (59/512:ℝ) (15/128:ℝ)
    (4055495829081/100000000000000:ℝ) (499636308793/12500000000000:ℝ) (394794515332816383702243/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_059 (thetaFirstMode_refined_node_0175).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_060 :
    (10291251457/250000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(61/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1472065680580774860715491/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (15/128:ℝ) (61/512:ℝ)-(61/512:ℝ)*thetaPowerMass 10 (15/128:ℝ) (61/512:ℝ)) ≤
      thetaFirstModeFirst (61/512:ℝ)*(thetaPowerMass 11 (15/128:ℝ) (61/512:ℝ)-(61/512:ℝ)*thetaPowerMass 10 (15/128:ℝ) (61/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0095.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (15/128:ℝ) (61/512:ℝ)
    (61/512:ℝ) (3939282518997/100000000000000:ℝ) (-1472065680580774860715491/5000000000000000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_060
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0181).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_060 :
    (∫ x in (15/128:ℝ)..(61/512:ℝ), x^10*thetaFirstMode x) ≤ (41165060329/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/128:ℝ) (61/512:ℝ)
    (499636308793/12500000000000:ℝ) (3939287518223/100000000000000:ℝ) (1572158618563914001664089/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_060 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0181).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_061 :
    (5974242207/125000000000000000000000:ℝ) ≤ ∫ x in (61/512:ℝ)..(31/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 10 (61/512:ℝ) (31/256:ℝ)) ≤
      thetaFirstModeFirst (2062244582827209/17296952731317760:ℝ)*(thetaPowerMass 11 (61/512:ℝ) (31/256:ℝ)-(2062244582827209/17296952731317760:ℝ)*thetaPowerMass 10 (61/512:ℝ) (31/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0096.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (61/512:ℝ) (31/256:ℝ)
    (2062244582827209/17296952731317760:ℝ) (3936772777441/100000000000000:ℝ) (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_061
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0185).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_061 :
    (∫ x in (61/512:ℝ)..(31/256:ℝ), x^10*thetaFirstMode x) ≤ (47794003837/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (61/512:ℝ) (31/256:ℝ)
    (3939287518223/100000000000000:ℝ) (3882084295049/100000000000000:ℝ) (782526611166251537386807/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_061 (thetaFirstMode_refined_node_0181).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_062 :
    (55340524579/1000000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(63/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-360374624006484139939341/1250000000000000000000000:ℝ)*(thetaPowerMass 11 (31/256:ℝ) (63/512:ℝ)-(63/512:ℝ)*thetaPowerMass 10 (31/256:ℝ) (63/512:ℝ)) ≤
      thetaFirstModeFirst (63/512:ℝ)*(thetaPowerMass 11 (31/256:ℝ) (63/512:ℝ)-(63/512:ℝ)*thetaPowerMass 10 (31/256:ℝ) (63/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0098.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (31/256:ℝ) (63/512:ℝ)
    (63/512:ℝ) (382547319749/10000000000000:ℝ) (-360374624006484139939341/1250000000000000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_062
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0187).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_062 :
    (∫ x in (31/256:ℝ)..(63/512:ℝ), x^10*thetaFirstMode x) ≤ (55340598567/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/256:ℝ) (63/512:ℝ)
    (3882084295049/100000000000000:ℝ) (3825478090361/100000000000000:ℝ) (778931566418436122015273/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_062 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0187).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_063 :
    (31955512061/500000000000000000000000:ℝ) ≤ ∫ x in (63/512:ℝ)..(1/8:ℝ), x^10*thetaFirstMode x := by
  have hd : (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 10 (63/512:ℝ) (1/8:ℝ)) ≤
      thetaFirstModeFirst (2756444578756407/22386559816092160:ℝ)*(thetaPowerMass 11 (63/512:ℝ) (1/8:ℝ)-(2756444578756407/22386559816092160:ℝ)*thetaPowerMass 10 (63/512:ℝ) (1/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0099.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (63/512:ℝ) (1/8:ℝ)
    (2756444578756407/22386559816092160:ℝ) (1911546687323/50000000000000:ℝ) (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_063
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0191).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_063 :
    (∫ x in (63/512:ℝ)..(1/8:ℝ), x^10*thetaFirstMode x) ≤ (15977778413/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (63/512:ℝ) (1/8:ℝ)
    (3825478090361/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (1550589622624381755686269/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_063 (thetaFirstMode_refined_node_0187).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
