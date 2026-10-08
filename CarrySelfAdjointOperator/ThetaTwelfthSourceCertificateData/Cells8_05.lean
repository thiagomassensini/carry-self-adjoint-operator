import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature05
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative07
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative08
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative09

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_8_160 :
    (297470338612923/250000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(161/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-18229161379622855787957/250000000000000000000000:ℝ)*(thetaPowerMass 9 (5/16:ℝ) (161/512:ℝ)-(161/512:ℝ)*thetaPowerMass 8 (5/16:ℝ) (161/512:ℝ)) ≤
      thetaFirstModeFirst (161/512:ℝ)*(thetaPowerMass 9 (5/16:ℝ) (161/512:ℝ)-(161/512:ℝ)*thetaPowerMass 8 (5/16:ℝ) (161/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0245.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (5/16:ℝ) (161/512:ℝ)
    (161/512:ℝ) (32308386653/5000000000000:ℝ) (-18229161379622855787957/250000000000000000000000:ℝ) (134106239829891427230371/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_160
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0481).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_160 :
    (∫ x in (5/16:ℝ)..(161/512:ℝ), x^8*thetaFirstMode x) ≤ (594942042085449/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/16:ℝ) (161/512:ℝ)
    (660538949293/100000000000000:ℝ) (646168944989/100000000000000:ℝ) (134106239829891427230371/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_160 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0481).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_161 :
    (1223238676255571/1000000000000000000000000:ℝ) ≤ ∫ x in (161/512:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-182237803669525893533975887351/2500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (161/512:ℝ) (81/256:ℝ)-(12782224971512359209/40644882680317749760:ℝ)*thetaPowerMass 8 (161/512:ℝ) (81/256:ℝ)) ≤
      thetaFirstModeFirst (12782224971512359209/40644882680317749760:ℝ)*(thetaPowerMass 9 (161/512:ℝ) (81/256:ℝ)-(12782224971512359209/40644882680317749760:ℝ)*thetaPowerMass 8 (161/512:ℝ) (81/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0246.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (161/512:ℝ) (81/256:ℝ)
    (12782224971512359209/40644882680317749760:ℝ) (322965965079/50000000000000:ℝ) (-182237803669525893533975887351/2500000000000000000000000000000:ℝ) (661894603755790120841153/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_161
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0485).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_161 :
    (∫ x in (161/512:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x) ≤ (1223242007773007/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (161/512:ℝ) (81/256:ℝ)
    (646168944989/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (661894603755790120841153/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_161 (thetaFirstMode_refined_node_0481).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_162 :
    (628516651895447/500000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(163/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-439569296878588781680347/6250000000000000000000000:ℝ)*(thetaPowerMass 9 (81/256:ℝ) (163/512:ℝ)-(163/512:ℝ)*thetaPowerMass 8 (81/256:ℝ) (163/512:ℝ)) ≤
      thetaFirstModeFirst (163/512:ℝ)*(thetaPowerMass 9 (81/256:ℝ) (163/512:ℝ)-(163/512:ℝ)*thetaPowerMass 8 (81/256:ℝ) (163/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0248.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (81/256:ℝ) (163/512:ℝ)
    (163/512:ℝ) (309095920617/50000000000000:ℝ) (-439569296878588781680347/6250000000000000000000000:ℝ) (653305882545361917059969/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_162
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0487).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_162 :
    (∫ x in (81/256:ℝ)..(163/512:ℝ), x^8*thetaFirstMode x) ≤ (1257036223827327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (81/256:ℝ) (163/512:ℝ)
    (632054730013/100000000000000:ℝ) (309096504893/50000000000000:ℝ) (653305882545361917059969/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_162 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0487).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_163 :
    (322813108320041/250000000000000000000000:ℝ) ≤ ∫ x in (163/512:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-140620749959506428356366670507/2000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (163/512:ℝ) (41/128:ℝ)-(14284239070852168407/44863782688534812160:ℝ)*thetaPowerMass 8 (163/512:ℝ) (41/128:ℝ)) ≤
      thetaFirstModeFirst (14284239070852168407/44863782688534812160:ℝ)*(thetaPowerMass 9 (163/512:ℝ) (41/128:ℝ)-(14284239070852168407/44863782688534812160:ℝ)*thetaPowerMass 8 (163/512:ℝ) (41/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0249.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (163/512:ℝ) (41/128:ℝ)
    (14284239070852168407/44863782688534812160:ℝ) (617967189223/100000000000000:ℝ) (-140620749959506428356366670507/2000000000000000000000000000000:ℝ) (644765869408293189826321/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_163
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0491).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_163 :
    (∫ x in (163/512:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x) ≤ (322814001456657/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (163/512:ℝ) (41/128:ℝ)
    (309096504893/50000000000000:ℝ) (151145126999/25000000000000:ℝ) (644765869408293189826321/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_163 (thetaFirstMode_refined_node_0487).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_164 :
    (1325886964695091/1000000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(165/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3390621877837672519889761/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (41/128:ℝ) (165/512:ℝ)-(165/512:ℝ)*thetaPowerMass 8 (41/128:ℝ) (165/512:ℝ)) ≤
      thetaFirstModeFirst (165/512:ℝ)*(thetaPowerMass 9 (41/128:ℝ) (165/512:ℝ)-(165/512:ℝ)*thetaPowerMass 8 (41/128:ℝ) (165/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0251.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (41/128:ℝ) (165/512:ℝ)
    (165/512:ℝ) (591212840587/100000000000000:ℝ) (-3390621877837672519889761/50000000000000000000000000:ℝ) (19883605626830067726437/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_164
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0493).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_164 :
    (∫ x in (41/128:ℝ)..(165/512:ℝ), x^8*thetaFirstMode x) ≤ (1325890083618063/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (41/128:ℝ) (165/512:ℝ)
    (151145126999/25000000000000:ℝ) (591213966907/100000000000000:ℝ) (19883605626830067726437/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_164 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0493).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_165 :
    (1360922822162929/1000000000000000000000000:ℝ) ≤ ∫ x in (165/512:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-677925107220350352590775899137/10000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (165/512:ℝ) (83/256:ℝ)-(3188228496497630685/9892200887210173952:ℝ)*thetaPowerMass 8 (165/512:ℝ) (83/256:ℝ)) ≤
      thetaFirstModeFirst (3188228496497630685/9892200887210173952:ℝ)*(thetaPowerMass 9 (165/512:ℝ) (83/256:ℝ)-(3188228496497630685/9892200887210173952:ℝ)*thetaPowerMass 8 (165/512:ℝ) (83/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0252.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (165/512:ℝ) (83/256:ℝ)
    (3188228496497630685/9892200887210173952:ℝ) (29549942907/5000000000000:ℝ) (-677925107220350352590775899137/10000000000000000000000000000000:ℝ) (313917605961490248176989/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_165
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0497).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_165 :
    (∫ x in (165/512:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x) ≤ (680463323774991/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (165/512:ℝ) (83/256:ℝ)
    (591213966907/100000000000000:ℝ) (578090147677/100000000000000:ℝ) (313917605961490248176989/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_165 (thetaFirstMode_refined_node_0493).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_166 :
    (1396350026908411/1000000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(167/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1633998049918065643921641/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (83/256:ℝ) (167/512:ℝ)-(167/512:ℝ)*thetaPowerMass 8 (83/256:ℝ) (167/512:ℝ)) ≤
      thetaFirstModeFirst (167/512:ℝ)*(thetaPowerMass 9 (83/256:ℝ) (167/512:ℝ)-(167/512:ℝ)*thetaPowerMass 8 (83/256:ℝ) (167/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0254.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (83/256:ℝ) (167/512:ℝ)
    (167/512:ℝ) (565204745437/100000000000000:ℝ) (-1633998049918065643921641/25000000000000000000000000:ℝ) (61944614403501519343567/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_166
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0499).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_166 :
    (∫ x in (83/256:ℝ)..(167/512:ℝ), x^8*thetaFirstMode x) ≤ (1396353353342683/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (83/256:ℝ) (167/512:ℝ)
    (578090147677/100000000000000:ℝ) (282602915327/50000000000000:ℝ) (61944614403501519343567/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_166 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0499).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_167 :
    (71607661873897/50000000000000000000000:ℝ) ≤ ∫ x in (167/512:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3267037786701633939058727331097/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (167/512:ℝ) (21/64:ℝ)-(17766735204530144943/54465262754276508160:ℝ)*thetaPowerMass 8 (167/512:ℝ) (21/64:ℝ)) ≤
      thetaFirstModeFirst (17766735204530144943/54465262754276508160:ℝ)*(thetaPowerMass 9 (167/512:ℝ) (21/64:ℝ)-(17766735204530144943/54465262754276508160:ℝ)*thetaPowerMass 8 (167/512:ℝ) (21/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0255.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (167/512:ℝ) (21/64:ℝ)
    (17766735204530144943/54465262754276508160:ℝ) (565000970919/100000000000000:ℝ) (-3267037786701633939058727331097/50000000000000000000000000000000:ℝ) (611108936940896103336437/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_167
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0503).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_167 :
    (∫ x in (167/512:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x) ≤ (358039331922147/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (167/512:ℝ) (21/64:ℝ)
    (282602915327/50000000000000:ℝ) (110511563137/20000000000000:ℝ) (611108936940896103336437/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_167 (thetaFirstMode_refined_node_0499).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_168 :
    (1468321631970519/1000000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(169/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3148637124928762968861963/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (21/64:ℝ) (169/512:ℝ)-(169/512:ℝ)*thetaPowerMass 8 (21/64:ℝ) (169/512:ℝ)) ≤
      thetaFirstModeFirst (169/512:ℝ)*(thetaPowerMass 9 (21/64:ℝ) (169/512:ℝ)-(169/512:ℝ)*thetaPowerMass 8 (21/64:ℝ) (169/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0257.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (21/64:ℝ) (169/512:ℝ)
    (169/512:ℝ) (540141877167/100000000000000:ℝ) (-3148637124928762968861963/50000000000000000000000000:ℝ) (301412166304549438383623/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_168
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0505).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_168 :
    (∫ x in (21/64:ℝ)..(169/512:ℝ), x^8*thetaFirstMode x) ≤ (146832517457223/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (21/64:ℝ) (169/512:ℝ)
    (110511563137/20000000000000:ℝ) (135035730599/25000000000000:ℝ) (301412166304549438383623/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_168 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0505).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_169 :
    (752419307573969/500000000000000000000000:ℝ) ≤ ∫ x in (169/512:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-786928904987340141143637617033/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (169/512:ℝ) (85/256:ℝ)-(19775858017267564641/59907066245820060160:ℝ)*thetaPowerMass 8 (169/512:ℝ) (85/256:ℝ)) ≤
      thetaFirstModeFirst (19775858017267564641/59907066245820060160:ℝ)*(thetaPowerMass 9 (169/512:ℝ) (85/256:ℝ)-(19775858017267564641/59907066245820060160:ℝ)*thetaPowerMass 8 (169/512:ℝ) (85/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0258.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (169/512:ℝ) (85/256:ℝ)
    (19775858017267564641/59907066245820060160:ℝ) (53994786779/10000000000000:ℝ) (-786928904987340141143637617033/12500000000000000000000000000000:ℝ) (594593054343830348494757/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_169
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0509).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_169 :
    (∫ x in (169/512:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x) ≤ (188105372787721/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (169/512:ℝ) (85/256:ℝ)
    (135035730599/25000000000000:ℝ) (527957990481/100000000000000:ℝ) (594593054343830348494757/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_169 (thetaFirstMode_refined_node_0505).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_170 :
    (192711570478683/125000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(171/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1516251931634819162967007/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (85/256:ℝ) (171/512:ℝ)-(171/512:ℝ)*thetaPowerMass 8 (85/256:ℝ) (171/512:ℝ)) ≤
      thetaFirstModeFirst (171/512:ℝ)*(thetaPowerMass 9 (85/256:ℝ) (171/512:ℝ)-(171/512:ℝ)*thetaPowerMass 8 (85/256:ℝ) (171/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0260.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (85/256:ℝ) (171/512:ℝ)
    (171/512:ℝ) (515998873633/100000000000000:ℝ) (-1516251931634819162967007/25000000000000000000000000:ℝ) (586415806713032535282343/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_170
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0511).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_170 :
    (∫ x in (85/256:ℝ)..(171/512:ℝ), x^8*thetaFirstMode x) ≤ (770848165632021/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (85/256:ℝ) (171/512:ℝ)
    (527957990481/100000000000000:ℝ) (20639995199/4000000000000:ℝ) (586415806713032535282343/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_170 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0511).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_171 :
    (98679102876461/62500000000000000000000:ℝ) ≤ ∫ x in (171/512:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-121264719200422566392135829323/2000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (171/512:ℝ) (43/128:ℝ)-(21984457092577248159/65818805832858856960:ℝ)*thetaPowerMass 8 (171/512:ℝ) (43/128:ℝ)) ≤
      thetaFirstModeFirst (21984457092577248159/65818805832858856960:ℝ)*(thetaPowerMass 9 (171/512:ℝ) (43/128:ℝ)-(21984457092577248159/65818805832858856960:ℝ)*thetaPowerMass 8 (171/512:ℝ) (43/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0261.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (171/512:ℝ) (43/128:ℝ)
    (21984457092577248159/65818805832858856960:ℝ) (515814204633/100000000000000:ℝ) (-121264719200422566392135829323/2000000000000000000000000000000:ℝ) (9035832429292167225019/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_171
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0515).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_171 :
    (∫ x in (171/512:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x) ≤ (394717575595049/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (171/512:ℝ) (43/128:ℝ)
    (20639995199/4000000000000:ℝ) (252132735761/50000000000000:ℝ) (9035832429292167225019/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_171 (thetaFirstMode_refined_node_0511).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_172 :
    (808172742677687/500000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(173/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-14597770547645466418983/250000000000000000000000:ℝ)*(thetaPowerMass 9 (43/128:ℝ) (173/512:ℝ)-(173/512:ℝ)*thetaPowerMass 8 (43/128:ℝ) (173/512:ℝ)) ≤
      thetaFirstModeFirst (173/512:ℝ)*(thetaPowerMass 9 (43/128:ℝ) (173/512:ℝ)-(173/512:ℝ)*thetaPowerMass 8 (43/128:ℝ) (173/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0263.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (43/128:ℝ) (173/512:ℝ)
    (173/512:ℝ) (4927506981/1000000000000:ℝ) (-14597770547645466418983/250000000000000000000000:ℝ) (570226127518297911390171/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_172
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0517).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_172 :
    (∫ x in (43/128:ℝ)..(173/512:ℝ), x^8*thetaFirstMode x) ≤ (64653979450807/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (43/128:ℝ) (173/512:ℝ)
    (252132735761/50000000000000:ℝ) (246375833319/50000000000000:ℝ) (570226127518297911390171/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_172 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0517).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_173 :
    (1654113035229787/1000000000000000000000000:ℝ) ≤ ∫ x in (173/512:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-583740538898351447989147005929/10000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (173/512:ℝ) (87/256:ℝ)-(24409651773064480857/72234846544296732160:ℝ)*thetaPowerMass 8 (173/512:ℝ) (87/256:ℝ)) ≤
      thetaFirstModeFirst (24409651773064480857/72234846544296732160:ℝ)*(thetaPowerMass 9 (173/512:ℝ) (87/256:ℝ)-(24409651773064480857/72234846544296732160:ℝ)*thetaPowerMass 8 (173/512:ℝ) (87/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0264.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (173/512:ℝ) (87/256:ℝ)
    (24409651773064480857/72234846544296732160:ℝ) (492574961981/100000000000000:ℝ) (-583740538898351447989147005929/10000000000000000000000000000000:ℝ) (562215010807529520582331/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_173
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0521).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_173 :
    (∫ x in (173/512:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x) ≤ (1654117993120933/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (173/512:ℝ) (87/256:ℝ)
    (246375833319/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (562215010807529520582331/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_173 (thetaFirstMode_refined_node_0517).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_174 :
    (1692155220222041/1000000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(175/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-14048723008194226754841/250000000000000000000000:ℝ)*(thetaPowerMass 9 (87/256:ℝ) (175/512:ℝ)-(175/512:ℝ)*thetaPowerMass 8 (87/256:ℝ) (175/512:ℝ)) ≤
      thetaFirstModeFirst (175/512:ℝ)*(thetaPowerMass 9 (87/256:ℝ) (175/512:ℝ)-(175/512:ℝ)*thetaPowerMass 8 (87/256:ℝ) (175/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0266.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (87/256:ℝ) (175/512:ℝ)
    (175/512:ℝ) (18814905909/4000000000000:ℝ) (-14048723008194226754841/250000000000000000000000:ℝ) (277130277167533315632323/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_174
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0523).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_174 :
    (∫ x in (87/256:ℝ)..(175/512:ℝ), x^8*thetaFirstMode x) ≤ (1692159463225569/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (87/256:ℝ) (175/512:ℝ)
    (481455387969/100000000000000:ℝ) (470373579529/100000000000000:ℝ) (277130277167533315632323/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_174 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0523).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_175 :
    (1730451806397363/1000000000000000000000000:ℝ) ≤ ∫ x in (175/512:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2808926533174888998017826497601/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (175/512:ℝ) (11/32:ℝ)-(5413961127233958075/15838324523948298752:ℝ)*thetaPowerMass 8 (175/512:ℝ) (11/32:ℝ)) ≤
      thetaFirstModeFirst (5413961127233958075/15838324523948298752:ℝ)*(thetaPowerMass 9 (175/512:ℝ) (11/32:ℝ)-(5413961127233958075/15838324523948298752:ℝ)*thetaPowerMass 8 (175/512:ℝ) (11/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0267.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (175/512:ℝ) (11/32:ℝ)
    (5413961127233958075/15838324523948298752:ℝ) (117551363383/25000000000000:ℝ) (-2808926533174888998017826497601/50000000000000000000000000000000:ℝ) (109272673616227367408399/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_175
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0527).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_175 :
    (∫ x in (175/512:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x) ≤ (1730457078214103/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (175/512:ℝ) (11/32:ℝ)
    (470373579529/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (109272673616227367408399/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_175 (thetaFirstMode_refined_node_0523).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_176 :
    (221123634915523/125000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(177/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2703031079969079547113327/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (11/32:ℝ) (177/512:ℝ)-(177/512:ℝ)*thetaPowerMass 8 (11/32:ℝ) (177/512:ℝ)) ≤
      thetaFirstModeFirst (177/512:ℝ)*(thetaPowerMass 9 (11/32:ℝ) (177/512:ℝ)-(177/512:ℝ)*thetaPowerMass 8 (11/32:ℝ) (177/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0269.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (11/32:ℝ) (177/512:ℝ)
    (177/512:ℝ) (448840361591/100000000000000:ℝ) (-2703031079969079547113327/50000000000000000000000000:ℝ) (538524042979173877513599/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_176
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0529).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_176 :
    (∫ x in (11/32:ℝ)..(177/512:ℝ), x^8*thetaFirstMode x) ≤ (1768993572947571/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/32:ℝ) (177/512:ℝ)
    (57437900869/12500000000000:ℝ) (448841257713/100000000000000:ℝ) (538524042979173877513599/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_176 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0529).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_177 :
    (451936412472397/250000000000000000000000:ℝ) ≤ ∫ x in (177/512:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-67556131681634168817799078999/1250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (177/512:ℝ) (89/256:ℝ)-(29984600961233742393/86727736009265052160:ℝ)*thetaPowerMass 8 (177/512:ℝ) (89/256:ℝ)) ≤
      thetaFirstModeFirst (29984600961233742393/86727736009265052160:ℝ)*(thetaPowerMass 9 (177/512:ℝ) (89/256:ℝ)-(29984600961233742393/86727736009265052160:ℝ)*thetaPowerMass 8 (177/512:ℝ) (89/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0270.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (177/512:ℝ) (89/256:ℝ)
    (29984600961233742393/86727736009265052160:ℝ) (89736266843/20000000000000:ℝ) (-67556131681634168817799078999/1250000000000000000000000000000:ℝ) (530743150886797466724179/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_177
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0533).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_177 :
    (∫ x in (177/512:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x) ≤ (451937812015389/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (177/512:ℝ) (89/256:ℝ)
    (448841257713/100000000000000:ℝ) (219192370681/50000000000000:ℝ) (530743150886797466724179/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_177 (thetaFirstMode_refined_node_0529).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_178 :
    (1846707230471311/1000000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(179/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-129968417333378080755309/2500000000000000000000000:ℝ)*(thetaPowerMass 9 (89/256:ℝ) (179/512:ℝ)-(179/512:ℝ)*thetaPowerMass 8 (89/256:ℝ) (179/512:ℝ)) ≤
      thetaFirstModeFirst (179/512:ℝ)*(thetaPowerMass 9 (89/256:ℝ) (179/512:ℝ)-(179/512:ℝ)*thetaPowerMass 8 (89/256:ℝ) (179/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0272.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (89/256:ℝ) (179/512:ℝ)
    (179/512:ℝ) (214064914129/50000000000000:ℝ) (-129968417333378080755309/2500000000000000000000000:ℝ) (523021244573003219654143/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_178
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0535).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_178 :
    (∫ x in (89/256:ℝ)..(179/512:ℝ), x^8*thetaFirstMode x) ≤ (1846711983162257/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (89/256:ℝ) (179/512:ℝ)
    (219192370681/50000000000000:ℝ) (53516336217/12500000000000:ℝ) (523021244573003219654143/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_178 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0535).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_179 :
    (1885851313699427/1000000000000000000000000:ℝ) ≤ ∫ x in (179/512:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2598613728867339888637141347023/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (179/512:ℝ) (45/128:ℝ)-(33175116720304347591/94884058348837864960:ℝ)*thetaPowerMass 8 (179/512:ℝ) (45/128:ℝ)) ≤
      thetaFirstModeFirst (33175116720304347591/94884058348837864960:ℝ)*(thetaPowerMass 9 (179/512:ℝ) (45/128:ℝ)-(33175116720304347591/94884058348837864960:ℝ)*thetaPowerMass 8 (179/512:ℝ) (45/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0273.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (179/512:ℝ) (45/128:ℝ)
    (33175116720304347591/94884058348837864960:ℝ) (42797860779/10000000000000:ℝ) (-2598613728867339888637141347023/50000000000000000000000000000000:ℝ) (257679428850872338749071/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_179
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0539).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_179 :
    (∫ x in (179/512:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x) ≤ (942928625322823/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (179/512:ℝ) (45/128:ℝ)
    (53516336217/12500000000000:ℝ) (16723046287/4000000000000:ℝ) (257679428850872338749071/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_179 (thetaFirstMode_refined_node_0535).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_180 :
    (96258155503231/50000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(181/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1249355162649246374283419/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (45/128:ℝ) (181/512:ℝ)-(181/512:ℝ)*thetaPowerMass 8 (45/128:ℝ) (181/512:ℝ)) ≤
      thetaFirstModeFirst (181/512:ℝ)*(thetaPowerMass 9 (45/128:ℝ) (181/512:ℝ)-(181/512:ℝ)*thetaPowerMass 8 (45/128:ℝ) (181/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0275.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (45/128:ℝ) (181/512:ℝ)
    (181/512:ℝ) (408217392869/100000000000000:ℝ) (-1249355162649246374283419/25000000000000000000000000:ℝ) (507756504821714887282653/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_180
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0541).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_180 :
    (∫ x in (45/128:ℝ)..(181/512:ℝ), x^8*thetaFirstMode x) ≤ (1925168130135951/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (45/128:ℝ) (181/512:ℝ)
    (16723046287/4000000000000:ℝ) (204109110361/50000000000000:ℝ) (507756504821714887282653/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_180 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0541).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_181 :
    (1964619035411213/1000000000000000000000000:ℝ) ≤ ∫ x in (181/512:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-499597174110084443344472835261/10000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (181/512:ℝ) (91/256:ℝ)-(36663910216296708609/103703836492258332160:ℝ)*thetaPowerMass 8 (181/512:ℝ) (91/256:ℝ)) ≤
      thetaFirstModeFirst (36663910216296708609/103703836492258332160:ℝ)*(thetaPowerMass 9 (181/512:ℝ) (91/256:ℝ)-(36663910216296708609/103703836492258332160:ℝ)*thetaPowerMass 8 (181/512:ℝ) (91/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0276.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (181/512:ℝ) (91/256:ℝ)
    (36663910216296708609/103703836492258332160:ℝ) (408073633973/100000000000000:ℝ) (-499597174110084443344472835261/10000000000000000000000000000000:ℝ) (250107340691448839721707/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_181
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0545).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_181 :
    (∫ x in (181/512:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x) ≤ (1964625323515303/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (181/512:ℝ) (91/256:ℝ)
    (204109110361/50000000000000:ℝ) (398553980321/100000000000000:ℝ) (250107340691448839721707/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_181 (thetaFirstMode_refined_node_0541).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_182 :
    (20042038749289/10000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(183/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-96040404819887627161647/2000000000000000000000000:ℝ)*(thetaPowerMass 9 (91/256:ℝ) (183/512:ℝ)-(183/512:ℝ)*thetaPowerMass 8 (91/256:ℝ) (183/512:ℝ)) ≤
      thetaFirstModeFirst (183/512:ℝ)*(thetaPowerMass 9 (91/256:ℝ) (183/512:ℝ)-(183/512:ℝ)*thetaPowerMass 8 (91/256:ℝ) (183/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0278.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (91/256:ℝ) (183/512:ℝ)
    (183/512:ℝ) (15563190551/4000000000000:ℝ) (-96040404819887627161647/2000000000000000000000000:ℝ) (492733863727986470362623/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_182
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0547).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_182 :
    (∫ x in (91/256:ℝ)..(183/512:ℝ), x^8*thetaFirstMode x) ≤ (100210458527009/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (91/256:ℝ) (183/512:ℝ)
    (398553980321/100000000000000:ℝ) (77816111801/20000000000000:ℝ) (492733863727986470362623/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_182 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0547).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_183 :
    (2043893013465071/1000000000000000000000000:ℝ) ≤ ∫ x in (183/512:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-192025186013557212285758283/4000000000000000000000000000:ℝ)*(thetaPowerMass 9 (183/512:ℝ) (23/64:ℝ)-(40475102494972215807/113232801681326748160:ℝ)*thetaPowerMass 8 (183/512:ℝ) (23/64:ℝ)) ≤
      thetaFirstModeFirst (40475102494972215807/113232801681326748160:ℝ)*(thetaPowerMass 9 (183/512:ℝ) (23/64:ℝ)-(40475102494972215807/113232801681326748160:ℝ)*thetaPowerMass 8 (183/512:ℝ) (23/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0279.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (183/512:ℝ) (23/64:ℝ)
    (40475102494972215807/113232801681326748160:ℝ) (388943135103/100000000000000:ℝ) (-192025186013557212285758283/4000000000000000000000000000:ℝ) (485314509120892510886041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_183
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0551).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_183 :
    (∫ x in (183/512:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x) ≤ (255487458128287/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (183/512:ℝ) (23/64:ℝ)
    (77816111801/20000000000000:ℝ) (379795103081/100000000000000:ℝ) (485314509120892510886041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_183 (thetaFirstMode_refined_node_0547).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_184 :
    (2083670892418217/1000000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(185/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-9224880310693381389793/200000000000000000000000:ℝ)*(thetaPowerMass 9 (23/64:ℝ) (185/512:ℝ)-(185/512:ℝ)*thetaPowerMass 8 (23/64:ℝ) (185/512:ℝ)) ≤
      thetaFirstModeFirst (185/512:ℝ)*(thetaPowerMass 9 (23/64:ℝ) (185/512:ℝ)-(185/512:ℝ)*thetaPowerMass 8 (23/64:ℝ) (185/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0281.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (23/64:ℝ) (185/512:ℝ)
    (185/512:ℝ) (370694018701/100000000000000:ℝ) (-9224880310693381389793/200000000000000000000000:ℝ) (119489263940876827368961/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_184
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0553).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_184 :
    (∫ x in (23/64:ℝ)..(185/512:ℝ), x^8*thetaFirstMode x) ≤ (260459558944891/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (23/64:ℝ) (185/512:ℝ)
    (379795103081/100000000000000:ℝ) (46336847787/12500000000000:ℝ) (119489263940876827368961/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_184 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0553).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_185 :
    (2123511915551919/1000000000000000000000000:ℝ) ≤ ∫ x in (185/512:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2305552965535923343311592752203/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (185/512:ℝ) (93/256:ℝ)-(8926893532018987965/24703856487388477952:ℝ)*thetaPowerMass 8 (185/512:ℝ) (93/256:ℝ)) ≤
      thetaFirstModeFirst (8926893532018987965/24703856487388477952:ℝ)*(thetaPowerMass 9 (185/512:ℝ) (93/256:ℝ)-(8926893532018987965/24703856487388477952:ℝ)*thetaPowerMass 8 (185/512:ℝ) (93/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0282.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (185/512:ℝ) (93/256:ℝ)
    (8926893532018987965/24703856487388477952:ℝ) (370564202331/100000000000000:ℝ) (-2305552965535923343311592752203/50000000000000000000000000000000:ℝ) (235330961414012658325869/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_185
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0557).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_185 :
    (∫ x in (185/512:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x) ≤ (2123518942748633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (185/512:ℝ) (93/256:ℝ)
    (46336847787/12500000000000:ℝ) (72355358003/20000000000000:ℝ) (235330961414012658325869/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_185 (thetaFirstMode_refined_node_0553).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_186 :
    (2163400266570361/1000000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(187/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-138393240166008847981967/3125000000000000000000000:ℝ)*(thetaPowerMass 9 (93/256:ℝ) (187/512:ℝ)-(187/512:ℝ)*thetaPowerMass 8 (93/256:ℝ) (187/512:ℝ)) ≤
      thetaFirstModeFirst (187/512:ℝ)*(thetaPowerMass 9 (93/256:ℝ) (187/512:ℝ)-(187/512:ℝ)*thetaPowerMass 8 (93/256:ℝ) (187/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0284.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (93/256:ℝ) (187/512:ℝ)
    (187/512:ℝ) (22064850653/6250000000000:ℝ) (-138393240166008847981967/3125000000000000000000000:ℝ) (463429510493183864685853/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_186
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0559).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_186 :
    (∫ x in (93/256:ℝ)..(187/512:ℝ), x^8*thetaFirstMode x) ≤ (540851534249347/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (93/256:ℝ) (187/512:ℝ)
    (72355358003/20000000000000:ℝ) (2824306747/800000000000:ℝ) (463429510493183864685853/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_186 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0559).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_187 :
    (2203309421849929/1000000000000000000000000:ℝ) ≤ ∫ x in (187/512:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-276706495516334150202936321061/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (187/512:ℝ) (47/128:ℝ)-(49169526224045867343/134614321254731292160:ℝ)*thetaPowerMass 8 (187/512:ℝ) (47/128:ℝ)) ≤
      thetaFirstModeFirst (49169526224045867343/134614321254731292160:ℝ)*(thetaPowerMass 9 (187/512:ℝ) (47/128:ℝ)-(49169526224045867343/134614321254731292160:ℝ)*thetaPowerMass 8 (187/512:ℝ) (47/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0285.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (187/512:ℝ) (47/128:ℝ)
    (49169526224045867343/134614321254731292160:ℝ) (11028571917/3125000000000:ℝ) (-276706495516334150202936321061/6250000000000000000000000000000:ℝ) (228130099991295207900149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_187
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0563).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_187 :
    (∫ x in (187/512:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x) ≤ (550829209180049/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (187/512:ℝ) (47/128:ℝ)
    (2824306747/800000000000:ℝ) (344476683437/100000000000000:ℝ) (228130099991295207900149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_187 (thetaFirstMode_refined_node_0559).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_188 :
    (1121611698890037/500000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(189/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-132823526318992987405857/3125000000000000000000000:ℝ)*(thetaPowerMass 9 (47/128:ℝ) (189/512:ℝ)-(189/512:ℝ)*thetaPowerMass 8 (47/128:ℝ) (189/512:ℝ)) ≤
      thetaFirstModeFirst (189/512:ℝ)*(thetaPowerMass 9 (47/128:ℝ) (189/512:ℝ)-(189/512:ℝ)*thetaPowerMass 8 (47/128:ℝ) (189/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0287.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (47/128:ℝ) (189/512:ℝ)
    (189/512:ℝ) (336088372119/100000000000000:ℝ) (-132823526318992987405857/3125000000000000000000000:ℝ) (449154353626588056695189/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_188
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0565).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_188 :
    (∫ x in (47/128:ℝ)..(189/512:ℝ), x^8*thetaFirstMode x) ≤ (560807391760297/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (47/128:ℝ) (189/512:ℝ)
    (344476683437/100000000000000:ℝ) (84022268833/25000000000000:ℝ) (449154353626588056695189/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_188 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0565).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_189 :
    (2283114800566353/1000000000000000000000000:ℝ) ≤ ∫ x in (189/512:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-531140713145251965214171273941/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (189/512:ℝ) (95/256:ℝ)-(54109642629131284041/146571795189741237760:ℝ)*thetaPowerMass 8 (189/512:ℝ) (95/256:ℝ)) ≤
      thetaFirstModeFirst (54109642629131284041/146571795189741237760:ℝ)*(thetaPowerMass 9 (189/512:ℝ) (95/256:ℝ)-(54109642629131284041/146571795189741237760:ℝ)*thetaPowerMass 8 (189/512:ℝ) (95/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0288.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (189/512:ℝ) (95/256:ℝ)
    (54109642629131284041/146571795189741237760:ℝ) (83992819407/25000000000000:ℝ) (-531140713145251965214171273941/12500000000000000000000000000000:ℝ) (442112314908028931533417/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_189
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0569).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_189 :
    (∫ x in (189/512:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x) ≤ (5707806537361/2500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (189/512:ℝ) (95/256:ℝ)
    (84022268833/25000000000000:ℝ) (327872808403/100000000000000:ℝ) (442112314908028931533417/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_189 (thetaFirstMode_refined_node_0565).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_190 :
    (290370946684989/125000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(191/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-50970605944413100095651/1250000000000000000000000:ℝ)*(thetaPowerMass 9 (95/256:ℝ) (191/512:ℝ)-(191/512:ℝ)*thetaPowerMass 8 (95/256:ℝ) (191/512:ℝ)) ≤
      thetaFirstModeFirst (191/512:ℝ)*(thetaPowerMass 9 (95/256:ℝ) (191/512:ℝ)-(191/512:ℝ)*thetaPowerMass 8 (95/256:ℝ) (191/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0290.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (95/256:ℝ) (191/512:ℝ)
    (191/512:ℝ) (319824521899/100000000000000:ℝ) (-50970605944413100095651/1250000000000000000000000:ℝ) (217567204265768439319323/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_190
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0571).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_190 :
    (∫ x in (95/256:ℝ)..(191/512:ℝ), x^8*thetaFirstMode x) ≤ (580743512204683/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (95/256:ℝ) (191/512:ℝ)
    (327872808403/100000000000000:ℝ) (31982519633/10000000000000:ℝ) (217567204265768439319323/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_190 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0571).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_191 :
    (295344189113567/125000000000000000000000:ℝ) ≤ ∫ x in (191/512:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x := by
  have hd : (-203823608088457410080610158259/5000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (191/512:ℝ) (3/8:ℝ)-(59486127077809925559/159448540415669455360:ℝ)*thetaPowerMass 8 (191/512:ℝ) (3/8:ℝ)) ≤
      thetaFirstModeFirst (59486127077809925559/159448540415669455360:ℝ)*(thetaPowerMass 9 (191/512:ℝ) (3/8:ℝ)-(59486127077809925559/159448540415669455360:ℝ)*thetaPowerMass 8 (191/512:ℝ) (3/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0291.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (191/512:ℝ) (3/8:ℝ)
    (59486127077809925559/159448540415669455360:ℝ) (39964170157/12500000000000:ℝ) (-203823608088457410080610158259/5000000000000000000000000000000:ℝ) (428220940491343599539703/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_191
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0575).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_191 :
    (∫ x in (191/512:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x) ≤ (36918152162569/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (191/512:ℝ) (3/8:ℝ)
    (31982519633/10000000000000:ℝ) (311943577261/100000000000000:ℝ) (428220940491343599539703/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_191 (thetaFirstMode_refined_node_0571).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
