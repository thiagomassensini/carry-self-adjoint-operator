import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature05
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative07
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative08
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative09

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_160 :
    (12760368031769338343/1000000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(161/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3711745659362169973594036336317/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/16:ℝ) (161/512:ℝ)-(5/16:ℝ)*thetaPowerMass 0 (5/16:ℝ) (161/512:ℝ)) ≤
      thetaFirstModeFirst (5/16:ℝ)*(thetaPowerMass 1 (5/16:ℝ) (161/512:ℝ)-(5/16:ℝ)*thetaPowerMass 0 (5/16:ℝ) (161/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0244.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/16:ℝ) (161/512:ℝ)
    (5/16:ℝ) (330268857621/50000000000000:ℝ) (-3711745659362169973594036336317/50000000000000000000000000000000:ℝ) (134106239829891427230371/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_160
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0480).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_160 :
    (∫ x in (5/16:ℝ)..(161/512:ℝ), x^0*thetaFirstMode x) ≤ (6380201479767910833/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/16:ℝ) (161/512:ℝ)
    (660538949293/100000000000000:ℝ) (646168944989/100000000000000:ℝ) (134106239829891427230371/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_160 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0481).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_161 :
    (6241104104989629101/500000000000000000000000:ℝ) ≤ ∫ x in (161/512:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-182237803669525893533975887351/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (161/512:ℝ) (81/256:ℝ)-(12782224971512359209/40644882680317749760:ℝ)*thetaPowerMass 0 (161/512:ℝ) (81/256:ℝ)) ≤
      thetaFirstModeFirst (12782224971512359209/40644882680317749760:ℝ)*(thetaPowerMass 1 (161/512:ℝ) (81/256:ℝ)-(12782224971512359209/40644882680317749760:ℝ)*thetaPowerMass 0 (161/512:ℝ) (81/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0246.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (161/512:ℝ) (81/256:ℝ)
    (12782224971512359209/40644882680317749760:ℝ) (322965965079/50000000000000:ℝ) (-182237803669525893533975887351/2500000000000000000000000000000:ℝ) (661894603755790120841153/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_161
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0485).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_161 :
    (∫ x in (161/512:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x) ≤ (3120560529483435907/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (161/512:ℝ) (81/256:ℝ)
    (646168944989/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (661894603755790120841153/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_161 (thetaFirstMode_refined_node_0481).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_162 :
    (12209011008844902777/1000000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(163/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1790390357129477066179156723069/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (81/256:ℝ) (163/512:ℝ)-(81/256:ℝ)*thetaPowerMass 0 (81/256:ℝ) (163/512:ℝ)) ≤
      thetaFirstModeFirst (81/256:ℝ)*(thetaPowerMass 1 (81/256:ℝ) (163/512:ℝ)-(81/256:ℝ)*thetaPowerMass 0 (81/256:ℝ) (163/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0247.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (81/256:ℝ) (163/512:ℝ)
    (81/256:ℝ) (158013384979/25000000000000:ℝ) (-1790390357129477066179156723069/25000000000000000000000000000000:ℝ) (653305882545361917059969/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_162
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0486).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_162 :
    (∫ x in (81/256:ℝ)..(163/512:ℝ), x^0*thetaFirstMode x) ≤ (12209044958296913653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (81/256:ℝ) (163/512:ℝ)
    (632054730013/100000000000000:ℝ) (309096504893/50000000000000:ℝ) (653305882545361917059969/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_162 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0487).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_163 :
    (373147323753360603/31250000000000000000000:ℝ) ≤ ∫ x in (163/512:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-140620749959506428356366670507/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (163/512:ℝ) (41/128:ℝ)-(14284239070852168407/44863782688534812160:ℝ)*thetaPowerMass 0 (163/512:ℝ) (41/128:ℝ)) ≤
      thetaFirstModeFirst (14284239070852168407/44863782688534812160:ℝ)*(thetaPowerMass 1 (163/512:ℝ) (41/128:ℝ)-(14284239070852168407/44863782688534812160:ℝ)*thetaPowerMass 0 (163/512:ℝ) (41/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0249.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (163/512:ℝ) (41/128:ℝ)
    (14284239070852168407/44863782688534812160:ℝ) (617967189223/100000000000000:ℝ) (-140620749959506428356366670507/2000000000000000000000000000000:ℝ) (644765869408293189826321/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_163
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0491).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_163 :
    (∫ x in (163/512:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x) ≤ (5970373655625081369/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (163/512:ℝ) (41/128:ℝ)
    (309096504893/50000000000000:ℝ) (151145126999/25000000000000:ℝ) (644765869408293189826321/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_163 (thetaFirstMode_refined_node_0487).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_164 :
    (11677252377667137217/1000000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(165/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-863295009875303196532089278973/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (41/128:ℝ) (165/512:ℝ)-(41/128:ℝ)*thetaPowerMass 0 (41/128:ℝ) (165/512:ℝ)) ≤
      thetaFirstModeFirst (41/128:ℝ)*(thetaPowerMass 1 (41/128:ℝ) (165/512:ℝ)-(41/128:ℝ)*thetaPowerMass 0 (41/128:ℝ) (165/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0250.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (41/128:ℝ) (165/512:ℝ)
    (41/128:ℝ) (302289680351/50000000000000:ℝ) (-863295009875303196532089278973/12500000000000000000000000000000:ℝ) (19883605626830067726437/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_164
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0492).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_164 :
    (∫ x in (41/128:ℝ)..(165/512:ℝ), x^0*thetaFirstMode x) ≤ (11677285367224528987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/128:ℝ) (165/512:ℝ)
    (151145126999/25000000000000:ℝ) (591213966907/100000000000000:ℝ) (19883605626830067726437/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_164 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0493).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_165 :
    (2854640917493659213/250000000000000000000000:ℝ) ≤ ∫ x in (165/512:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-677925107220350352590775899137/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (165/512:ℝ) (83/256:ℝ)-(3188228496497630685/9892200887210173952:ℝ)*thetaPowerMass 0 (165/512:ℝ) (83/256:ℝ)) ≤
      thetaFirstModeFirst (3188228496497630685/9892200887210173952:ℝ)*(thetaPowerMass 1 (165/512:ℝ) (83/256:ℝ)-(3188228496497630685/9892200887210173952:ℝ)*thetaPowerMass 0 (165/512:ℝ) (83/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0252.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (165/512:ℝ) (83/256:ℝ)
    (3188228496497630685/9892200887210173952:ℝ) (29549942907/5000000000000:ℝ) (-677925107220350352590775899137/10000000000000000000000000000000:ℝ) (313917605961490248176989/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_165
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0497).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_165 :
    (∫ x in (165/512:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x) ≤ (713662230161273339/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (165/512:ℝ) (83/256:ℝ)
    (591213966907/100000000000000:ℝ) (578090147677/100000000000000:ℝ) (313917605961490248176989/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_165 (thetaFirstMode_refined_node_0493).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_166 :
    (11164583137635539871/1000000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(167/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1664452793922021710207011376119/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (83/256:ℝ) (167/512:ℝ)-(83/256:ℝ)*thetaPowerMass 0 (83/256:ℝ) (167/512:ℝ)) ≤
      thetaFirstModeFirst (83/256:ℝ)*(thetaPowerMass 1 (83/256:ℝ) (167/512:ℝ)-(83/256:ℝ)*thetaPowerMass 0 (83/256:ℝ) (167/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0253.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (83/256:ℝ) (167/512:ℝ)
    (83/256:ℝ) (4516320641/781250000000:ℝ) (-1664452793922021710207011376119/25000000000000000000000000000000:ℝ) (61944614403501519343567/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_166
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0498).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_166 :
    (∫ x in (83/256:ℝ)..(167/512:ℝ), x^0*thetaFirstMode x) ≤ (5582307592801769831/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (83/256:ℝ) (167/512:ℝ)
    (578090147677/100000000000000:ℝ) (282602915327/50000000000000:ℝ) (61944614403501519343567/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_166 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0499).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_167 :
    (5457625045092886269/500000000000000000000000:ℝ) ≤ ∫ x in (167/512:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3267037786701633939058727331097/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (167/512:ℝ) (21/64:ℝ)-(17766735204530144943/54465262754276508160:ℝ)*thetaPowerMass 0 (167/512:ℝ) (21/64:ℝ)) ≤
      thetaFirstModeFirst (17766735204530144943/54465262754276508160:ℝ)*(thetaPowerMass 1 (167/512:ℝ) (21/64:ℝ)-(17766735204530144943/54465262754276508160:ℝ)*thetaPowerMass 0 (167/512:ℝ) (21/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0255.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (167/512:ℝ) (21/64:ℝ)
    (17766735204530144943/54465262754276508160:ℝ) (565000970919/100000000000000:ℝ) (-3267037786701633939058727331097/50000000000000000000000000000000:ℝ) (611108936940896103336437/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_167
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0503).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_167 :
    (∫ x in (167/512:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x) ≤ (10915281182413615327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (167/512:ℝ) (21/64:ℝ)
    (282602915327/50000000000000:ℝ) (110511563137/20000000000000:ℝ) (611108936940896103336437/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_167 (thetaFirstMode_refined_node_0499).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_168 :
    (5335250119081747587/500000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(169/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-80197951294933113354738958311/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (21/64:ℝ) (169/512:ℝ)-(21/64:ℝ)*thetaPowerMass 0 (21/64:ℝ) (169/512:ℝ)) ≤
      thetaFirstModeFirst (21/64:ℝ)*(thetaPowerMass 1 (21/64:ℝ) (169/512:ℝ)-(21/64:ℝ)*thetaPowerMass 0 (21/64:ℝ) (169/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0256.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (21/64:ℝ) (169/512:ℝ)
    (21/64:ℝ) (2762783753/500000000000:ℝ) (-80197951294933113354738958311/1250000000000000000000000000000:ℝ) (301412166304549438383623/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_168
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0504).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_168 :
    (∫ x in (21/64:ℝ)..(169/512:ℝ), x^0*thetaFirstMode x) ≤ (10670531362715941383/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/64:ℝ) (169/512:ℝ)
    (110511563137/20000000000000:ℝ) (135035730599/25000000000000:ℝ) (301412166304549438383623/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_168 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0505).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_169 :
    (10430273615532665403/1000000000000000000000000:ℝ) ≤ ∫ x in (169/512:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-786928904987340141143637617033/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (169/512:ℝ) (85/256:ℝ)-(19775858017267564641/59907066245820060160:ℝ)*thetaPowerMass 0 (169/512:ℝ) (85/256:ℝ)) ≤
      thetaFirstModeFirst (19775858017267564641/59907066245820060160:ℝ)*(thetaPowerMass 1 (169/512:ℝ) (85/256:ℝ)-(19775858017267564641/59907066245820060160:ℝ)*thetaPowerMass 0 (169/512:ℝ) (85/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0258.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (169/512:ℝ) (85/256:ℝ)
    (19775858017267564641/59907066245820060160:ℝ) (53994786779/10000000000000:ℝ) (-786928904987340141143637617033/12500000000000000000000000000000:ℝ) (594593054343830348494757/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_169
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0509).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_169 :
    (∫ x in (169/512:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x) ≤ (5215151902679153237/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (169/512:ℝ) (85/256:ℝ)
    (135035730599/25000000000000:ℝ) (527957990481/100000000000000:ℝ) (594593054343830348494757/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_169 (thetaFirstMode_refined_node_0505).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_170 :
    (10194506764565672751/1000000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(171/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3090176921161734740166798406527/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (85/256:ℝ) (171/512:ℝ)-(85/256:ℝ)*thetaPowerMass 0 (85/256:ℝ) (171/512:ℝ)) ≤
      thetaFirstModeFirst (85/256:ℝ)*(thetaPowerMass 1 (85/256:ℝ) (171/512:ℝ)-(85/256:ℝ)*thetaPowerMass 0 (85/256:ℝ) (171/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0259.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (85/256:ℝ) (171/512:ℝ)
    (85/256:ℝ) (16498655151/3125000000000:ℝ) (-3090176921161734740166798406527/50000000000000000000000000000000:ℝ) (586415806713032535282343/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_170
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0510).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_170 :
    (∫ x in (85/256:ℝ)..(171/512:ℝ), x^0*thetaFirstMode x) ≤ (10194536983819272871/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (85/256:ℝ) (171/512:ℝ)
    (527957990481/100000000000000:ℝ) (20639995199/4000000000000:ℝ) (586415806713032535282343/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_170 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0511).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_171 :
    (2490785116514883539/250000000000000000000000:ℝ) ≤ ∫ x in (171/512:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-121264719200422566392135829323/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (171/512:ℝ) (43/128:ℝ)-(21984457092577248159/65818805832858856960:ℝ)*thetaPowerMass 0 (171/512:ℝ) (43/128:ℝ)) ≤
      thetaFirstModeFirst (21984457092577248159/65818805832858856960:ℝ)*(thetaPowerMass 1 (171/512:ℝ) (43/128:ℝ)-(21984457092577248159/65818805832858856960:ℝ)*thetaPowerMass 0 (171/512:ℝ) (43/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0261.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (171/512:ℝ) (43/128:ℝ)
    (21984457092577248159/65818805832858856960:ℝ) (515814204633/100000000000000:ℝ) (-121264719200422566392135829323/2000000000000000000000000000000:ℝ) (9035832429292167225019/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_171
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0515).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_171 :
    (∫ x in (171/512:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x) ≤ (9963169771491425349/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (171/512:ℝ) (43/128:ℝ)
    (20639995199/4000000000000:ℝ) (252132735761/50000000000000:ℝ) (9035832429292167225019/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_171 (thetaFirstMode_refined_node_0511).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_172 :
    (9736112114943106537/1000000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(173/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1487820270524623783224479554439/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (43/128:ℝ) (173/512:ℝ)-(43/128:ℝ)*thetaPowerMass 0 (43/128:ℝ) (173/512:ℝ)) ≤
      thetaFirstModeFirst (43/128:ℝ)*(thetaPowerMass 1 (43/128:ℝ) (173/512:ℝ)-(43/128:ℝ)*thetaPowerMass 0 (43/128:ℝ) (173/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0262.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (43/128:ℝ) (173/512:ℝ)
    (43/128:ℝ) (63033060527/12500000000000:ℝ) (-1487820270524623783224479554439/25000000000000000000000000000000:ℝ) (570226127518297911390171/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_172
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0516).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_172 :
    (∫ x in (43/128:ℝ)..(173/512:ℝ), x^0*thetaFirstMode x) ≤ (973614144686695443/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/128:ℝ) (173/512:ℝ)
    (252132735761/50000000000000:ℝ) (246375833319/50000000000000:ℝ) (570226127518297911390171/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_172 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0517).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_173 :
    (2378340814957329387/250000000000000000000000:ℝ) ≤ ∫ x in (173/512:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-583740538898351447989147005929/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (173/512:ℝ) (87/256:ℝ)-(24409651773064480857/72234846544296732160:ℝ)*thetaPowerMass 0 (173/512:ℝ) (87/256:ℝ)) ≤
      thetaFirstModeFirst (24409651773064480857/72234846544296732160:ℝ)*(thetaPowerMass 1 (173/512:ℝ) (87/256:ℝ)-(24409651773064480857/72234846544296732160:ℝ)*thetaPowerMass 0 (173/512:ℝ) (87/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0264.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (173/512:ℝ) (87/256:ℝ)
    (24409651773064480857/72234846544296732160:ℝ) (492574961981/100000000000000:ℝ) (-583740538898351447989147005929/10000000000000000000000000000000:ℝ) (562215010807529520582331/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_173
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0521).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_173 :
    (∫ x in (173/512:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x) ≤ (9513391698625582551/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (173/512:ℝ) (87/256:ℝ)
    (246375833319/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (562215010807529520582331/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_173 (thetaFirstMode_refined_node_0517).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_174 :
    (464741608401349123/50000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(175/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-286426617038656559582589808677/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (87/256:ℝ) (175/512:ℝ)-(87/256:ℝ)*thetaPowerMass 0 (87/256:ℝ) (175/512:ℝ)) ≤
      thetaFirstModeFirst (87/256:ℝ)*(thetaPowerMass 1 (87/256:ℝ) (175/512:ℝ)-(87/256:ℝ)*thetaPowerMass 0 (87/256:ℝ) (175/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0265.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (87/256:ℝ) (175/512:ℝ)
    (87/256:ℝ) (48145443793/10000000000000:ℝ) (-286426617038656559582589808677/5000000000000000000000000000000:ℝ) (277130277167533315632323/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_174
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0522).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_174 :
    (∫ x in (87/256:ℝ)..(175/512:ℝ), x^0*thetaFirstMode x) ≤ (9294860630478342159/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (87/256:ℝ) (175/512:ℝ)
    (481455387969/100000000000000:ℝ) (470373579529/100000000000000:ℝ) (277130277167533315632323/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_174 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0523).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_175 :
    (1816092235229450957/200000000000000000000000:ℝ) ≤ ∫ x in (175/512:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2808926533174888998017826497601/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (175/512:ℝ) (11/32:ℝ)-(5413961127233958075/15838324523948298752:ℝ)*thetaPowerMass 0 (175/512:ℝ) (11/32:ℝ)) ≤
      thetaFirstModeFirst (5413961127233958075/15838324523948298752:ℝ)*(thetaPowerMass 1 (175/512:ℝ) (11/32:ℝ)-(5413961127233958075/15838324523948298752:ℝ)*thetaPowerMass 0 (175/512:ℝ) (11/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0267.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (175/512:ℝ) (11/32:ℝ)
    (5413961127233958075/15838324523948298752:ℝ) (117551363383/25000000000000:ℝ) (-2808926533174888998017826497601/50000000000000000000000000000000:ℝ) (109272673616227367408399/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_175
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0527).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_175 :
    (∫ x in (175/512:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x) ≤ (4540244382976378843/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (175/512:ℝ) (11/32:ℝ)
    (470373579529/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (109272673616227367408399/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_175 (thetaFirstMode_refined_node_0523).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_176 :
    (8870189442273385671/1000000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(177/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-344501255115077538441379609811/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/32:ℝ) (177/512:ℝ)-(11/32:ℝ)*thetaPowerMass 0 (11/32:ℝ) (177/512:ℝ)) ≤
      thetaFirstModeFirst (11/32:ℝ)*(thetaPowerMass 1 (11/32:ℝ) (177/512:ℝ)-(11/32:ℝ)*thetaPowerMass 0 (11/32:ℝ) (177/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0268.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/32:ℝ) (177/512:ℝ)
    (11/32:ℝ) (459502293119/100000000000000:ℝ) (-344501255115077538441379609811/6250000000000000000000000000000:ℝ) (538524042979173877513599/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_176
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0528).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_176 :
    (∫ x in (11/32:ℝ)..(177/512:ℝ), x^0*thetaFirstMode x) ≤ (2217554263253001873/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/32:ℝ) (177/512:ℝ)
    (57437900869/12500000000000:ℝ) (448841257713/100000000000000:ℝ) (538524042979173877513599/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_176 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0529).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_177 :
    (270748753440879427/31250000000000000000000:ℝ) ≤ ∫ x in (177/512:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-67556131681634168817799078999/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (177/512:ℝ) (89/256:ℝ)-(29984600961233742393/86727736009265052160:ℝ)*thetaPowerMass 0 (177/512:ℝ) (89/256:ℝ)) ≤
      thetaFirstModeFirst (29984600961233742393/86727736009265052160:ℝ)*(thetaPowerMass 1 (177/512:ℝ) (89/256:ℝ)-(29984600961233742393/86727736009265052160:ℝ)*thetaPowerMass 0 (177/512:ℝ) (89/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0270.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (177/512:ℝ) (89/256:ℝ)
    (29984600961233742393/86727736009265052160:ℝ) (89736266843/20000000000000:ℝ) (-67556131681634168817799078999/1250000000000000000000000000000:ℝ) (530743150886797466724179/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_177
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0533).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_177 :
    (∫ x in (177/512:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x) ≤ (433199343424915063/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (177/512:ℝ) (89/256:ℝ)
    (448841257713/100000000000000:ℝ) (219192370681/50000000000000:ℝ) (530743150886797466724179/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_177 (thetaFirstMode_refined_node_0529).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_178 :
    (1057714155730891617/125000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(179/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10603309665933449817666242951/200000000000000000000000000000:ℝ)*(thetaPowerMass 1 (89/256:ℝ) (179/512:ℝ)-(89/256:ℝ)*thetaPowerMass 0 (89/256:ℝ) (179/512:ℝ)) ≤
      thetaFirstModeFirst (89/256:ℝ)*(thetaPowerMass 1 (89/256:ℝ) (179/512:ℝ)-(89/256:ℝ)*thetaPowerMass 0 (89/256:ℝ) (179/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0271.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (89/256:ℝ) (179/512:ℝ)
    (89/256:ℝ) (43838386269/10000000000000:ℝ) (-10603309665933449817666242951/200000000000000000000000000000:ℝ) (523021244573003219654143/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_178
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0534).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_178 :
    (∫ x in (89/256:ℝ)..(179/512:ℝ), x^0*thetaFirstMode x) ≤ (8461740022488356703/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (89/256:ℝ) (179/512:ℝ)
    (219192370681/50000000000000:ℝ) (53516336217/12500000000000:ℝ) (523021244573003219654143/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_178 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0535).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_179 :
    (6455775639127367/781250000000000000000:ℝ) ≤ ∫ x in (179/512:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2598613728867339888637141347023/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (179/512:ℝ) (45/128:ℝ)-(33175116720304347591/94884058348837864960:ℝ)*thetaPowerMass 0 (179/512:ℝ) (45/128:ℝ)) ≤
      thetaFirstModeFirst (33175116720304347591/94884058348837864960:ℝ)*(thetaPowerMass 1 (179/512:ℝ) (45/128:ℝ)-(33175116720304347591/94884058348837864960:ℝ)*thetaPowerMass 0 (179/512:ℝ) (45/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0273.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (179/512:ℝ) (45/128:ℝ)
    (33175116720304347591/94884058348837864960:ℝ) (42797860779/10000000000000:ℝ) (-2598613728867339888637141347023/50000000000000000000000000000000:ℝ) (257679428850872338749071/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_179
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0539).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_179 :
    (∫ x in (179/512:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x) ≤ (1652683752494619451/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (179/512:ℝ) (45/128:ℝ)
    (53516336217/12500000000000:ℝ) (16723046287/4000000000000:ℝ) (257679428850872338749071/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_179 (thetaFirstMode_refined_node_0535).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_180 :
    (8068939817418467843/1000000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(181/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-101946906098692603922936527419/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (45/128:ℝ) (181/512:ℝ)-(45/128:ℝ)*thetaPowerMass 0 (45/128:ℝ) (181/512:ℝ)) ≤
      thetaFirstModeFirst (45/128:ℝ)*(thetaPowerMass 1 (45/128:ℝ) (181/512:ℝ)-(45/128:ℝ)*thetaPowerMass 0 (45/128:ℝ) (181/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0274.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (45/128:ℝ) (181/512:ℝ)
    (45/128:ℝ) (418075312637/100000000000000:ℝ) (-101946906098692603922936527419/2000000000000000000000000000000:ℝ) (507756504821714887282653/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_180
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0540).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_180 :
    (∫ x in (45/128:ℝ)..(181/512:ℝ), x^0*thetaFirstMode x) ≤ (1613793155484031683/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/128:ℝ) (181/512:ℝ)
    (16723046287/4000000000000:ℝ) (204109110361/50000000000000:ℝ) (507756504821714887282653/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_180 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0541).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_181 :
    (7878299053970837799/1000000000000000000000000:ℝ) ≤ ∫ x in (181/512:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-499597174110084443344472835261/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (181/512:ℝ) (91/256:ℝ)-(36663910216296708609/103703836492258332160:ℝ)*thetaPowerMass 0 (181/512:ℝ) (91/256:ℝ)) ≤
      thetaFirstModeFirst (36663910216296708609/103703836492258332160:ℝ)*(thetaPowerMass 1 (181/512:ℝ) (91/256:ℝ)-(36663910216296708609/103703836492258332160:ℝ)*thetaPowerMass 0 (181/512:ℝ) (91/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0276.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (181/512:ℝ) (91/256:ℝ)
    (36663910216296708609/103703836492258332160:ℝ) (408073633973/100000000000000:ℝ) (-499597174110084443344472835261/10000000000000000000000000000000:ℝ) (250107340691448839721707/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_181
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0545).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_181 :
    (∫ x in (181/512:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x) ≤ (7878324201660596221/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (181/512:ℝ) (91/256:ℝ)
    (204109110361/50000000000000:ℝ) (398553980321/100000000000000:ℝ) (250107340691448839721707/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_181 (thetaFirstMode_refined_node_0541).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_182 :
    (7691412457929201641/1000000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(183/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-97979970220078608528250909399/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (91/256:ℝ) (183/512:ℝ)-(91/256:ℝ)*thetaPowerMass 0 (91/256:ℝ) (183/512:ℝ)) ≤
      thetaFirstModeFirst (91/256:ℝ)*(thetaPowerMass 1 (91/256:ℝ) (183/512:ℝ)-(91/256:ℝ)*thetaPowerMass 0 (91/256:ℝ) (183/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0277.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (91/256:ℝ) (183/512:ℝ)
    (91/256:ℝ) (49819146113/12500000000000:ℝ) (-97979970220078608528250909399/2000000000000000000000000000000:ℝ) (492733863727986470362623/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_182
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0546).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_182 :
    (∫ x in (91/256:ℝ)..(183/512:ℝ), x^0*thetaFirstMode x) ≤ (769143761865842383/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (91/256:ℝ) (183/512:ℝ)
    (398553980321/100000000000000:ℝ) (77816111801/20000000000000:ℝ) (492733863727986470362623/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_182 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0547).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_183 :
    (7508225696537468963/1000000000000000000000000:ℝ) ≤ ∫ x in (183/512:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-192025186013557212285758283/4000000000000000000000000000:ℝ)*(thetaPowerMass 1 (183/512:ℝ) (23/64:ℝ)-(40475102494972215807/113232801681326748160:ℝ)*thetaPowerMass 0 (183/512:ℝ) (23/64:ℝ)) ≤
      thetaFirstModeFirst (40475102494972215807/113232801681326748160:ℝ)*(thetaPowerMass 1 (183/512:ℝ) (23/64:ℝ)-(40475102494972215807/113232801681326748160:ℝ)*thetaPowerMass 0 (183/512:ℝ) (23/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0279.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (183/512:ℝ) (23/64:ℝ)
    (40475102494972215807/113232801681326748160:ℝ) (388943135103/100000000000000:ℝ) (-192025186013557212285758283/4000000000000000000000000000:ℝ) (485314509120892510886041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_183
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0551).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_183 :
    (∫ x in (183/512:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x) ≤ (7508250064653171939/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (183/512:ℝ) (23/64:ℝ)
    (77816111801/20000000000000:ℝ) (379795103081/100000000000000:ℝ) (485314509120892510886041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_183 (thetaFirstMode_refined_node_0547).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_184 :
    (3664340826706639937/500000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(185/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-147078746446992774982606184319/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (23/64:ℝ) (185/512:ℝ)-(23/64:ℝ)*thetaPowerMass 0 (23/64:ℝ) (185/512:ℝ)) ≤
      thetaFirstModeFirst (23/64:ℝ)*(thetaPowerMass 1 (23/64:ℝ) (185/512:ℝ)-(23/64:ℝ)*thetaPowerMass 0 (23/64:ℝ) (185/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0280.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (23/64:ℝ) (185/512:ℝ)
    (23/64:ℝ) (37979432379/10000000000000:ℝ) (-147078746446992774982606184319/3125000000000000000000000000000:ℝ) (119489263940876827368961/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_184
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0552).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_184 :
    (∫ x in (23/64:ℝ)..(185/512:ℝ), x^0*thetaFirstMode x) ≤ (7328706032087612757/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/64:ℝ) (185/512:ℝ)
    (379795103081/100000000000000:ℝ) (46336847787/12500000000000:ℝ) (119489263940876827368961/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_184 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0553).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_185 :
    (3576363433731741581/500000000000000000000000:ℝ) ≤ ∫ x in (185/512:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2305552965535923343311592752203/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (185/512:ℝ) (93/256:ℝ)-(8926893532018987965/24703856487388477952:ℝ)*thetaPowerMass 0 (185/512:ℝ) (93/256:ℝ)) ≤
      thetaFirstModeFirst (8926893532018987965/24703856487388477952:ℝ)*(thetaPowerMass 1 (185/512:ℝ) (93/256:ℝ)-(8926893532018987965/24703856487388477952:ℝ)*thetaPowerMass 0 (185/512:ℝ) (93/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0282.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (185/512:ℝ) (93/256:ℝ)
    (8926893532018987965/24703856487388477952:ℝ) (370564202331/100000000000000:ℝ) (-2305552965535923343311592752203/50000000000000000000000000000000:ℝ) (235330961414012658325869/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_185
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0557).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_185 :
    (∫ x in (185/512:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x) ≤ (715275047296711493/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (185/512:ℝ) (93/256:ℝ)
    (46336847787/12500000000000:ℝ) (72355358003/20000000000000:ℝ) (235330961414012658325869/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_185 (thetaFirstMode_refined_node_0553).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_186 :
    (3490152594222374493/500000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(187/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-28248833794583401980344666087/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (93/256:ℝ) (187/512:ℝ)-(93/256:ℝ)*thetaPowerMass 0 (93/256:ℝ) (187/512:ℝ)) ≤
      thetaFirstModeFirst (93/256:ℝ)*(thetaPowerMass 1 (93/256:ℝ) (187/512:ℝ)-(93/256:ℝ)*thetaPowerMass 0 (93/256:ℝ) (187/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0283.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (93/256:ℝ) (187/512:ℝ)
    (93/256:ℝ) (180888020937/50000000000000:ℝ) (-28248833794583401980344666087/625000000000000000000000000000:ℝ) (463429510493183864685853/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_186
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0558).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_186 :
    (∫ x in (93/256:ℝ)..(187/512:ℝ), x^0*thetaFirstMode x) ≤ (6980328802101808549/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (93/256:ℝ) (187/512:ℝ)
    (72355358003/20000000000000:ℝ) (2824306747/800000000000:ℝ) (463429510493183864685853/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_186 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0559).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_187 :
    (6811364040344357257/1000000000000000000000000:ℝ) ≤ ∫ x in (187/512:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-276706495516334150202936321061/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (187/512:ℝ) (47/128:ℝ)-(49169526224045867343/134614321254731292160:ℝ)*thetaPowerMass 0 (187/512:ℝ) (47/128:ℝ)) ≤
      thetaFirstModeFirst (49169526224045867343/134614321254731292160:ℝ)*(thetaPowerMass 1 (187/512:ℝ) (47/128:ℝ)-(49169526224045867343/134614321254731292160:ℝ)*thetaPowerMass 0 (187/512:ℝ) (47/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0285.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (187/512:ℝ) (47/128:ℝ)
    (49169526224045867343/134614321254731292160:ℝ) (11028571917/3125000000000:ℝ) (-276706495516334150202936321061/6250000000000000000000000000000:ℝ) (228130099991295207900149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_187
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0563).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_187 :
    (∫ x in (187/512:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x) ≤ (3405693450047421297/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (187/512:ℝ) (47/128:ℝ)
    (2824306747/800000000000:ℝ) (344476683437/100000000000000:ℝ) (228130099991295207900149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_187 (thetaFirstMode_refined_node_0559).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_188 :
    (3322924125340891357/500000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(189/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-271173856885532170522390272867/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (47/128:ℝ) (189/512:ℝ)-(47/128:ℝ)*thetaPowerMass 0 (47/128:ℝ) (189/512:ℝ)) ≤
      thetaFirstModeFirst (47/128:ℝ)*(thetaPowerMass 1 (47/128:ℝ) (189/512:ℝ)-(47/128:ℝ)*thetaPowerMass 0 (47/128:ℝ) (189/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0286.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (47/128:ℝ) (189/512:ℝ)
    (47/128:ℝ) (86118991371/25000000000000:ℝ) (-271173856885532170522390272867/6250000000000000000000000000000:ℝ) (449154353626588056695189/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_188
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0564).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_188 :
    (∫ x in (47/128:ℝ)..(189/512:ℝ), x^0*thetaFirstMode x) ≤ (3322935558126251391/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/128:ℝ) (189/512:ℝ)
    (344476683437/100000000000000:ℝ) (84022268833/25000000000000:ℝ) (449154353626588056695189/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_188 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0565).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_189 :
    (6483706140729074413/1000000000000000000000000:ℝ) ≤ ∫ x in (189/512:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-531140713145251965214171273941/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (189/512:ℝ) (95/256:ℝ)-(54109642629131284041/146571795189741237760:ℝ)*thetaPowerMass 0 (189/512:ℝ) (95/256:ℝ)) ≤
      thetaFirstModeFirst (54109642629131284041/146571795189741237760:ℝ)*(thetaPowerMass 1 (189/512:ℝ) (95/256:ℝ)-(54109642629131284041/146571795189741237760:ℝ)*thetaPowerMass 0 (189/512:ℝ) (95/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0288.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (189/512:ℝ) (95/256:ℝ)
    (54109642629131284041/146571795189741237760:ℝ) (83992819407/25000000000000:ℝ) (-531140713145251965214171273941/12500000000000000000000000000000:ℝ) (442112314908028931533417/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_189
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0569).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_189 :
    (∫ x in (189/512:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x) ≤ (6483728271396683139/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (189/512:ℝ) (95/256:ℝ)
    (84022268833/25000000000000:ℝ) (327872808403/100000000000000:ℝ) (442112314908028931533417/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_189 (thetaFirstMode_refined_node_0565).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_190 :
    (6324883526244392881/1000000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(191/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2081663105498706539138262658599/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (95/256:ℝ) (191/512:ℝ)-(95/256:ℝ)*thetaPowerMass 0 (95/256:ℝ) (191/512:ℝ)) ≤
      thetaFirstModeFirst (95/256:ℝ)*(thetaPowerMass 1 (95/256:ℝ) (191/512:ℝ)-(95/256:ℝ)*thetaPowerMass 0 (95/256:ℝ) (191/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0289.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (95/256:ℝ) (191/512:ℝ)
    (95/256:ℝ) (20492007481/6250000000000:ℝ) (-2081663105498706539138262658599/50000000000000000000000000000000:ℝ) (217567204265768439319323/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_190
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0570).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_190 :
    (∫ x in (95/256:ℝ)..(191/512:ℝ), x^0*thetaFirstMode x) ≤ (1581226415118066219/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (95/256:ℝ) (191/512:ℝ)
    (327872808403/100000000000000:ℝ) (31982519633/10000000000000:ℝ) (217567204265768439319323/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_190 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0571).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_191 :
    (6169329636921854933/1000000000000000000000000:ℝ) ≤ ∫ x in (191/512:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x := by
  have hd : (-203823608088457410080610158259/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (191/512:ℝ) (3/8:ℝ)-(59486127077809925559/159448540415669455360:ℝ)*thetaPowerMass 0 (191/512:ℝ) (3/8:ℝ)) ≤
      thetaFirstModeFirst (59486127077809925559/159448540415669455360:ℝ)*(thetaPowerMass 1 (191/512:ℝ) (3/8:ℝ)-(59486127077809925559/159448540415669455360:ℝ)*thetaPowerMass 0 (191/512:ℝ) (3/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0291.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (191/512:ℝ) (3/8:ℝ)
    (59486127077809925559/159448540415669455360:ℝ) (39964170157/12500000000000:ℝ) (-203823608088457410080610158259/5000000000000000000000000000000:ℝ) (428220940491343599539703/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_191
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0575).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_191 :
    (∫ x in (191/512:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x) ≤ (6169351055047074269/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (191/512:ℝ) (3/8:ℝ)
    (31982519633/10000000000000:ℝ) (311943577261/100000000000000:ℝ) (428220940491343599539703/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_191 (thetaFirstMode_refined_node_0571).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
