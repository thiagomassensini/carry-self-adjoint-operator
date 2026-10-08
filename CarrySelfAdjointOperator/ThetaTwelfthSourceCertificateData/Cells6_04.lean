import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature04
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative06
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative07

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_6_128 :
    (1233726953580871/200000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(129/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-774399407407011937221351/6250000000000000000000000:ℝ)*(thetaPowerMass 7 (1/4:ℝ) (129/512:ℝ)-(129/512:ℝ)*thetaPowerMass 6 (1/4:ℝ) (129/512:ℝ)) ≤
      thetaFirstModeFirst (129/512:ℝ)*(thetaPowerMass 7 (1/4:ℝ) (129/512:ℝ)-(129/512:ℝ)*thetaPowerMass 6 (1/4:ℝ) (129/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0197.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (1/4:ℝ) (129/512:ℝ)
    (129/512:ℝ) (1251584440439/100000000000000:ℝ) (-774399407407011937221351/6250000000000000000000000:ℝ) (966295758513919120153063/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_128
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0385).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_128 :
    (∫ x in (1/4:ℝ)..(129/512:ℝ), x^6*thetaFirstMode x) ≤ (6168646462117373/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/4:ℝ) (129/512:ℝ)
    (1275971452837/100000000000000:ℝ) (312896628009/25000000000000:ℝ) (966295758513919120153063/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_128 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0385).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_129 :
    (3169284063381949/500000000000000000000000:ℝ) ≤ ∫ x in (129/512:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-387078605595862628952036844953/3125000000000000000000000000000:ℝ)*(thetaPowerMass 7 (129/512:ℝ) (65/256:ℝ)-(1740175468704392841/6905636680726120960:ℝ)*thetaPowerMass 6 (129/512:ℝ) (65/256:ℝ)) ≤
      thetaFirstModeFirst (1740175468704392841/6905636680726120960:ℝ)*(thetaPowerMass 7 (129/512:ℝ) (65/256:ℝ)-(1740175468704392841/6905636680726120960:ℝ)*thetaPowerMass 6 (129/512:ℝ) (65/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0198.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (129/512:ℝ) (65/256:ℝ)
    (1740175468704392841/6905636680726120960:ℝ) (312771103803/25000000000000:ℝ) (-387078605595862628952036844953/3125000000000000000000000000000:ℝ) (478333949264452833596727/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_129
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0389).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_129 :
    (∫ x in (129/512:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x) ≤ (6338581702777807/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (129/512:ℝ) (65/256:ℝ)
    (312896628009/25000000000000:ℝ) (1227570184781/100000000000000:ℝ) (478333949264452833596727/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_129 (thetaFirstMode_refined_node_0385).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_130 :
    (3255169254335143/500000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(131/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-187760799086849630326783/1562500000000000000000000:ℝ)*(thetaPowerMass 7 (65/256:ℝ) (131/512:ℝ)-(131/512:ℝ)*thetaPowerMass 6 (65/256:ℝ) (131/512:ℝ)) ≤
      thetaFirstModeFirst (131/512:ℝ)*(thetaPowerMass 7 (65/256:ℝ) (131/512:ℝ)-(131/512:ℝ)*thetaPowerMass 6 (65/256:ℝ) (131/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0200.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (65/256:ℝ) (131/512:ℝ)
    (131/512:ℝ) (37622399689/3125000000000:ℝ) (-187760799086849630326783/1562500000000000000000000:ℝ) (947052643874298212119509/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_130
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0391).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_130 :
    (∫ x in (65/256:ℝ)..(131/512:ℝ), x^6*thetaFirstMode x) ≤ (6510350993115817/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (65/256:ℝ) (131/512:ℝ)
    (1227570184781/100000000000000:ℝ) (150489849797/12500000000000:ℝ) (947052643874298212119509/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_130 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0391).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_131 :
    (167096792981673/25000000000000000000000:ℝ) ≤ ∫ x in (131/512:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-187702365522042567234998070069/1562500000000000000000000000000:ℝ)*(thetaPowerMass 7 (131/512:ℝ) (33/128:ℝ)-(1998562918031146359/7809963970327836160:ℝ)*thetaPowerMass 6 (131/512:ℝ) (33/128:ℝ)) ≤
      thetaFirstModeFirst (1998562918031146359/7809963970327836160:ℝ)*(thetaPowerMass 7 (131/512:ℝ) (33/128:ℝ)-(1998562918031146359/7809963970327836160:ℝ)*thetaPowerMass 6 (131/512:ℝ) (33/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0201.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (131/512:ℝ) (33/128:ℝ)
    (1998562918031146359/7809963970327836160:ℝ) (601719622347/50000000000000:ℝ) (-187702365522042567234998070069/1562500000000000000000000000000:ℝ) (93745131236830700098271/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_131
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0395).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_131 :
    (∫ x in (131/512:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x) ≤ (6683886241199061/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (131/512:ℝ) (33/128:ℝ)
    (150489849797/12500000000000:ℝ) (9223661601/781250000000:ℝ) (93745131236830700098271/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_131 (thetaFirstMode_refined_node_0391).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_132 :
    (6859103742605743/1000000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(133/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-291262451907453407747717/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (33/128:ℝ) (133/512:ℝ)-(133/512:ℝ)*thetaPowerMass 6 (33/128:ℝ) (133/512:ℝ)) ≤
      thetaFirstModeFirst (133/512:ℝ)*(thetaPowerMass 7 (33/128:ℝ) (133/512:ℝ)-(133/512:ℝ)*thetaPowerMass 6 (33/128:ℝ) (133/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0203.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (33/128:ℝ) (133/512:ℝ)
    (133/512:ℝ) (115769423549/10000000000000:ℝ) (-291262451907453407747717/2500000000000000000000000:ℝ) (927865210544466697500661/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_132
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0397).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_132 :
    (∫ x in (33/128:ℝ)..(133/512:ℝ), x^6*thetaFirstMode x) ≤ (6859117048465471/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (33/128:ℝ) (133/512:ℝ)
    (9223661601/781250000000:ℝ) (578848090929/50000000000000:ℝ) (927865210544466697500661/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_132 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0397).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_133 :
    (7035955253184893/1000000000000000000000000:ℝ) ≤ ∫ x in (133/512:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5823444710741132072874374521599/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (133/512:ℝ) (67/256:ℝ)-(2290508312768691057/8816267219187228160:ℝ)*thetaPowerMass 6 (133/512:ℝ) (67/256:ℝ)) ≤
      thetaFirstModeFirst (2290508312768691057/8816267219187228160:ℝ)*(thetaPowerMass 7 (133/512:ℝ) (67/256:ℝ)-(2290508312768691057/8816267219187228160:ℝ)*thetaPowerMass 6 (133/512:ℝ) (67/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0204.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (133/512:ℝ) (67/256:ℝ)
    (2290508312768691057/8816267219187228160:ℝ) (578619100303/50000000000000:ℝ) (-5823444710741132072874374521599/50000000000000000000000000000000:ℝ) (918295633360136582510243/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_133
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0401).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_133 :
    (∫ x in (133/512:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x) ≤ (7035970761786667/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (133/512:ℝ) (67/256:ℝ)
    (578848090929/50000000000000:ℝ) (567558816199/50000000000000:ℝ) (918295633360136582510243/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_133 (thetaFirstMode_refined_node_0397).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_134 :
    (288574334804539/40000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(135/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-22054272527138244735391/195312500000000000000000:ℝ)*(thetaPowerMass 7 (67/256:ℝ) (135/512:ℝ)-(135/512:ℝ)*thetaPowerMass 6 (67/256:ℝ) (135/512:ℝ)) ≤
      thetaFirstModeFirst (135/512:ℝ)*(thetaPowerMass 7 (67/256:ℝ) (135/512:ℝ)-(135/512:ℝ)*thetaPowerMass 6 (67/256:ℝ) (135/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0206.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (67/256:ℝ) (135/512:ℝ)
    (135/512:ℝ) (69555468773/6250000000000:ℝ) (-22054272527138244735391/195312500000000000000000:ℝ) (454371931943431231700863/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_134
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0403).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_134 :
    (∫ x in (67/256:ℝ)..(135/512:ℝ), x^6*thetaFirstMode x) ≤ (1442874505669291/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (67/256:ℝ) (135/512:ℝ)
    (567558816199/50000000000000:ℝ) (1112889386079/100000000000000:ℝ) (454371931943431231700863/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_134 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0403).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_135 :
    (29576915268829/4000000000000000000000:ℝ) ≤ ∫ x in (135/512:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1411038228199264502842671683349/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (135/512:ℝ) (17/64:ℝ)-(523953028089808515/1986849740868925952:ℝ)*thetaPowerMass 6 (135/512:ℝ) (17/64:ℝ)) ≤
      thetaFirstModeFirst (523953028089808515/1986849740868925952:ℝ)*(thetaPowerMass 7 (135/512:ℝ) (17/64:ℝ)-(523953028089808515/1986849740868925952:ℝ)*thetaPowerMass 6 (135/512:ℝ) (17/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0207.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (135/512:ℝ) (17/64:ℝ)
    (523953028089808515/1986849740868925952:ℝ) (222490410103/20000000000000:ℝ) (-1411038228199264502842671683349/12500000000000000000000000000000:ℝ) (179842234606979033115729/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_135
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0407).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_135 :
    (∫ x in (135/512:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x) ≤ (295769814133079/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (135/512:ℝ) (17/64:ℝ)
    (1112889386079/100000000000000:ℝ) (1091007799227/100000000000000:ℝ) (179842234606979033115729/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_135 (thetaFirstMode_refined_node_0403).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_136 :
    (3787747559515671/500000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(137/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1367566462204701759016853/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (17/64:ℝ) (137/512:ℝ)-(137/512:ℝ)*thetaPowerMass 6 (17/64:ℝ) (137/512:ℝ)) ≤
      thetaFirstModeFirst (137/512:ℝ)*(thetaPowerMass 7 (17/64:ℝ) (137/512:ℝ)-(137/512:ℝ)*thetaPowerMass 6 (17/64:ℝ) (137/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0209.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (17/64:ℝ) (137/512:ℝ)
    (137/512:ℝ) (1069467409093/100000000000000:ℝ) (-1367566462204701759016853/12500000000000000000000000:ℝ) (889698819256701636650141/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_136
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0409).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_136 :
    (∫ x in (17/64:ℝ)..(137/512:ℝ), x^6*thetaFirstMode x) ≤ (7575510160320349/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (17/64:ℝ) (137/512:ℝ)
    (1091007799227/100000000000000:ℝ) (213893847089/20000000000000:ℝ) (889698819256701636650141/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_136 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0409).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_137 :
    (310322729993677/40000000000000000000000:ℝ) ≤ ∫ x in (137/512:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-683573308254643201407023355147/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (137/512:ℝ) (69/256:ℝ)-(2990441164477942593/11174368100215452160:ℝ)*thetaPowerMass 6 (137/512:ℝ) (69/256:ℝ)) ≤
      thetaFirstModeFirst (2990441164477942593/11174368100215452160:ℝ)*(thetaPowerMass 7 (137/512:ℝ) (69/256:ℝ)-(2990441164477942593/11174368100215452160:ℝ)*thetaPowerMass 6 (137/512:ℝ) (69/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0210.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (137/512:ℝ) (69/256:ℝ)
    (2990441164477942593/11174368100215452160:ℝ) (534525830191/50000000000000:ℝ) (-683573308254643201407023355147/6250000000000000000000000000000:ℝ) (880208048276601117164071/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_137
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0413).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_137 :
    (∫ x in (137/512:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x) ≤ (1939521463592431/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (137/512:ℝ) (69/256:ℝ)
    (213893847089/20000000000000:ℝ) (65516879131/6250000000000:ℝ) (880208048276601117164071/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_137 (thetaFirstMode_refined_node_0409).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_138 :
    (7941873432952133/1000000000000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(139/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-264917469979422112138173/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (69/256:ℝ) (139/512:ℝ)-(139/512:ℝ)*thetaPowerMass 6 (69/256:ℝ) (139/512:ℝ)) ≤
      thetaFirstModeFirst (139/512:ℝ)*(thetaPowerMass 7 (69/256:ℝ) (139/512:ℝ)-(139/512:ℝ)*thetaPowerMass 6 (69/256:ℝ) (139/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0212.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (69/256:ℝ) (139/512:ℝ)
    (139/512:ℝ) (102740490249/10000000000000:ℝ) (-264917469979422112138173/2500000000000000000000000:ℝ) (217685023200282580708467/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_138
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0415).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_138 :
    (∫ x in (69/256:ℝ)..(139/512:ℝ), x^6*thetaFirstMode x) ≤ (7941889387553333/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (69/256:ℝ) (139/512:ℝ)
    (65516879131/6250000000000:ℝ) (1027406670771/100000000000000:ℝ) (217685023200282580708467/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_138 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0415).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_139 :
    (1015852139170021/125000000000000000000000:ℝ) ≤ ∫ x in (139/512:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-662091194259221679603307025511/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (139/512:ℝ) (35/128:ℝ)-(3407025864107161791/12547889060924853760:ℝ)*thetaPowerMass 6 (139/512:ℝ) (35/128:ℝ)) ≤
      thetaFirstModeFirst (3407025864107161791/12547889060924853760:ℝ)*(thetaPowerMass 7 (139/512:ℝ) (35/128:ℝ)-(3407025864107161791/12547889060924853760:ℝ)*thetaPowerMass 6 (139/512:ℝ) (35/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0213.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (139/512:ℝ) (35/128:ℝ)
    (3407025864107161791/12547889060924853760:ℝ) (513504005171/50000000000000:ℝ) (-662091194259221679603307025511/6250000000000000000000000000000:ℝ) (861296172253319353622509/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_139
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0419).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_139 :
    (∫ x in (139/512:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x) ≤ (8126835827049949/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (139/512:ℝ) (35/128:ℝ)
    (1027406670771/100000000000000:ℝ) (251718859441/25000000000000:ℝ) (861296172253319353622509/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_139 (thetaFirstMode_refined_node_0415).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_140 :
    (2078205381985811/250000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(141/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-641265824862226378281017/6250000000000000000000000:ℝ)*(thetaPowerMass 7 (35/128:ℝ) (141/512:ℝ)-(141/512:ℝ)*thetaPowerMass 6 (35/128:ℝ) (141/512:ℝ)) ≤
      thetaFirstModeFirst (141/512:ℝ)*(thetaPowerMass 7 (35/128:ℝ) (141/512:ℝ)-(141/512:ℝ)*thetaPowerMass 6 (35/128:ℝ) (141/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0215.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (35/128:ℝ) (141/512:ℝ)
    (141/512:ℝ) (246667763263/25000000000000:ℝ) (-641265824862226378281017/6250000000000000000000000:ℝ) (851877492518435817071201/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_140
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0421).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_140 :
    (∫ x in (35/128:ℝ)..(141/512:ℝ), x^6*thetaFirstMode x) ≤ (1662567685130441/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (35/128:ℝ) (141/512:ℝ)
    (251718859441/25000000000000:ℝ) (7708380973/781250000000:ℝ) (851877492518435817071201/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_140 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0421).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_141 :
    (849978883111127/100000000000000000000000:ℝ) ≤ ∫ x in (141/512:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-320535276306616594541771228153/3125000000000000000000000000000:ℝ)*(thetaPowerMass 7 (141/512:ℝ) (71/256:ℝ)-(3874419549088930809/14066927919229519360:ℝ)*thetaPowerMass 6 (141/512:ℝ) (71/256:ℝ)) ≤
      thetaFirstModeFirst (3874419549088930809/14066927919229519360:ℝ)*(thetaPowerMass 7 (141/512:ℝ) (71/256:ℝ)-(3874419549088930809/14066927919229519360:ℝ)*thetaPowerMass 6 (141/512:ℝ) (71/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0216.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (141/512:ℝ) (71/256:ℝ)
    (3874419549088930809/14066927919229519360:ℝ) (986292210119/100000000000000:ℝ) (-320535276306616594541771228153/3125000000000000000000000000000:ℝ) (842485245662307302529057/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_141
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0425).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_141 :
    (∫ x in (141/512:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x) ≤ (4249904347261253/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (141/512:ℝ) (71/256:ℝ)
    (7708380973/781250000000:ℝ) (966795058203/100000000000000:ℝ) (842485245662307302529057/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_141 (thetaFirstMode_refined_node_0421).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_142 :
    (8687638608134829/1000000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(143/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2482788865938089219118733/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (71/256:ℝ) (143/512:ℝ)-(143/512:ℝ)*thetaPowerMass 6 (71/256:ℝ) (143/512:ℝ)) ≤
      thetaFirstModeFirst (143/512:ℝ)*(thetaPowerMass 7 (71/256:ℝ) (143/512:ℝ)-(143/512:ℝ)*thetaPowerMass 6 (71/256:ℝ) (143/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0218.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (71/256:ℝ) (143/512:ℝ)
    (143/512:ℝ) (473618539969/50000000000000:ℝ) (-2482788865938089219118733/25000000000000000000000000:ℝ) (208280152422305870594033/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_142
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0427).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_142 :
    (∫ x in (71/256:ℝ)..(143/512:ℝ), x^6*thetaFirstMode x) ≤ (8687656478145933/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (71/256:ℝ) (143/512:ℝ)
    (966795058203/100000000000000:ℝ) (189447747183/20000000000000:ℝ) (208280152422305870594033/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_142 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0427).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_143 :
    (2219067244522251/250000000000000000000000:ℝ) ≤ ∫ x in (143/512:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4964071412775898871754220633283/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (143/512:ℝ) (9/32:ℝ)-(4397964224531456007/15744504565196700160:ℝ)*thetaPowerMass 6 (143/512:ℝ) (9/32:ℝ)) ≤
      thetaFirstModeFirst (4397964224531456007/15744504565196700160:ℝ)*(thetaPowerMass 7 (143/512:ℝ) (9/32:ℝ)-(4397964224531456007/15744504565196700160:ℝ)*thetaPowerMass 6 (143/512:ℝ) (9/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0219.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (143/512:ℝ) (9/32:ℝ)
    (4397964224531456007/15744504565196700160:ℝ) (946875514151/100000000000000:ℝ) (-4964071412775898871754220633283/50000000000000000000000000000000:ℝ) (102973093536103918447049/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_143
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0431).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_143 :
    (∫ x in (143/512:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x) ≤ (8876290031466793/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (143/512:ℝ) (9/32:ℝ)
    (189447747183/20000000000000:ℝ) (928000225389/100000000000000:ℝ) (102973093536103918447049/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_143 (thetaFirstMode_refined_node_0427).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_144 :
    (9065597228211327/1000000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(145/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-75073144252494485009719/781250000000000000000000:ℝ)*(thetaPowerMass 7 (9/32:ℝ) (145/512:ℝ)-(145/512:ℝ)*thetaPowerMass 6 (9/32:ℝ) (145/512:ℝ)) ≤
      thetaFirstModeFirst (145/512:ℝ)*(thetaPowerMass 7 (9/32:ℝ) (145/512:ℝ)-(145/512:ℝ)*thetaPowerMass 6 (9/32:ℝ) (145/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0221.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (9/32:ℝ) (145/512:ℝ)
    (145/512:ℝ) (14204286931/1562500000000:ℝ) (-75073144252494485009719/781250000000000000000000:ℝ) (20361970264686498177509/25000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_144
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0433).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_144 :
    (∫ x in (9/32:ℝ)..(145/512:ℝ), x^6*thetaFirstMode x) ≤ (453280804950799/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/32:ℝ) (145/512:ℝ)
    (928000225389/100000000000000:ℝ) (909075965309/100000000000000:ℝ) (20361970264686498177509/25000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_144 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0433).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_145 :
    (11569397140983/1250000000000000000000:ℝ) ≤ ∫ x in (145/512:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-600403627685138544767187612993/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (145/512:ℝ) (73/256:ℝ)-(996695256742326405/3518919113747927552:ℝ)*thetaPowerMass 6 (145/512:ℝ) (73/256:ℝ)) ≤
      thetaFirstModeFirst (996695256742326405/3518919113747927552:ℝ)*(thetaPowerMass 7 (145/512:ℝ) (73/256:ℝ)-(996695256742326405/3518919113747927552:ℝ)*thetaPowerMass 6 (145/512:ℝ) (73/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0222.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (145/512:ℝ) (73/256:ℝ)
    (996695256742326405/3518919113747927552:ℝ) (181745867269/20000000000000:ℝ) (-600403627685138544767187612993/6250000000000000000000000000000:ℝ) (80520393091388882743507/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_145
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0437).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_145 :
    (∫ x in (145/512:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x) ≤ (9255539995941621/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (145/512:ℝ) (73/256:ℝ)
    (909075965309/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (80520393091388882743507/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_145 (thetaFirstMode_refined_node_0433).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_146 :
    (4722972895795817/500000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(147/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4647413726650552416003963/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (73/256:ℝ) (147/512:ℝ)-(147/512:ℝ)*thetaPowerMass 6 (73/256:ℝ) (147/512:ℝ)) ≤
      thetaFirstModeFirst (147/512:ℝ)*(thetaPowerMass 7 (73/256:ℝ) (147/512:ℝ)-(147/512:ℝ)*thetaPowerMass 6 (73/256:ℝ) (147/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0224.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (73/256:ℝ) (147/512:ℝ)
    (147/512:ℝ) (872154459999/100000000000000:ℝ) (-4647413726650552416003963/50000000000000000000000000:ℝ) (99495153570601387524011/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_146
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0439).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_146 :
    (∫ x in (73/256:ℝ)..(147/512:ℝ), x^6*thetaFirstMode x) ≤ (9445965690906209/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (73/256:ℝ) (147/512:ℝ)
    (222615601443/25000000000000:ℝ) (436078004363/50000000000000:ℝ) (99495153570601387524011/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_146 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0439).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_147 :
    (1927354467698359/200000000000000000000000:ℝ) ≤ ∫ x in (147/512:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-929202785872532394523319159819/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (147/512:ℝ) (37/128:ℝ)-(5637281108870877543/19632189611037468160:ℝ)*thetaPowerMass 6 (147/512:ℝ) (37/128:ℝ)) ≤
      thetaFirstModeFirst (5637281108870877543/19632189611037468160:ℝ)*(thetaPowerMass 7 (147/512:ℝ) (37/128:ℝ)-(5637281108870877543/19632189611037468160:ℝ)*thetaPowerMass 6 (147/512:ℝ) (37/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0225.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (147/512:ℝ) (37/128:ℝ)
    (5637281108870877543/19632189611037468160:ℝ) (871825264493/100000000000000:ℝ) (-929202785872532394523319159819/10000000000000000000000000000000:ℝ) (393375903785310745672377/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_147
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0443).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_147 :
    (∫ x in (147/512:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x) ≤ (602299743166273/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (147/512:ℝ) (37/128:ℝ)
    (436078004363/50000000000000:ℝ) (213538312097/25000000000000:ℝ) (393375903785310745672377/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_147 (thetaFirstMode_refined_node_0439).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_148 :
    (9827911171588793/1000000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(149/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2246875040877545106741331/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (37/128:ℝ) (149/512:ℝ)-(149/512:ℝ)*thetaPowerMass 6 (37/128:ℝ) (149/512:ℝ)) ≤
      thetaFirstModeFirst (149/512:ℝ)*(thetaPowerMass 7 (37/128:ℝ) (149/512:ℝ)-(149/512:ℝ)*thetaPowerMass 6 (37/128:ℝ) (149/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0227.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (37/128:ℝ) (149/512:ℝ)
    (149/512:ℝ) (418224557351/50000000000000:ℝ) (-2246875040877545106741331/25000000000000000000000000:ℝ) (194394189120748864607043/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_148
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0445).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_148 :
    (∫ x in (37/128:ℝ)..(149/512:ℝ), x^6*thetaFirstMode x) ≤ (4913966063126669/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (37/128:ℝ) (149/512:ℝ)
    (213538312097/25000000000000:ℝ) (33458024467/4000000000000:ℝ) (194394189120748864607043/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_148 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0445).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_149 :
    (400769999240583/40000000000000000000000:ℝ) ≤ ∫ x in (149/512:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1123100263923040084569625314417/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (149/512:ℝ) (75/256:ℝ)-(6366249662322494241/21873345290796674560:ℝ)*thetaPowerMass 6 (149/512:ℝ) (75/256:ℝ)) ≤
      thetaFirstModeFirst (6366249662322494241/21873345290796674560:ℝ)*(thetaPowerMass 7 (149/512:ℝ) (75/256:ℝ)-(6366249662322494241/21873345290796674560:ℝ)*thetaPowerMass 6 (149/512:ℝ) (75/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0228.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (149/512:ℝ) (75/256:ℝ)
    (6366249662322494241/21873345290796674560:ℝ) (104516884289/12500000000000:ℝ) (-1123100263923040084569625314417/12500000000000000000000000000000:ℝ) (192109287038277537851283/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_149
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0449).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_149 :
    (∫ x in (149/512:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x) ≤ (20038549681521/2000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (149/512:ℝ) (75/256:ℝ)
    (33458024467/4000000000000:ℝ) (204761149653/25000000000000:ℝ) (192109287038277537851283/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_149 (thetaFirstMode_refined_node_0445).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_150 :
    (10210701442493383/1000000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(151/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2171831725535485339960533/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (75/256:ℝ) (151/512:ℝ)-(151/512:ℝ)*thetaPowerMass 6 (75/256:ℝ) (151/512:ℝ)) ≤
      thetaFirstModeFirst (151/512:ℝ)*(thetaPowerMass 7 (75/256:ℝ) (151/512:ℝ)-(151/512:ℝ)*thetaPowerMass 6 (75/256:ℝ) (151/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0230.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (75/256:ℝ) (151/512:ℝ)
    (151/512:ℝ) (801930276291/100000000000000:ℝ) (-2171831725535485339960533/25000000000000000000000000:ℝ) (759334039519671048511609/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_150
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0451).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_150 :
    (∫ x in (75/256:ℝ)..(151/512:ℝ), x^6*thetaFirstMode x) ≤ (638170217397269/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (75/256:ℝ) (151/512:ℝ)
    (204761149653/25000000000000:ℝ) (400965861371/50000000000000:ℝ) (759334039519671048511609/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_150 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0451).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_151 :
    (5201075184872399/500000000000000000000000:ℝ) ≤ ∫ x in (151/512:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-217118180229069638499437562101/2500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (151/512:ℝ) (19/64:ℝ)-(7177837152534081759/24335251372240130560:ℝ)*thetaPowerMass 6 (151/512:ℝ) (19/64:ℝ)) ≤
      thetaFirstModeFirst (7177837152534081759/24335251372240130560:ℝ)*(thetaPowerMass 7 (151/512:ℝ) (19/64:ℝ)-(7177837152534081759/24335251372240130560:ℝ)*thetaPowerMass 6 (151/512:ℝ) (19/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0231.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (151/512:ℝ) (19/64:ℝ)
    (7177837152534081759/24335251372240130560:ℝ) (801630743121/100000000000000:ℝ) (-217118180229069638499437562101/2500000000000000000000000000000:ℝ) (375134235707624221016263/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_151
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0455).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_151 :
    (∫ x in (151/512:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x) ≤ (650136035923987/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (151/512:ℝ) (19/64:ℝ)
    (400965861371/50000000000000:ℝ) (39255425577/5000000000000:ℝ) (375134235707624221016263/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_151 (thetaFirstMode_refined_node_0451).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_152 :
    (5296754353526897/500000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(153/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-52464066555620330768949/625000000000000000000000:ℝ)*(thetaPowerMass 7 (19/64:ℝ) (153/512:ℝ)-(153/512:ℝ)*thetaPowerMass 6 (19/64:ℝ) (153/512:ℝ)) ≤
      thetaFirstModeFirst (153/512:ℝ)*(thetaPowerMass 7 (19/64:ℝ) (153/512:ℝ)-(153/512:ℝ)*thetaPowerMass 6 (19/64:ℝ) (153/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0233.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (19/64:ℝ) (153/512:ℝ)
    (153/512:ℝ) (768570109637/100000000000000:ℝ) (-52464066555620330768949/625000000000000000000000:ℝ) (370620734176972153163053/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_152
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0457).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_152 :
    (∫ x in (19/64:ℝ)..(153/512:ℝ), x^6*thetaFirstMode x) ≤ (5296765924437287/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/64:ℝ) (153/512:ℝ)
    (39255425577/5000000000000:ℝ) (76857150679/10000000000000:ℝ) (370620734176972153163053/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_152 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0457).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_153 :
    (5392329353965717/500000000000000000000000:ℝ) ≤ ∫ x in (153/512:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1048968278535039437045883926147/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (153/512:ℝ) (77/256:ℝ)-(8080123862216333457/27036289542638748160:ℝ)*thetaPowerMass 6 (153/512:ℝ) (77/256:ℝ)) ≤
      thetaFirstModeFirst (8080123862216333457/27036289542638748160:ℝ)*(thetaPowerMass 7 (153/512:ℝ) (77/256:ℝ)-(8080123862216333457/27036289542638748160:ℝ)*thetaPowerMass 6 (153/512:ℝ) (77/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0234.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (153/512:ℝ) (77/256:ℝ)
    (8080123862216333457/27036289542638748160:ℝ) (192071115779/25000000000000:ℝ) (-1048968278535039437045883926147/12500000000000000000000000000000:ℝ) (732254038351135320149277/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_153
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0461).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_153 :
    (∫ x in (153/512:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x) ≤ (10784686295151723/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (153/512:ℝ) (77/256:ℝ)
    (76857150679/10000000000000:ℝ) (752317264991/100000000000000:ℝ) (732254038351135320149277/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_153 (thetaFirstMode_refined_node_0457).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_154 :
    (274387800154313/25000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(155/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2027052789150508143840639/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (77/256:ℝ) (155/512:ℝ)-(155/512:ℝ)*thetaPowerMass 6 (77/256:ℝ) (155/512:ℝ)) ≤
      thetaFirstModeFirst (155/512:ℝ)*(thetaPowerMass 7 (77/256:ℝ) (155/512:ℝ)-(155/512:ℝ)*thetaPowerMass 6 (77/256:ℝ) (155/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0236.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (77/256:ℝ) (155/512:ℝ)
    (155/512:ℝ) (736341008679/100000000000000:ℝ) (-2027052789150508143840639/25000000000000000000000000:ℝ) (361653586367971121122721/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_154
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0463).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_154 :
    (∫ x in (77/256:ℝ)..(155/512:ℝ), x^6*thetaFirstMode x) ≤ (10975536277515503/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (77/256:ℝ) (155/512:ℝ)
    (752317264991/100000000000000:ℝ) (736342357741/100000000000000:ℝ) (361653586367971121122721/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_154 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0463).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_155 :
    (5582974309193331/500000000000000000000000:ℝ) ≤ ∫ x in (155/512:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-101322487675637297705305099061/1250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (155/512:ℝ) (39/128:ℝ)-(1816371645569997795/5999219949625943552:ℝ)*thetaPowerMass 6 (155/512:ℝ) (39/128:ℝ)) ≤
      thetaFirstModeFirst (1816371645569997795/5999219949625943552:ℝ)*(thetaPowerMass 7 (155/512:ℝ) (39/128:ℝ)-(1816371645569997795/5999219949625943552:ℝ)*thetaPowerMass 6 (155/512:ℝ) (39/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0237.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (155/512:ℝ) (39/128:ℝ)
    (1816371645569997795/5999219949625943552:ℝ) (736068654267/100000000000000:ℝ) (-101322487675637297705305099061/1250000000000000000000000000000:ℝ) (357200922982804769686459/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_155
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0467).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_155 :
    (∫ x in (155/512:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x) ≤ (2233195524721973/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (155/512:ℝ) (39/128:ℝ)
    (736342357741/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (357200922982804769686459/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_155 (thetaFirstMode_refined_node_0463).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_156 :
    (88717814817749/7812500000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(157/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-195728626357322999278911/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (39/128:ℝ) (157/512:ℝ)-(157/512:ℝ)*thetaPowerMass 6 (39/128:ℝ) (157/512:ℝ)) ≤
      thetaFirstModeFirst (157/512:ℝ)*(thetaPowerMass 7 (39/128:ℝ) (157/512:ℝ)-(157/512:ℝ)*thetaPowerMass 6 (39/128:ℝ) (157/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0239.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (39/128:ℝ) (157/512:ℝ)
    (157/512:ℝ) (176303902207/25000000000000:ℝ) (-195728626357322999278911/2500000000000000000000000:ℝ) (705539015461980504919239/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_156
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0469).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_156 :
    (∫ x in (39/128:ℝ)..(157/512:ℝ), x^6*thetaFirstMode x) ≤ (567795285995841/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (39/128:ℝ) (157/512:ℝ)
    (720643372107/100000000000000:ℝ) (705216910999/100000000000000:ℝ) (705539015461980504919239/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_156 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0469).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_157 :
    (2886296287438883/250000000000000000000000:ℝ) ≤ ∫ x in (157/512:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-78268222841926281470126304231/1000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (157/512:ℝ) (79/256:ℝ)-(10192502262515829993/33235648177494300160:ℝ)*thetaPowerMass 6 (157/512:ℝ) (79/256:ℝ)) ≤
      thetaFirstModeFirst (10192502262515829993/33235648177494300160:ℝ)*(thetaPowerMass 7 (157/512:ℝ) (79/256:ℝ)-(10192502262515829993/33235648177494300160:ℝ)*thetaPowerMass 6 (157/512:ℝ) (79/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0240.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (157/512:ℝ) (79/256:ℝ)
    (10192502262515829993/33235648177494300160:ℝ) (704955976797/100000000000000:ℝ) (-78268222841926281470126304231/1000000000000000000000000000000:ℝ) (348359810723514749431253/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_157
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0473).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_157 :
    (∫ x in (157/512:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x) ≤ (1154521560759971/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (157/512:ℝ) (79/256:ℝ)
    (705216910999/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (348359810723514749431253/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_157 (thetaFirstMode_refined_node_0469).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_158 :
    (11733775482639543/1000000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(159/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-75569859527507411067417/1000000000000000000000000:ℝ)*(thetaPowerMass 7 (79/256:ℝ) (159/512:ℝ)-(159/512:ℝ)*thetaPowerMass 6 (79/256:ℝ) (159/512:ℝ)) ≤
      thetaFirstModeFirst (159/512:ℝ)*(thetaPowerMass 7 (79/256:ℝ) (159/512:ℝ)-(159/512:ℝ)*thetaPowerMass 6 (79/256:ℝ) (159/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0242.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (79/256:ℝ) (159/512:ℝ)
    (159/512:ℝ) (27006671959/4000000000000:ℝ) (-75569859527507411067417/1000000000000000000000000:ℝ) (171986146693352966422757/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_158
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0475).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_158 :
    (∫ x in (79/256:ℝ)..(159/512:ℝ), x^6*thetaFirstMode x) ≤ (5866901039350721/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (79/256:ℝ) (159/512:ℝ)
    (345029796773/50000000000000:ℝ) (675168055439/100000000000000:ℝ) (171986146693352966422757/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_158 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0475).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_159 :
    (2980381957218149/250000000000000000000000:ℝ) ≤ ∫ x in (159/512:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x := by
  have hd : (-188868743363900031565117752833/2500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (159/512:ℝ) (5/16:ℝ)-(11422279416358375191/36777297964497103360:ℝ)*thetaPowerMass 6 (159/512:ℝ) (5/16:ℝ)) ≤
      thetaFirstModeFirst (11422279416358375191/36777297964497103360:ℝ)*(thetaPowerMass 7 (159/512:ℝ) (5/16:ℝ)-(11422279416358375191/36777297964497103360:ℝ)*thetaPowerMass 6 (159/512:ℝ) (5/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0243.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (159/512:ℝ) (5/16:ℝ)
    (11422279416358375191/36777297964497103360:ℝ) (337459671627/50000000000000:ℝ) (-188868743363900031565117752833/2500000000000000000000000000000:ℝ) (339607408390625219458253/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_159
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0479).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_159 :
    (∫ x in (159/512:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x) ≤ (2980389943174889/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (159/512:ℝ) (5/16:ℝ)
    (675168055439/100000000000000:ℝ) (660538949293/100000000000000:ℝ) (339607408390625219458253/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_159 (thetaFirstMode_refined_node_0475).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
