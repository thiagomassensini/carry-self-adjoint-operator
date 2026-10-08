import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature04
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative06
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative07

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_128 :
    (6170632538955736179/250000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(129/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6290043168594789650918400158041/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/4:ℝ) (129/512:ℝ)-(1/4:ℝ)*thetaPowerMass 0 (1/4:ℝ) (129/512:ℝ)) ≤
      thetaFirstModeFirst (1/4:ℝ)*(thetaPowerMass 1 (1/4:ℝ) (129/512:ℝ)-(1/4:ℝ)*thetaPowerMass 0 (1/4:ℝ) (129/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0196.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/4:ℝ) (129/512:ℝ)
    (1/4:ℝ) (159496168639/12500000000000:ℝ) (-6290043168594789650918400158041/50000000000000000000000000000000:ℝ) (966295758513919120153063/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_128
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0384).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_128 :
    (∫ x in (1/4:ℝ)..(129/512:ℝ), x^0*thetaFirstMode x) ≤ (6170645823835946123/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/4:ℝ) (129/512:ℝ)
    (1275971452837/100000000000000:ℝ) (312896628009/25000000000000:ℝ) (966295758513919120153063/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_128 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0385).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_129 :
    (24209868877936219297/1000000000000000000000000:ℝ) ≤ ∫ x in (129/512:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-387078605595862628952036844953/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (129/512:ℝ) (65/256:ℝ)-(1740175468704392841/6905636680726120960:ℝ)*thetaPowerMass 0 (129/512:ℝ) (65/256:ℝ)) ≤
      thetaFirstModeFirst (1740175468704392841/6905636680726120960:ℝ)*(thetaPowerMass 1 (129/512:ℝ) (65/256:ℝ)-(1740175468704392841/6905636680726120960:ℝ)*thetaPowerMass 0 (129/512:ℝ) (65/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0198.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (129/512:ℝ) (65/256:ℝ)
    (1740175468704392841/6905636680726120960:ℝ) (312771103803/25000000000000:ℝ) (-387078605595862628952036844953/3125000000000000000000000000000:ℝ) (478333949264452833596727/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_129
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0389).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_129 :
    (∫ x in (129/512:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x) ≤ (12104960319873321173/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (129/512:ℝ) (65/256:ℝ)
    (312896628009/25000000000000:ℝ) (1227570184781/100000000000000:ℝ) (478333949264452833596727/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_129 (thetaFirstMode_refined_node_0385).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_130 :
    (23744369735069561549/1000000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(131/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6101312784872935521420468329769/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (65/256:ℝ) (131/512:ℝ)-(65/256:ℝ)*thetaPowerMass 0 (65/256:ℝ) (131/512:ℝ)) ≤
      thetaFirstModeFirst (65/256:ℝ)*(thetaPowerMass 1 (65/256:ℝ) (131/512:ℝ)-(65/256:ℝ)*thetaPowerMass 0 (65/256:ℝ) (131/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0199.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (65/256:ℝ) (131/512:ℝ)
    (65/256:ℝ) (1227568144983/100000000000000:ℝ) (-6101312784872935521420468329769/50000000000000000000000000000000:ℝ) (947052643874298212119509/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_130
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0390).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_130 :
    (∫ x in (65/256:ℝ)..(131/512:ℝ), x^0*thetaFirstMode x) ≤ (23744421593471518521/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (65/256:ℝ) (131/512:ℝ)
    (1227570184781/100000000000000:ℝ) (150489849797/12500000000000:ℝ) (947052643874298212119509/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_130 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0391).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_131 :
    (727686373961836431/31250000000000000000000:ℝ) ≤ ∫ x in (131/512:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-187702365522042567234998070069/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (131/512:ℝ) (33/128:ℝ)-(1998562918031146359/7809963970327836160:ℝ)*thetaPowerMass 0 (131/512:ℝ) (33/128:ℝ)) ≤
      thetaFirstModeFirst (1998562918031146359/7809963970327836160:ℝ)*(thetaPowerMass 1 (131/512:ℝ) (33/128:ℝ)-(1998562918031146359/7809963970327836160:ℝ)*thetaPowerMass 0 (131/512:ℝ) (33/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0201.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (131/512:ℝ) (33/128:ℝ)
    (1998562918031146359/7809963970327836160:ℝ) (601719622347/50000000000000:ℝ) (-187702365522042567234998070069/1562500000000000000000000000000:ℝ) (93745131236830700098271/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_131
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0395).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_131 :
    (∫ x in (131/512:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x) ≤ (1164300723513037533/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (131/512:ℝ) (33/128:ℝ)
    (150489849797/12500000000000:ℝ) (9223661601/781250000000:ℝ) (93745131236830700098271/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_131 (thetaFirstMode_refined_node_0391).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_132 :
    (22834577086243699837/1000000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(133/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11555353009681443998870998779/97656250000000000000000000000:ℝ)*(thetaPowerMass 1 (33/128:ℝ) (133/512:ℝ)-(33/128:ℝ)*thetaPowerMass 0 (33/128:ℝ) (133/512:ℝ)) ≤
      thetaFirstModeFirst (33/128:ℝ)*(thetaPowerMass 1 (33/128:ℝ) (133/512:ℝ)-(33/128:ℝ)*thetaPowerMass 0 (33/128:ℝ) (133/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0202.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (33/128:ℝ) (133/512:ℝ)
    (33/128:ℝ) (36894584617/3125000000000:ℝ) (-11555353009681443998870998779/97656250000000000000000000000:ℝ) (927865210544466697500661/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_132
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0396).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_132 :
    (∫ x in (33/128:ℝ)..(133/512:ℝ), x^0*thetaFirstMode x) ≤ (1141731384133125549/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/128:ℝ) (133/512:ℝ)
    (9223661601/781250000000:ℝ) (578848090929/50000000000000:ℝ) (927865210544466697500661/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_132 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0397).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_133 :
    (22390140487596130641/1000000000000000000000000:ℝ) ≤ ∫ x in (133/512:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5823444710741132072874374521599/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (133/512:ℝ) (67/256:ℝ)-(2290508312768691057/8816267219187228160:ℝ)*thetaPowerMass 0 (133/512:ℝ) (67/256:ℝ)) ≤
      thetaFirstModeFirst (2290508312768691057/8816267219187228160:ℝ)*(thetaPowerMass 1 (133/512:ℝ) (67/256:ℝ)-(2290508312768691057/8816267219187228160:ℝ)*thetaPowerMass 0 (133/512:ℝ) (67/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0204.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (133/512:ℝ) (67/256:ℝ)
    (2290508312768691057/8816267219187228160:ℝ) (578619100303/50000000000000:ℝ) (-5823444710741132072874374521599/50000000000000000000000000000000:ℝ) (918295633360136582510243/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_133
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0401).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_133 :
    (∫ x in (133/512:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x) ≤ (11195094875937368629/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (133/512:ℝ) (67/256:ℝ)
    (578848090929/50000000000000:ℝ) (567558816199/50000000000000:ℝ) (918295633360136582510243/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_133 (thetaFirstMode_refined_node_0397).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_134 :
    (10976289981882873857/500000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(135/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2867558081554541786663992677321/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (67/256:ℝ) (135/512:ℝ)-(67/256:ℝ)*thetaPowerMass 0 (67/256:ℝ) (135/512:ℝ)) ≤
      thetaFirstModeFirst (67/256:ℝ)*(thetaPowerMass 1 (67/256:ℝ) (135/512:ℝ)-(67/256:ℝ)*thetaPowerMass 0 (67/256:ℝ) (135/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0205.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (67/256:ℝ) (135/512:ℝ)
    (67/256:ℝ) (567557858261/50000000000000:ℝ) (-2867558081554541786663992677321/25000000000000000000000000000000:ℝ) (454371931943431231700863/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_134
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0402).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_134 :
    (∫ x in (67/256:ℝ)..(135/512:ℝ), x^0*thetaFirstMode x) ≤ (4390525863472893141/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (67/256:ℝ) (135/512:ℝ)
    (567558816199/50000000000000:ℝ) (1112889386079/100000000000000:ℝ) (454371931943431231700863/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_134 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0403).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_135 :
    (4304365420464458063/200000000000000000000000:ℝ) ≤ ∫ x in (135/512:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1411038228199264502842671683349/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (135/512:ℝ) (17/64:ℝ)-(523953028089808515/1986849740868925952:ℝ)*thetaPowerMass 0 (135/512:ℝ) (17/64:ℝ)) ≤
      thetaFirstModeFirst (523953028089808515/1986849740868925952:ℝ)*(thetaPowerMass 1 (135/512:ℝ) (17/64:ℝ)-(523953028089808515/1986849740868925952:ℝ)*thetaPowerMass 0 (135/512:ℝ) (17/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0207.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (135/512:ℝ) (17/64:ℝ)
    (523953028089808515/1986849740868925952:ℝ) (222490410103/20000000000000:ℝ) (-1411038228199264502842671683349/12500000000000000000000000000000:ℝ) (179842234606979033115729/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_135
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0407).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_135 :
    (∫ x in (135/512:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x) ≤ (1345117196654836063/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (135/512:ℝ) (17/64:ℝ)
    (1112889386079/100000000000000:ℝ) (1091007799227/100000000000000:ℝ) (179842234606979033115729/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_135 (thetaFirstMode_refined_node_0403).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_136 :
    (21097808014069376237/1000000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(137/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5557626145381755970245768281739/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (17/64:ℝ) (137/512:ℝ)-(17/64:ℝ)*thetaPowerMass 0 (17/64:ℝ) (137/512:ℝ)) ≤
      thetaFirstModeFirst (17/64:ℝ)*(thetaPowerMass 1 (17/64:ℝ) (137/512:ℝ)-(17/64:ℝ)*thetaPowerMass 0 (17/64:ℝ) (137/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0208.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (17/64:ℝ) (137/512:ℝ)
    (17/64:ℝ) (545502971679/50000000000000:ℝ) (-5557626145381755970245768281739/50000000000000000000000000000000:ℝ) (889698819256701636650141/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_136
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0408).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_136 :
    (∫ x in (17/64:ℝ)..(137/512:ℝ), x^0*thetaFirstMode x) ≤ (4219571228797752333/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/64:ℝ) (137/512:ℝ)
    (1091007799227/100000000000000:ℝ) (213893847089/20000000000000:ℝ) (889698819256701636650141/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_136 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0409).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_137 :
    (827218180733045717/40000000000000000000000:ℝ) ≤ ∫ x in (137/512:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-683573308254643201407023355147/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (137/512:ℝ) (69/256:ℝ)-(2990441164477942593/11174368100215452160:ℝ)*thetaPowerMass 0 (137/512:ℝ) (69/256:ℝ)) ≤
      thetaFirstModeFirst (2990441164477942593/11174368100215452160:ℝ)*(thetaPowerMass 1 (137/512:ℝ) (69/256:ℝ)-(2990441164477942593/11174368100215452160:ℝ)*thetaPowerMass 0 (137/512:ℝ) (69/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0210.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (137/512:ℝ) (69/256:ℝ)
    (2990441164477942593/11174368100215452160:ℝ) (534525830191/50000000000000:ℝ) (-683573308254643201407023355147/6250000000000000000000000000000:ℝ) (880208048276601117164071/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_137
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0413).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_137 :
    (∫ x in (137/512:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x) ≤ (5170125340381878993/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (137/512:ℝ) (69/256:ℝ)
    (213893847089/20000000000000:ℝ) (65516879131/6250000000000:ℝ) (880208048276601117164071/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_137 (thetaFirstMode_refined_node_0409).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_138 :
    (20269693081460347841/1000000000000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(139/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-336490986669274645970258816143/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (69/256:ℝ) (139/512:ℝ)-(69/256:ℝ)*thetaPowerMass 0 (69/256:ℝ) (139/512:ℝ)) ≤
      thetaFirstModeFirst (69/256:ℝ)*(thetaPowerMass 1 (69/256:ℝ) (139/512:ℝ)-(69/256:ℝ)*thetaPowerMass 0 (69/256:ℝ) (139/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0211.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (69/256:ℝ) (139/512:ℝ)
    (69/256:ℝ) (52413413447/5000000000000:ℝ) (-336490986669274645970258816143/3125000000000000000000000000000:ℝ) (217685023200282580708467/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_138
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0414).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_138 :
    (∫ x in (69/256:ℝ)..(139/512:ℝ), x^0*thetaFirstMode x) ≤ (20269740006863431229/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (69/256:ℝ) (139/512:ℝ)
    (65516879131/6250000000000:ℝ) (1027406670771/100000000000000:ℝ) (217685023200282580708467/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_138 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0415).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_139 :
    (9932727895910740533/500000000000000000000000:ℝ) ≤ ∫ x in (139/512:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-662091194259221679603307025511/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (139/512:ℝ) (35/128:ℝ)-(3407025864107161791/12547889060924853760:ℝ)*thetaPowerMass 0 (139/512:ℝ) (35/128:ℝ)) ≤
      thetaFirstModeFirst (3407025864107161791/12547889060924853760:ℝ)*(thetaPowerMass 1 (139/512:ℝ) (35/128:ℝ)-(3407025864107161791/12547889060924853760:ℝ)*thetaPowerMass 0 (139/512:ℝ) (35/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0213.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (139/512:ℝ) (35/128:ℝ)
    (3407025864107161791/12547889060924853760:ℝ) (513504005171/50000000000000:ℝ) (-662091194259221679603307025511/6250000000000000000000000000000:ℝ) (861296172253319353622509/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_139
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0419).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_139 :
    (∫ x in (139/512:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x) ≤ (19865501453116343097/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (139/512:ℝ) (35/128:ℝ)
    (1027406670771/100000000000000:ℝ) (251718859441/25000000000000:ℝ) (861296172253319353622509/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_139 (thetaFirstMode_refined_node_0415).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_140 :
    (19467669508047524181/1000000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(141/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-81465441090581769886994481929/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (35/128:ℝ) (141/512:ℝ)-(35/128:ℝ)*thetaPowerMass 0 (35/128:ℝ) (141/512:ℝ)) ≤
      thetaFirstModeFirst (35/128:ℝ)*(thetaPowerMass 1 (35/128:ℝ) (141/512:ℝ)-(35/128:ℝ)*thetaPowerMass 0 (35/128:ℝ) (141/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0214.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (35/128:ℝ) (141/512:ℝ)
    (35/128:ℝ) (251718424509/25000000000000:ℝ) (-81465441090581769886994481929/781250000000000000000000000000:ℝ) (851877492518435817071201/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_140
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0420).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_140 :
    (∫ x in (35/128:ℝ)..(141/512:ℝ), x^0*thetaFirstMode x) ≤ (3893543049600867267/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/128:ℝ) (141/512:ℝ)
    (251718859441/25000000000000:ℝ) (7708380973/781250000000:ℝ) (851877492518435817071201/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_140 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0421).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_141 :
    (19076266624375174093/1000000000000000000000000:ℝ) ≤ ∫ x in (141/512:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-320535276306616594541771228153/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (141/512:ℝ) (71/256:ℝ)-(3874419549088930809/14066927919229519360:ℝ)*thetaPowerMass 0 (141/512:ℝ) (71/256:ℝ)) ≤
      thetaFirstModeFirst (3874419549088930809/14066927919229519360:ℝ)*(thetaPowerMass 1 (141/512:ℝ) (71/256:ℝ)-(3874419549088930809/14066927919229519360:ℝ)*thetaPowerMass 0 (141/512:ℝ) (71/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0216.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (141/512:ℝ) (71/256:ℝ)
    (3874419549088930809/14066927919229519360:ℝ) (986292210119/100000000000000:ℝ) (-320535276306616594541771228153/3125000000000000000000000000000:ℝ) (842485245662307302529057/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_141
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0425).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_141 :
    (∫ x in (141/512:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x) ≤ (19076311122828294693/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (141/512:ℝ) (71/256:ℝ)
    (7708380973/781250000000:ℝ) (966795058203/100000000000000:ℝ) (842485245662307302529057/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_141 (thetaFirstMode_refined_node_0421).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_142 :
    (18691174427746430749/1000000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(143/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-315462793863830427786706968441/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (71/256:ℝ) (143/512:ℝ)-(71/256:ℝ)*thetaPowerMass 0 (71/256:ℝ) (143/512:ℝ)) ≤
      thetaFirstModeFirst (71/256:ℝ)*(thetaPowerMass 1 (71/256:ℝ) (143/512:ℝ)-(71/256:ℝ)*thetaPowerMass 0 (71/256:ℝ) (143/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0217.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (71/256:ℝ) (143/512:ℝ)
    (71/256:ℝ) (966793374627/100000000000000:ℝ) (-315462793863830427786706968441/3125000000000000000000000000000:ℝ) (208280152422305870594033/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_142
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0426).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_142 :
    (∫ x in (71/256:ℝ)..(143/512:ℝ), x^0*thetaFirstMode x) ≤ (9345609500664736547/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (71/256:ℝ) (143/512:ℝ)
    (966795058203/100000000000000:ℝ) (189447747183/20000000000000:ℝ) (208280152422305870594033/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_142 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0427).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_143 :
    (114452035337095009/6250000000000000000000:ℝ) ≤ ∫ x in (143/512:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4964071412775898871754220633283/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (143/512:ℝ) (9/32:ℝ)-(4397964224531456007/15744504565196700160:ℝ)*thetaPowerMass 0 (143/512:ℝ) (9/32:ℝ)) ≤
      thetaFirstModeFirst (4397964224531456007/15744504565196700160:ℝ)*(thetaPowerMass 1 (143/512:ℝ) (9/32:ℝ)-(4397964224531456007/15744504565196700160:ℝ)*thetaPowerMass 0 (143/512:ℝ) (9/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0219.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (143/512:ℝ) (9/32:ℝ)
    (4397964224531456007/15744504565196700160:ℝ) (946875514151/100000000000000:ℝ) (-4964071412775898871754220633283/50000000000000000000000000000000:ℝ) (102973093536103918447049/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_143
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0431).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_143 :
    (∫ x in (143/512:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x) ≤ (4578092252148976197/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (143/512:ℝ) (9/32:ℝ)
    (189447747183/20000000000000:ℝ) (928000225389/100000000000000:ℝ) (102973093536103918447049/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_143 (thetaFirstMode_refined_node_0427).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_144 :
    (17939648053503545333/1000000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(145/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4884684556704138430807991106597/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (9/32:ℝ) (145/512:ℝ)-(9/32:ℝ)*thetaPowerMass 0 (9/32:ℝ) (145/512:ℝ)) ≤
      thetaFirstModeFirst (9/32:ℝ)*(thetaPowerMass 1 (9/32:ℝ) (145/512:ℝ)-(9/32:ℝ)*thetaPowerMass 0 (9/32:ℝ) (145/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0220.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (9/32:ℝ) (145/512:ℝ)
    (9/32:ℝ) (115999824587/12500000000000:ℝ) (-4884684556704138430807991106597/50000000000000000000000000000000:ℝ) (20361970264686498177509/25000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_144
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0432).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_144 :
    (∫ x in (9/32:ℝ)..(145/512:ℝ), x^0*thetaFirstMode x) ≤ (17939691479783258873/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/32:ℝ) (145/512:ℝ)
    (928000225389/100000000000000:ℝ) (909075965309/100000000000000:ℝ) (20361970264686498177509/25000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_144 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0433).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_145 :
    (17573074738808407383/1000000000000000000000000:ℝ) ≤ ∫ x in (145/512:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-600403627685138544767187612993/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (145/512:ℝ) (73/256:ℝ)-(996695256742326405/3518919113747927552:ℝ)*thetaPowerMass 0 (145/512:ℝ) (73/256:ℝ)) ≤
      thetaFirstModeFirst (996695256742326405/3518919113747927552:ℝ)*(thetaPowerMass 1 (145/512:ℝ) (73/256:ℝ)-(996695256742326405/3518919113747927552:ℝ)*thetaPowerMass 0 (145/512:ℝ) (73/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0222.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (145/512:ℝ) (73/256:ℝ)
    (996695256742326405/3518919113747927552:ℝ) (181745867269/20000000000000:ℝ) (-600403627685138544767187612993/6250000000000000000000000000000:ℝ) (80520393091388882743507/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_145
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0437).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_145 :
    (∫ x in (145/512:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x) ≤ (8786558484344602237/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (145/512:ℝ) (73/256:ℝ)
    (909075965309/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (80520393091388882743507/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_145 (thetaFirstMode_refined_node_0433).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_146 :
    (17212533958304516347/1000000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(147/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-590700664886053846604941614681/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (73/256:ℝ) (147/512:ℝ)-(73/256:ℝ)*thetaPowerMass 0 (73/256:ℝ) (147/512:ℝ)) ≤
      thetaFirstModeFirst (73/256:ℝ)*(thetaPowerMass 1 (73/256:ℝ) (147/512:ℝ)-(73/256:ℝ)*thetaPowerMass 0 (73/256:ℝ) (147/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0223.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (73/256:ℝ) (147/512:ℝ)
    (73/256:ℝ) (445230415351/50000000000000:ℝ) (-590700664886053846604941614681/6250000000000000000000000000000:ℝ) (99495153570601387524011/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_146
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0438).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_146 :
    (∫ x in (73/256:ℝ)..(147/512:ℝ), x^0*thetaFirstMode x) ≤ (2151572032038530483/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (73/256:ℝ) (147/512:ℝ)
    (222615601443/25000000000000:ℝ) (436078004363/50000000000000:ℝ) (99495153570601387524011/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_146 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0439).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_147 :
    (210724490439540319/12500000000000000000000:ℝ) ≤ ∫ x in (147/512:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-929202785872532394523319159819/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (147/512:ℝ) (37/128:ℝ)-(5637281108870877543/19632189611037468160:ℝ)*thetaPowerMass 0 (147/512:ℝ) (37/128:ℝ)) ≤
      thetaFirstModeFirst (5637281108870877543/19632189611037468160:ℝ)*(thetaPowerMass 1 (147/512:ℝ) (37/128:ℝ)-(5637281108870877543/19632189611037468160:ℝ)*thetaPowerMass 0 (147/512:ℝ) (37/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0225.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (147/512:ℝ) (37/128:ℝ)
    (5637281108870877543/19632189611037468160:ℝ) (871825264493/100000000000000:ℝ) (-929202785872532394523319159819/10000000000000000000000000000000:ℝ) (393375903785310745672377/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_147
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0443).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_147 :
    (∫ x in (147/512:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x) ≤ (8429000179595616441/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (147/512:ℝ) (37/128:ℝ)
    (436078004363/50000000000000:ℝ) (213538312097/25000000000000:ℝ) (393375903785310745672377/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_147 (thetaFirstMode_refined_node_0439).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_148 :
    (16509279349074497331/1000000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(149/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-285633920613287166523597449323/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (37/128:ℝ) (149/512:ℝ)-(37/128:ℝ)*thetaPowerMass 0 (37/128:ℝ) (149/512:ℝ)) ≤
      thetaFirstModeFirst (37/128:ℝ)*(thetaPowerMass 1 (37/128:ℝ) (149/512:ℝ)-(37/128:ℝ)*thetaPowerMass 0 (37/128:ℝ) (149/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0226.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (37/128:ℝ) (149/512:ℝ)
    (37/128:ℝ) (854151725693/100000000000000:ℝ) (-285633920613287166523597449323/3125000000000000000000000000000:ℝ) (194394189120748864607043/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_148
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0444).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_148 :
    (∫ x in (37/128:ℝ)..(149/512:ℝ), x^0*thetaFirstMode x) ≤ (3301864107547305689/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/128:ℝ) (149/512:ℝ)
    (213538312097/25000000000000:ℝ) (33458024467/4000000000000:ℝ) (194394189120748864607043/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_148 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0445).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_149 :
    (2020803533415672293/125000000000000000000000:ℝ) ≤ ∫ x in (149/512:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1123100263923040084569625314417/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (149/512:ℝ) (75/256:ℝ)-(6366249662322494241/21873345290796674560:ℝ)*thetaPowerMass 0 (149/512:ℝ) (75/256:ℝ)) ≤
      thetaFirstModeFirst (6366249662322494241/21873345290796674560:ℝ)*(thetaPowerMass 1 (149/512:ℝ) (75/256:ℝ)-(6366249662322494241/21873345290796674560:ℝ)*thetaPowerMass 0 (149/512:ℝ) (75/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0228.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (149/512:ℝ) (75/256:ℝ)
    (6366249662322494241/21873345290796674560:ℝ) (104516884289/12500000000000:ℝ) (-1123100263923040084569625314417/12500000000000000000000000000000:ℝ) (192109287038277537851283/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_149
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0449).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_149 :
    (∫ x in (149/512:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x) ≤ (8083234152191742811/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (149/512:ℝ) (75/256:ℝ)
    (33458024467/4000000000000:ℝ) (204761149653/25000000000000:ℝ) (192109287038277537851283/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_149 (thetaFirstMode_refined_node_0445).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_150 :
    (15829335333373657023/1000000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(151/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-883654158575577255778453827/10000000000000000000000000000:ℝ)*(thetaPowerMass 1 (75/256:ℝ) (151/512:ℝ)-(75/256:ℝ)*thetaPowerMass 0 (75/256:ℝ) (151/512:ℝ)) ≤
      thetaFirstModeFirst (75/256:ℝ)*(thetaPowerMass 1 (75/256:ℝ) (151/512:ℝ)-(75/256:ℝ)*thetaPowerMass 0 (75/256:ℝ) (151/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0229.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (75/256:ℝ) (151/512:ℝ)
    (75/256:ℝ) (819043127053/100000000000000:ℝ) (-883654158575577255778453827/10000000000000000000000000000:ℝ) (759334039519671048511609/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_150
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0450).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_150 :
    (∫ x in (75/256:ℝ)..(151/512:ℝ), x^0*thetaFirstMode x) ≤ (494667982237527203/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (75/256:ℝ) (151/512:ℝ)
    (204761149653/25000000000000:ℝ) (400965861371/50000000000000:ℝ) (759334039519671048511609/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_150 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0451).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_151 :
    (3099586998219663651/200000000000000000000000:ℝ) ≤ ∫ x in (151/512:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-217118180229069638499437562101/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (151/512:ℝ) (19/64:ℝ)-(7177837152534081759/24335251372240130560:ℝ)*thetaPowerMass 0 (151/512:ℝ) (19/64:ℝ)) ≤
      thetaFirstModeFirst (7177837152534081759/24335251372240130560:ℝ)*(thetaPowerMass 1 (151/512:ℝ) (19/64:ℝ)-(7177837152534081759/24335251372240130560:ℝ)*thetaPowerMass 0 (151/512:ℝ) (19/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0231.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (151/512:ℝ) (19/64:ℝ)
    (7177837152534081759/24335251372240130560:ℝ) (801630743121/100000000000000:ℝ) (-217118180229069638499437562101/2500000000000000000000000000000:ℝ) (375134235707624221016263/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_151
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0455).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_151 :
    (∫ x in (151/512:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x) ≤ (3099594791986771081/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (151/512:ℝ) (19/64:ℝ)
    (400965861371/50000000000000:ℝ) (39255425577/5000000000000:ℝ) (375134235707624221016263/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_151 (thetaFirstMode_refined_node_0451).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_152 :
    (15172157179027674441/1000000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(153/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5337452279781138832050812283/62500000000000000000000000000:ℝ)*(thetaPowerMass 1 (19/64:ℝ) (153/512:ℝ)-(19/64:ℝ)*thetaPowerMass 0 (19/64:ℝ) (153/512:ℝ)) ≤
      thetaFirstModeFirst (19/64:ℝ)*(thetaPowerMass 1 (19/64:ℝ) (153/512:ℝ)-(19/64:ℝ)*thetaPowerMass 0 (19/64:ℝ) (153/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0232.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (19/64:ℝ) (153/512:ℝ)
    (19/64:ℝ) (78510708989/10000000000000:ℝ) (-5337452279781138832050812283/62500000000000000000000000000:ℝ) (370620734176972153163053/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_152
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0456).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_152 :
    (∫ x in (19/64:ℝ)..(153/512:ℝ), x^0*thetaFirstMode x) ≤ (3793049051432190037/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/64:ℝ) (153/512:ℝ)
    (39255425577/5000000000000:ℝ) (76857150679/10000000000000:ℝ) (370620734176972153163053/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_152 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0457).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_153 :
    (3712984212335269947/250000000000000000000000:ℝ) ≤ ∫ x in (153/512:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1048968278535039437045883926147/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (153/512:ℝ) (77/256:ℝ)-(8080123862216333457/27036289542638748160:ℝ)*thetaPowerMass 0 (153/512:ℝ) (77/256:ℝ)) ≤
      thetaFirstModeFirst (8080123862216333457/27036289542638748160:ℝ)*(thetaPowerMass 1 (153/512:ℝ) (77/256:ℝ)-(8080123862216333457/27036289542638748160:ℝ)*thetaPowerMass 0 (153/512:ℝ) (77/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0234.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (153/512:ℝ) (77/256:ℝ)
    (8080123862216333457/27036289542638748160:ℝ) (192071115779/25000000000000:ℝ) (-1048968278535039437045883926147/12500000000000000000000000000000:ℝ) (732254038351135320149277/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_153
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0461).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_153 :
    (∫ x in (153/512:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x) ≤ (2970394953755929657/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (153/512:ℝ) (77/256:ℝ)
    (76857150679/10000000000000:ℝ) (752317264991/100000000000000:ℝ) (732254038351135320149277/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_153 (thetaFirstMode_refined_node_0457).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_154 :
    (7268602283045044791/500000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(155/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2062593249729226879894276925523/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (77/256:ℝ) (155/512:ℝ)-(77/256:ℝ)*thetaPowerMass 0 (77/256:ℝ) (155/512:ℝ)) ≤
      thetaFirstModeFirst (77/256:ℝ)*(thetaPowerMass 1 (77/256:ℝ) (155/512:ℝ)-(77/256:ℝ)*thetaPowerMass 0 (77/256:ℝ) (155/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0235.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (77/256:ℝ) (155/512:ℝ)
    (77/256:ℝ) (376157946017/50000000000000:ℝ) (-2062593249729226879894276925523/25000000000000000000000000000000:ℝ) (361653586367971121122721/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_154
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0462).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_154 :
    (∫ x in (77/256:ℝ)..(155/512:ℝ), x^0*thetaFirstMode x) ≤ (7268621270021643657/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (77/256:ℝ) (155/512:ℝ)
    (752317264991/100000000000000:ℝ) (736342357741/100000000000000:ℝ) (361653586367971121122721/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_154 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0463).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_155 :
    (14227895820252944163/1000000000000000000000000:ℝ) ≤ ∫ x in (155/512:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-101322487675637297705305099061/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (155/512:ℝ) (39/128:ℝ)-(1816371645569997795/5999219949625943552:ℝ)*thetaPowerMass 0 (155/512:ℝ) (39/128:ℝ)) ≤
      thetaFirstModeFirst (1816371645569997795/5999219949625943552:ℝ)*(thetaPowerMass 1 (155/512:ℝ) (39/128:ℝ)-(1816371645569997795/5999219949625943552:ℝ)*thetaPowerMass 0 (155/512:ℝ) (39/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0237.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (155/512:ℝ) (39/128:ℝ)
    (1816371645569997795/5999219949625943552:ℝ) (736068654267/100000000000000:ℝ) (-101322487675637297705305099061/1250000000000000000000000000000:ℝ) (357200922982804769686459/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_155
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0467).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_155 :
    (∫ x in (155/512:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x) ≤ (14227932709002545173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (155/512:ℝ) (39/128:ℝ)
    (736342357741/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (357200922982804769686459/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_155 (thetaFirstMode_refined_node_0463).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_156 :
    (13923941831024467537/1000000000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(157/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1991956954393217262127398832221/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (39/128:ℝ) (157/512:ℝ)-(39/128:ℝ)*thetaPowerMass 0 (39/128:ℝ) (157/512:ℝ)) ≤
      thetaFirstModeFirst (39/128:ℝ)*(thetaPowerMass 1 (39/128:ℝ) (157/512:ℝ)-(39/128:ℝ)*thetaPowerMass 0 (39/128:ℝ) (157/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0238.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (39/128:ℝ) (157/512:ℝ)
    (39/128:ℝ) (720642046639/100000000000000:ℝ) (-1991956954393217262127398832221/25000000000000000000000000000000:ℝ) (705539015461980504919239/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_156
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0468).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_156 :
    (∫ x in (39/128:ℝ)..(157/512:ℝ), x^0*thetaFirstMode x) ≤ (13923978770932116769/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/128:ℝ) (157/512:ℝ)
    (720643372107/100000000000000:ℝ) (705216910999/100000000000000:ℝ) (705539015461980504919239/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_156 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0469).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_157 :
    (13625278657581556283/1000000000000000000000000:ℝ) ≤ ∫ x in (157/512:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-78268222841926281470126304231/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (157/512:ℝ) (79/256:ℝ)-(10192502262515829993/33235648177494300160:ℝ)*thetaPowerMass 0 (157/512:ℝ) (79/256:ℝ)) ≤
      thetaFirstModeFirst (10192502262515829993/33235648177494300160:ℝ)*(thetaPowerMass 1 (157/512:ℝ) (79/256:ℝ)-(10192502262515829993/33235648177494300160:ℝ)*thetaPowerMass 0 (157/512:ℝ) (79/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0240.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (157/512:ℝ) (79/256:ℝ)
    (10192502262515829993/33235648177494300160:ℝ) (704955976797/100000000000000:ℝ) (-78268222841926281470126304231/1000000000000000000000000000000:ℝ) (348359810723514749431253/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_157
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0473).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_157 :
    (∫ x in (157/512:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x) ≤ (6812657267111422423/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (157/512:ℝ) (79/256:ℝ)
    (705216910999/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (348359810723514749431253/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_157 (thetaFirstMode_refined_node_0469).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_158 :
    (1666479775356858157/125000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(159/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1923055802555391946567563659283/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (79/256:ℝ) (159/512:ℝ)-(79/256:ℝ)*thetaPowerMass 0 (79/256:ℝ) (159/512:ℝ)) ≤
      thetaFirstModeFirst (79/256:ℝ)*(thetaPowerMass 1 (79/256:ℝ) (159/512:ℝ)-(79/256:ℝ)*thetaPowerMass 0 (79/256:ℝ) (159/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0241.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (79/256:ℝ) (159/512:ℝ)
    (79/256:ℝ) (86257289297/12500000000000:ℝ) (-1923055802555391946567563659283/25000000000000000000000000000000:ℝ) (171986146693352966422757/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_158
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0474).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_158 :
    (∫ x in (79/256:ℝ)..(159/512:ℝ), x^0*thetaFirstMode x) ≤ (6665937063701654781/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (79/256:ℝ) (159/512:ℝ)
    (345029796773/50000000000000:ℝ) (675168055439/100000000000000:ℝ) (171986146693352966422757/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_158 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0475).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_159 :
    (2608711424590834431/200000000000000000000000:ℝ) ≤ ∫ x in (159/512:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-188868743363900031565117752833/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (159/512:ℝ) (5/16:ℝ)-(11422279416358375191/36777297964497103360:ℝ)*thetaPowerMass 0 (159/512:ℝ) (5/16:ℝ)) ≤
      thetaFirstModeFirst (11422279416358375191/36777297964497103360:ℝ)*(thetaPowerMass 1 (159/512:ℝ) (5/16:ℝ)-(11422279416358375191/36777297964497103360:ℝ)*thetaPowerMass 0 (159/512:ℝ) (5/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0243.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (159/512:ℝ) (5/16:ℝ)
    (11422279416358375191/36777297964497103360:ℝ) (337459671627/50000000000000:ℝ) (-188868743363900031565117752833/2500000000000000000000000000000:ℝ) (339607408390625219458253/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_159
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0479).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_159 :
    (∫ x in (159/512:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x) ≤ (13043592006024683037/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (159/512:ℝ) (5/16:ℝ)
    (675168055439/100000000000000:ℝ) (660538949293/100000000000000:ℝ) (339607408390625219458253/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_159 (thetaFirstMode_refined_node_0475).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
