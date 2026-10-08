import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature02
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative03
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative04

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_064 :
    (736215633/10000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(65/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-441004311101183622189327/1562500000000000000000000:ℝ)*(thetaPowerMass 11 (1/8:ℝ) (65/512:ℝ)-(65/512:ℝ)*thetaPowerMass 10 (1/8:ℝ) (65/512:ℝ)) ≤
      thetaFirstModeFirst (65/512:ℝ)*(thetaPowerMass 11 (1/8:ℝ) (65/512:ℝ)-(65/512:ℝ)*thetaPowerMass 10 (1/8:ℝ) (65/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0101.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (1/8:ℝ) (65/512:ℝ)
    (65/512:ℝ) (3714040946007/100000000000000:ℝ) (-441004311101183622189327/1562500000000000000000000:ℝ) (771616988138548525625321/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_064
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0193).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_064 :
    (∫ x in (1/8:ℝ)..(65/512:ℝ), x^10*thetaFirstMode x) ≤ (736216627/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/8:ℝ) (65/512:ℝ)
    (1884733080709/50000000000000:ℝ) (371404573361/10000000000000:ℝ) (771616988138548525625321/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_064 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0193).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_065 :
    (4229937561/50000000000000000000000:ℝ) ≤ ∫ x in (65/512:ℝ)..(33/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-440812068793677968734930153603/1562500000000000000000000000000:ℝ)*(thetaPowerMass 11 (65/512:ℝ) (33/256:ℝ)-(730222341159285/5748281504317952:ℝ)*thetaPowerMass 10 (65/512:ℝ) (33/256:ℝ)) ≤
      thetaFirstModeFirst (730222341159285/5748281504317952:ℝ)*(thetaPowerMass 11 (65/512:ℝ) (33/256:ℝ)-(730222341159285/5748281504317952:ℝ)*thetaPowerMass 10 (65/512:ℝ) (33/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0102.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (65/512:ℝ) (33/256:ℝ)
    (730222341159285/5748281504317952:ℝ) (3711782621959/100000000000000:ℝ) (-440812068793677968734930153603/1562500000000000000000000000000:ℝ) (1535797490155883452378041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_065
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0197).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_065 :
    (∫ x in (65/512:ℝ)..(33/256:ℝ), x^10*thetaFirstMode x) ≤ (1057485889/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (65/512:ℝ) (33/256:ℝ)
    (371404573361/10000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1535797490155883452378041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_065 (thetaFirstMode_refined_node_0193).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_066 :
    (96980436503/1000000000000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(67/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1381217995574941985536647/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (33/256:ℝ) (67/512:ℝ)-(67/512:ℝ)*thetaPowerMass 10 (33/256:ℝ) (67/512:ℝ)) ≤
      thetaFirstModeFirst (67/512:ℝ)*(thetaPowerMass 11 (33/256:ℝ) (67/512:ℝ)-(67/512:ℝ)*thetaPowerMass 10 (33/256:ℝ) (67/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0104.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (33/256:ℝ) (67/512:ℝ)
    (67/512:ℝ) (360496344351/10000000000000:ℝ) (-1381217995574941985536647/5000000000000000000000000:ℝ) (382070368022873068008451/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_066
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0199).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_066 :
    (∫ x in (33/256:ℝ)..(67/512:ℝ), x^10*thetaFirstMode x) ≤ (96980568737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (33/256:ℝ) (67/512:ℝ)
    (3659214001041/100000000000000:ℝ) (1802484063477/50000000000000:ℝ) (382070368022873068008451/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_066 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0199).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_067 :
    (110916348223/1000000000000000000000000:ℝ) ≤ ∫ x in (67/512:ℝ)..(17/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-862891861876883622691457190309/3125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (67/512:ℝ) (17/128:ℝ)-(4795188919157943/36622101413148160:ℝ)*thetaPowerMass 10 (67/512:ℝ) (17/128:ℝ)) ≤
      thetaFirstModeFirst (4795188919157943/36622101413148160:ℝ)*(thetaPowerMass 11 (67/512:ℝ) (17/128:ℝ)-(4795188919157943/36622101413148160:ℝ)*thetaPowerMass 10 (67/512:ℝ) (17/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0105.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (67/512:ℝ) (17/128:ℝ)
    (4795188919157943/36622101413148160:ℝ) (3602818939147/100000000000000:ℝ) (-862891861876883622691457190309/3125000000000000000000000000000:ℝ) (1520687241082132602176131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_067
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0203).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_067 :
    (∫ x in (67/512:ℝ)..(17/128:ℝ), x^10*thetaFirstMode x) ≤ (27729126819/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (67/512:ℝ) (17/128:ℝ)
    (1802484063477/50000000000000:ℝ) (1775652622123/50000000000000:ℝ) (1520687241082132602176131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_067 (thetaFirstMode_refined_node_0199).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_068 :
    (63284463973/500000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(69/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-6757586546227492336257371/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (17/128:ℝ) (69/512:ℝ)-(69/512:ℝ)*thetaPowerMass 10 (17/128:ℝ) (69/512:ℝ)) ≤
      thetaFirstModeFirst (69/512:ℝ)*(thetaPowerMass 11 (17/128:ℝ) (69/512:ℝ)-(69/512:ℝ)*thetaPowerMass 10 (17/128:ℝ) (69/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0107.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (17/128:ℝ) (69/512:ℝ)
    (69/512:ℝ) (3498217875589/100000000000000:ℝ) (-6757586546227492336257371/25000000000000000000000000:ℝ) (151301612701023632113533/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_068
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0205).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_068 :
    (∫ x in (17/128:ℝ)..(69/512:ℝ), x^10*thetaFirstMode x) ≤ (126569102239/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/128:ℝ) (69/512:ℝ)
    (1775652622123/50000000000000:ℝ) (3498222455997/100000000000000:ℝ) (151301612701023632113533/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_068 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0205).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_069 :
    (144113989427/1000000000000000000000000:ℝ) ≤ ∫ x in (69/512:ℝ)..(35/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-844343231971522615162708807799/3125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (69/512:ℝ) (35/256:ℝ)-(6247526395102641/46332533517852160:ℝ)*thetaPowerMass 10 (69/512:ℝ) (35/256:ℝ)) ≤
      thetaFirstModeFirst (6247526395102641/46332533517852160:ℝ)*(thetaPowerMass 11 (69/512:ℝ) (35/256:ℝ)-(6247526395102641/46332533517852160:ℝ)*thetaPowerMass 10 (69/512:ℝ) (35/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0108.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (69/512:ℝ) (35/256:ℝ)
    (6247526395102641/46332533517852160:ℝ) (3496180167453/100000000000000:ℝ) (-844343231971522615162708807799/3125000000000000000000000000000:ℝ) (1505269470331555588058513/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_069
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0209).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_069 :
    (∫ x in (69/512:ℝ)..(35/256:ℝ), x^10*thetaFirstMode x) ≤ (144114198539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (69/512:ℝ) (35/256:ℝ)
    (3498222455997/100000000000000:ℝ) (3445716835953/100000000000000:ℝ) (1505269470331555588058513/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_069 (thetaFirstMode_refined_node_0205).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_070 :
    (32748326291/200000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(71/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3305294356720900482817879/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (35/256:ℝ) (71/512:ℝ)-(71/512:ℝ)*thetaPowerMass 10 (35/256:ℝ) (71/512:ℝ)) ≤
      thetaFirstModeFirst (71/512:ℝ)*(thetaPowerMass 11 (35/256:ℝ) (71/512:ℝ)-(71/512:ℝ)*thetaPowerMass 10 (35/256:ℝ) (71/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0110.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (35/256:ℝ) (71/512:ℝ)
    (71/512:ℝ) (3393780950527/100000000000000:ℝ) (-3305294356720900482817879/12500000000000000000000000:ℝ) (748724310880892193048397/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_070
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0211).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_070 :
    (∫ x in (35/256:ℝ)..(71/512:ℝ), x^10*thetaFirstMode x) ≤ (163741859189/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (35/256:ℝ) (71/512:ℝ)
    (3445716835953/100000000000000:ℝ) (3393785429043/100000000000000:ℝ) (748724310880892193048397/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_070 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0211).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_071 :
    (92828451811/500000000000000000000000:ℝ) ≤ ∫ x in (71/512:ℝ)..(9/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3303928266481065202744776473013/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (71/512:ℝ) (9/64:ℝ)-(8078499778926159/58225454071144960:ℝ)*thetaPowerMass 10 (71/512:ℝ) (9/64:ℝ)) ≤
      thetaFirstModeFirst (8078499778926159/58225454071144960:ℝ)*(thetaPowerMass 11 (71/512:ℝ) (9/64:ℝ)-(8078499778926159/58225454071144960:ℝ)*thetaPowerMass 10 (71/512:ℝ) (9/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0111.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (71/512:ℝ) (9/64:ℝ)
    (8078499778926159/58225454071144960:ℝ) (3391843597631/100000000000000:ℝ) (-3303928266481065202744776473013/12500000000000000000000000000000:ℝ) (744777470984011550919633/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_071
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0215).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_071 :
    (∫ x in (71/512:ℝ)..(9/64:ℝ), x^10*thetaFirstMode x) ≤ (185657176231/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (71/512:ℝ) (9/64:ℝ)
    (3393785429043/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (744777470984011550919633/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_071 (thetaFirstMode_refined_node_0211).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_072 :
    (52520201959/250000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(73/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2586050183630350436935147/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (9/64:ℝ) (73/512:ℝ)-(73/512:ℝ)*thetaPowerMass 10 (9/64:ℝ) (73/512:ℝ)) ≤
      thetaFirstModeFirst (73/512:ℝ)*(thetaPowerMass 11 (9/64:ℝ) (73/512:ℝ)-(73/512:ℝ)*thetaPowerMass 10 (9/64:ℝ) (73/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0113.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (9/64:ℝ) (73/512:ℝ)
    (73/512:ℝ) (658325783107/20000000000000:ℝ) (-2586050183630350436935147/10000000000000000000000000:ℝ) (370397450314778713904079/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_072
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0217).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_072 :
    (∫ x in (9/64:ℝ)..(73/512:ℝ), x^10*thetaFirstMode x) ≤ (210081102949/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/64:ℝ) (73/512:ℝ)
    (3342425251881/100000000000000:ℝ) (822908323329/25000000000000:ℝ) (370397450314778713904079/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_072 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0217).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_073 :
    (59312738447/250000000000000000000000:ℝ) ≤ ∫ x in (73/512:ℝ)..(37/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-12924992736998081823136428581811/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (73/512:ℝ) (37/256:ℝ)-(10371833391193857/72708564804252160:ℝ)*thetaPowerMass 10 (73/512:ℝ) (37/256:ℝ)) ≤
      thetaFirstModeFirst (10371833391193857/72708564804252160:ℝ)*(thetaPowerMass 11 (73/512:ℝ) (37/256:ℝ)-(10371833391193857/72708564804252160:ℝ)*thetaPowerMass 10 (73/512:ℝ) (37/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0114.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (73/512:ℝ) (37/256:ℝ)
    (10371833391193857/72708564804252160:ℝ) (3289785996133/100000000000000:ℝ) (-12924992736998081823136428581811/50000000000000000000000000000000:ℝ) (368388644815982758205847/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_073
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0221).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_073 :
    (∫ x in (73/512:ℝ)..(37/256:ℝ), x^10*thetaFirstMode x) ≤ (118625653171/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (73/512:ℝ) (37/256:ℝ)
    (822908323329/25000000000000:ℝ) (3241406514929/100000000000000:ℝ) (368388644815982758205847/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_073 (thetaFirstMode_refined_node_0217).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_074 :
    (267422659239/1000000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(75/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3160612348033087623930969/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (37/256:ℝ) (75/512:ℝ)-(75/512:ℝ)*thetaPowerMass 10 (37/256:ℝ) (75/512:ℝ)) ≤
      thetaFirstModeFirst (75/512:ℝ)*(thetaPowerMass 11 (37/256:ℝ) (75/512:ℝ)-(75/512:ℝ)*thetaPowerMass 10 (37/256:ℝ) (75/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0116.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (37/256:ℝ) (75/512:ℝ)
    (75/512:ℝ) (1595868786681/50000000000000:ℝ) (-3160612348033087623930969/12500000000000000000000000:ℝ) (1465450664616607846771403/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_074
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0223).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_074 :
    (∫ x in (37/256:ℝ)..(75/512:ℝ), x^10*thetaFirstMode x) ≤ (267423038687/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (37/256:ℝ) (75/512:ℝ)
    (3241406514929/100000000000000:ℝ) (49870966431/1562500000000:ℝ) (1465450664616607846771403/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_074 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0223).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_075 :
    (300869574429/1000000000000000000000000:ℝ) ≤ ∫ x in (75/512:ℝ)..(19/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2527477475311461353611027872753/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (75/512:ℝ) (19/128:ℝ)-(2645329456026675/18050233071498752:ℝ)*thetaPowerMass 10 (75/512:ℝ) (19/128:ℝ)) ≤
      thetaFirstModeFirst (2645329456026675/18050233071498752:ℝ)*(thetaPowerMass 11 (75/512:ℝ) (19/128:ℝ)-(2645329456026675/18050233071498752:ℝ)*thetaPowerMass 10 (75/512:ℝ) (19/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0117.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (75/512:ℝ) (19/128:ℝ)
    (2645329456026675/18050233071498752:ℝ) (3189983630081/100000000000000:ℝ) (-2527477475311461353611027872753/10000000000000000000000000000000:ℝ) (1457279454603692893258001/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_075
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0227).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_075 :
    (∫ x in (75/512:ℝ)..(19/128:ℝ), x^10*thetaFirstMode x) ≤ (150435013463/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (75/512:ℝ) (19/128:ℝ)
    (49870966431/1562500000000:ℝ) (3142636211899/100000000000000:ℝ) (1457279454603692893258001/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_075 (thetaFirstMode_refined_node_0223).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_076 :
    (168942447107/500000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(77/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3089456628025361405326801/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (19/128:ℝ) (77/512:ℝ)-(77/512:ℝ)*thetaPowerMass 10 (19/128:ℝ) (77/512:ℝ)) ≤
      thetaFirstModeFirst (77/512:ℝ)*(thetaPowerMass 11 (19/128:ℝ) (77/512:ℝ)-(77/512:ℝ)*thetaPowerMass 10 (19/128:ℝ) (77/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0119.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (19/128:ℝ) (77/512:ℝ)
    (77/512:ℝ) (1547041149511/50000000000000:ℝ) (-3089456628025361405326801/12500000000000000000000000:ℝ) (1449042354883298170445393/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_076
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0229).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_076 :
    (∫ x in (19/128:ℝ)..(77/512:ℝ), x^10*thetaFirstMode x) ≤ (337885378491/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (19/128:ℝ) (77/512:ℝ)
    (3142636211899/100000000000000:ℝ) (1547043239437/50000000000000:ℝ) (1449042354883298170445393/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_076 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0229).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_077 :
    (47347740683/125000000000000000000000:ℝ) ≤ ∫ x in (77/512:ℝ)..(39/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1544118923500118761735787114851/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (77/512:ℝ) (39/256:ℝ)-(16759748134830393/111391385333532160:ℝ)*thetaPowerMass 10 (77/512:ℝ) (39/256:ℝ)) ≤
      thetaFirstModeFirst (16759748134830393/111391385333532160:ℝ)*(thetaPowerMass 11 (77/512:ℝ) (39/256:ℝ)-(16759748134830393/111391385333532160:ℝ)*thetaPowerMass 10 (77/512:ℝ) (39/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0120.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (77/512:ℝ) (39/256:ℝ)
    (16759748134830393/111391385333532160:ℝ) (309241229113/10000000000000:ℝ) (-1544118923500118761735787114851/6250000000000000000000000000000:ℝ) (57629631164214578349543/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_077
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0233).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_077 :
    (∫ x in (77/512:ℝ)..(39/256:ℝ), x^10*thetaFirstMode x) ≤ (47347812759/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (77/512:ℝ) (39/256:ℝ)
    (1547043239437/50000000000000:ℝ) (121843580413/4000000000000:ℝ) (57629631164214578349543/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_077 (thetaFirstMode_refined_node_0229).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_078 :
    (52986928499/125000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(79/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3019108437952439639708251/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (39/256:ℝ) (79/512:ℝ)-(79/512:ℝ)*thetaPowerMass 10 (39/256:ℝ) (79/512:ℝ)) ≤
      thetaFirstModeFirst (79/512:ℝ)*(thetaPowerMass 11 (39/256:ℝ) (79/512:ℝ)-(79/512:ℝ)*thetaPowerMass 10 (39/256:ℝ) (79/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0122.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (39/256:ℝ) (79/512:ℝ)
    (79/512:ℝ) (1499319028417/50000000000000:ℝ) (-3019108437952439639708251/12500000000000000000000000:ℝ) (358094037155113844769399/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_078
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0235).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_078 :
    (∫ x in (39/256:ℝ)..(79/512:ℝ), x^10*thetaFirstMode x) ≤ (211948020859/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (39/256:ℝ) (79/512:ℝ)
    (121843580413/4000000000000:ℝ) (4685378343/156250000000:ℝ) (358094037155113844769399/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_078 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0235).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_079 :
    (59197761599/125000000000000000000000:ℝ) ≤ ∫ x in (79/512:ℝ)..(5/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-6035868455077975671958567201281/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (79/512:ℝ) (5/32:ℝ)-(21108185233275591/136744035433576960:ℝ)*thetaPowerMass 10 (79/512:ℝ) (5/32:ℝ)) ≤
      thetaFirstModeFirst (21108185233275591/136744035433576960:ℝ)*(thetaPowerMass 11 (79/512:ℝ) (5/32:ℝ)-(21108185233275591/136744035433576960:ℝ)*thetaPowerMass 10 (79/512:ℝ) (5/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0123.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (79/512:ℝ) (5/32:ℝ)
    (21108185233275591/136744035433576960:ℝ) (599409463703/20000000000000:ℝ) (-6035868455077975671958567201281/25000000000000000000000000000000:ℝ) (142394989210521566569459/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_079
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0239).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_079 :
    (∫ x in (79/512:ℝ)..(5/32:ℝ), x^10*thetaFirstMode x) ≤ (23679141127/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (79/512:ℝ) (5/32:ℝ)
    (4685378343/156250000000:ℝ) (2951741175631/100000000000000:ℝ) (142394989210521566569459/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_079 (thetaFirstMode_refined_node_0235).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_080 :
    (528222033623/1000000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(81/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2949580092583559481467759/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (5/32:ℝ) (81/512:ℝ)-(81/512:ℝ)*thetaPowerMass 10 (5/32:ℝ) (81/512:ℝ)) ≤
      thetaFirstModeFirst (81/512:ℝ)*(thetaPowerMass 11 (5/32:ℝ) (81/512:ℝ)-(81/512:ℝ)*thetaPowerMass 10 (5/32:ℝ) (81/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0125.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (5/32:ℝ) (81/512:ℝ)
    (81/512:ℝ) (2905379417603/100000000000000:ℝ) (-2949580092583559481467759/12500000000000000000000000:ℝ) (707731722623356296678787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_080
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0241).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_080 :
    (∫ x in (5/32:ℝ)..(81/512:ℝ), x^10*thetaFirstMode x) ≤ (264111403101/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/32:ℝ) (81/512:ℝ)
    (2951741175631/100000000000000:ℝ) (2905383404341/100000000000000:ℝ) (707731722623356296678787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_080 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0241).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_081 :
    (23528765467/40000000000000000000000:ℝ) ≤ ∫ x in (81/512:ℝ)..(41/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-23034753518307205617771900509/97656250000000000000000000000:ℝ)*(thetaPowerMass 11 (81/512:ℝ) (41/256:ℝ)-(26432093791371609/167009112048540160:ℝ)*thetaPowerMass 10 (81/512:ℝ) (41/256:ℝ)) ≤
      thetaFirstModeFirst (26432093791371609/167009112048540160:ℝ)*(thetaPowerMass 11 (81/512:ℝ) (41/256:ℝ)-(26432093791371609/167009112048540160:ℝ)*thetaPowerMass 10 (81/512:ℝ) (41/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0126.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (81/512:ℝ) (41/256:ℝ)
    (26432093791371609/167009112048540160:ℝ) (2903863621341/100000000000000:ℝ) (-23034753518307205617771900509/97656250000000000000000000000:ℝ) (140691825040653213041507/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_081
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0245).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_081 :
    (∫ x in (81/512:ℝ)..(41/256:ℝ), x^10*thetaFirstMode x) ≤ (588220054237/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (81/512:ℝ) (41/256:ℝ)
    (2905383404341/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (140691825040653213041507/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_081 (thetaFirstMode_refined_node_0241).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_082 :
    (327001365397/500000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(83/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-360110418415211111719267/1562500000000000000000000:ℝ)*(thetaPowerMass 11 (41/256:ℝ) (83/512:ℝ)-(83/512:ℝ)*thetaPowerMass 10 (41/256:ℝ) (83/512:ℝ)) ≤
      thetaFirstModeFirst (83/512:ℝ)*(thetaPowerMass 11 (41/256:ℝ) (83/512:ℝ)-(83/512:ℝ)*thetaPowerMass 10 (41/256:ℝ) (83/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0128.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (41/256:ℝ) (83/512:ℝ)
    (83/512:ℝ) (175892536003/6250000000000:ℝ) (-360110418415211111719267/1562500000000000000000000:ℝ) (1398315756235929239638543/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_082
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0247).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_082 :
    (∫ x in (41/256:ℝ)..(83/512:ℝ), x^10*thetaFirstMode x) ≤ (163500924287/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (41/256:ℝ) (83/512:ℝ)
    (2859565588393/100000000000000:ℝ) (2814284468069/100000000000000:ℝ) (1398315756235929239638543/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_082 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0247).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_083 :
    (72602776057/100000000000000000000000:ℝ) ≤ ∫ x in (83/512:ℝ)..(21/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-5759584812271629765978533442441/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (83/512:ℝ) (21/128:ℝ)-(32917849303728807/202980990606108160:ℝ)*thetaPowerMass 10 (83/512:ℝ) (21/128:ℝ)) ≤
      thetaFirstModeFirst (32917849303728807/202980990606108160:ℝ)*(thetaPowerMass 11 (83/512:ℝ) (21/128:ℝ)-(32917849303728807/202980990606108160:ℝ)*thetaPowerMass 10 (83/512:ℝ) (21/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0129.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (83/512:ℝ) (21/128:ℝ)
    (32917849303728807/202980990606108160:ℝ) (351604462549/12500000000000:ℝ) (-5759584812271629765978533442441/25000000000000000000000000000000:ℝ) (69482870869170007236767/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_083
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0251).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_083 :
    (∫ x in (83/512:ℝ)..(21/128:ℝ), x^10*thetaFirstMode x) ≤ (90753613393/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (83/512:ℝ) (21/128:ℝ)
    (2814284468069/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (69482870869170007236767/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_083 (thetaFirstMode_refined_node_0247).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_084 :
    (804776670859/1000000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(85/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2250423514356939893987757/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (21/128:ℝ) (85/512:ℝ)-(85/512:ℝ)*thetaPowerMass 10 (21/128:ℝ) (85/512:ℝ)) ≤
      thetaFirstModeFirst (85/512:ℝ)*(thetaPowerMass 11 (21/128:ℝ) (85/512:ℝ)-(85/512:ℝ)*thetaPowerMass 10 (21/128:ℝ) (85/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0131.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (21/128:ℝ) (85/512:ℝ)
    (85/512:ℝ) (545063073663/20000000000000:ℝ) (-2250423514356939893987757/10000000000000000000000000:ℝ) (55237787764003379295427/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_084
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0253).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_084 :
    (∫ x in (21/128:ℝ)..(85/512:ℝ), x^10*thetaFirstMode x) ≤ (804777872243/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (21/128:ℝ) (85/512:ℝ)
    (1384768380923/50000000000000:ℝ) (1362659583431/50000000000000:ℝ) (55237787764003379295427/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_084 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0253).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_085 :
    (890759345111/1000000000000000000000000:ℝ) ≤ ∫ x in (85/512:ℝ)..(43/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-11247909633159162109304544626363/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (85/512:ℝ) (43/256:ℝ)-(8156311544891565/49111668780733952:ℝ)*thetaPowerMass 10 (85/512:ℝ) (43/256:ℝ)) ≤
      thetaFirstModeFirst (8156311544891565/49111668780733952:ℝ)*(thetaPowerMass 11 (85/512:ℝ) (43/256:ℝ)-(8156311544891565/49111668780733952:ℝ)*thetaPowerMass 10 (85/512:ℝ) (43/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0132.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (85/512:ℝ) (43/256:ℝ)
    (8156311544891565/49111668780733952:ℝ) (2723937669481/100000000000000:ℝ) (-11247909633159162109304544626363/50000000000000000000000000000000:ℝ) (27443581038305592302033/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_085
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0257).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_085 :
    (∫ x in (85/512:ℝ)..(43/256:ℝ), x^10*thetaFirstMode x) ≤ (890760769393/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (85/512:ℝ) (43/256:ℝ)
    (1362659583431/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (27443581038305592302033/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_085 (thetaFirstMode_refined_node_0253).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_086 :
    (492257624621/500000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(87/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-10726675199165057979899/48828125000000000000000:ℝ)*(thetaPowerMass 11 (43/256:ℝ) (87/512:ℝ)-(87/512:ℝ)*thetaPowerMass 10 (43/256:ℝ) (87/512:ℝ)) ≤
      thetaFirstModeFirst (87/512:ℝ)*(thetaPowerMass 11 (43/256:ℝ) (87/512:ℝ)-(87/512:ℝ)*thetaPowerMass 10 (43/256:ℝ) (87/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0134.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (43/256:ℝ) (87/512:ℝ)
    (87/512:ℝ) (2576618447/97656250000:ℝ) (-10726675199165057979899/48828125000000000000000:ℝ) (1363361961265949616345863/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_086
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0259).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_086 :
    (∫ x in (43/256:ℝ)..(87/512:ℝ), x^10*thetaFirstMode x) ≤ (19690334683/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (43/256:ℝ) (87/512:ℝ)
    (2681628359527/100000000000000:ℝ) (1319230498027/50000000000000:ℝ) (1363361961265949616345863/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_086 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0259).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_087 :
    (1086613065119/1000000000000000000000000:ℝ) ≤ ∫ x in (87/512:ℝ)..(11/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1372507094811860412583584941229/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (87/512:ℝ) (11/64:ℝ)-(50272907626205343/295754822586012160:ℝ)*thetaPowerMass 10 (87/512:ℝ) (11/64:ℝ)) ≤
      thetaFirstModeFirst (50272907626205343/295754822586012160:ℝ)*(thetaPowerMass 11 (87/512:ℝ) (11/64:ℝ)-(50272907626205343/295754822586012160:ℝ)*thetaPowerMass 10 (87/512:ℝ) (11/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0135.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (87/512:ℝ) (11/64:ℝ)
    (50272907626205343/295754822586012160:ℝ) (2637143276417/100000000000000:ℝ) (-1372507094811860412583584941229/6250000000000000000000000000000:ℝ) (677247448577648422409407/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_087
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0263).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_087 :
    (∫ x in (87/512:ℝ)..(11/64:ℝ), x^10*thetaFirstMode x) ≤ (54330741219/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (87/512:ℝ) (11/64:ℝ)
    (1319230498027/50000000000000:ℝ) (2595813713037/100000000000000:ℝ) (677247448577648422409407/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_087 (thetaFirstMode_refined_node_0259).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_088 :
    (1197653150189/1000000000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(89/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-669972942398000957144817/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (11/64:ℝ) (89/512:ℝ)-(89/512:ℝ)*thetaPowerMass 10 (11/64:ℝ) (89/512:ℝ)) ≤
      thetaFirstModeFirst (89/512:ℝ)*(thetaPowerMass 11 (11/64:ℝ) (89/512:ℝ)-(89/512:ℝ)*thetaPowerMass 10 (11/64:ℝ) (89/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0137.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (11/64:ℝ) (89/512:ℝ)
    (89/512:ℝ) (319209939079/12500000000000:ℝ) (-669972942398000957144817/3125000000000000000000000:ℝ) (1345579338786648282695207/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_088
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0265).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_088 :
    (∫ x in (11/64:ℝ)..(89/512:ℝ), x^10*thetaFirstMode x) ≤ (598827487671/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/64:ℝ) (89/512:ℝ)
    (2595813713037/100000000000000:ℝ) (638420782001/25000000000000:ℝ) (1345579338786648282695207/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_088 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0265).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_089 :
    (659133391073/500000000000000000000000:ℝ) ≤ ∫ x in (89/512:ℝ)..(45/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-10715651598204005518805144426309/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (89/512:ℝ) (45/256:ℝ)-(61679411798377041/354710535855669760:ℝ)*thetaPowerMass 10 (89/512:ℝ) (45/256:ℝ)) ≤
      thetaFirstModeFirst (61679411798377041/354710535855669760:ℝ)*(thetaPowerMass 11 (89/512:ℝ) (45/256:ℝ)-(61679411798377041/354710535855669760:ℝ)*thetaPowerMass 10 (89/512:ℝ) (45/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0138.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (89/512:ℝ) (45/256:ℝ)
    (61679411798377041/354710535855669760:ℝ) (2552425923669/100000000000000:ℝ) (-10715651598204005518805144426309/50000000000000000000000000000000:ℝ) (41769274037795552817787/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_089
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0269).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_089 :
    (∫ x in (89/512:ℝ)..(45/256:ℝ), x^10*thetaFirstMode x) ≤ (659134471717/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (89/512:ℝ) (45/256:ℝ)
    (638420782001/25000000000000:ℝ) (2512065839989/100000000000000:ℝ) (41769274037795552817787/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_089 (thetaFirstMode_refined_node_0265).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_090 :
    (2318590407/1600000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(91/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-104585104799884434452673/500000000000000000000000:ℝ)*(thetaPowerMass 11 (45/256:ℝ) (91/512:ℝ)-(91/512:ℝ)*thetaPowerMass 10 (45/256:ℝ) (91/512:ℝ)) ≤
      thetaFirstModeFirst (91/512:ℝ)*(thetaPowerMass 11 (45/256:ℝ) (91/512:ℝ)-(91/512:ℝ)*thetaPowerMass 10 (45/256:ℝ) (91/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0140.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (45/256:ℝ) (91/512:ℝ)
    (91/512:ℝ) (2470954904391/100000000000000:ℝ) (-104585104799884434452673/500000000000000000000000:ℝ) (663804337474992033484227/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_090
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0271).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_090 :
    (∫ x in (45/256:ℝ)..(91/512:ℝ), x^10*thetaFirstMode x) ≤ (144912123581/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (45/256:ℝ) (91/512:ℝ)
    (2512065839989/100000000000000:ℝ) (1235479215041/50000000000000:ℝ) (663804337474992033484227/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_090 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0271).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_091 :
    (1590907381551/1000000000000000000000000:ℝ) ≤ ∫ x in (91/512:ℝ)..(23/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2613683101637881345539804340327/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (91/512:ℝ) (23/128:ℝ)-(75331067100848559/423704371432783360:ℝ)*thetaPowerMass 10 (91/512:ℝ) (23/128:ℝ)) ≤
      thetaFirstModeFirst (75331067100848559/423704371432783360:ℝ)*(thetaPowerMass 11 (91/512:ℝ) (23/128:ℝ)-(75331067100848559/423704371432783360:ℝ)*thetaPowerMass 10 (91/512:ℝ) (23/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0141.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (91/512:ℝ) (23/128:ℝ)
    (75331067100848559/423704371432783360:ℝ) (1234879344403/50000000000000:ℝ) (-2613683101637881345539804340327/12500000000000000000000000000000:ℝ) (659278272829284846706663/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_091
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0275).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_091 :
    (∫ x in (91/512:ℝ)..(23/128:ℝ), x^10*thetaFirstMode x) ≤ (1590910023001/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (91/512:ℝ) (23/128:ℝ)
    (1235479215041/50000000000000:ℝ) (1215178731007/50000000000000:ℝ) (659278272829284846706663/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_091 (thetaFirstMode_refined_node_0271).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_092 :
    (54511416167/31250000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(93/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-10200981173921390980686851/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (23/128:ℝ) (93/512:ℝ)-(93/512:ℝ)*thetaPowerMass 10 (23/128:ℝ) (93/512:ℝ)) ≤
      thetaFirstModeFirst (93/512:ℝ)*(thetaPowerMass 11 (23/128:ℝ) (93/512:ℝ)-(93/512:ℝ)*thetaPowerMass 10 (23/128:ℝ) (93/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0143.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (23/128:ℝ) (93/512:ℝ)
    (93/512:ℝ) (2390256045431/100000000000000:ℝ) (-10200981173921390980686851/50000000000000000000000000:ℝ) (654730936874303803865293/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_092
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0277).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_092 :
    (∫ x in (23/128:ℝ)..(93/512:ℝ), x^10*thetaFirstMode x) ≤ (872184015799/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/128:ℝ) (93/512:ℝ)
    (1215178731007/50000000000000:ℝ) (2390259482727/100000000000000:ℝ) (654730936874303803865293/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_092 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0277).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_093 :
    (1910260201713/1000000000000000000000000:ℝ) ≤ ∫ x in (93/512:ℝ)..(47/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1019733508622841471817190211/5000000000000000000000000000:ℝ)*(thetaPowerMass 11 (93/512:ℝ) (47/256:ℝ)-(91605462777481257/504167194710300160:ℝ)*thetaPowerMass 10 (93/512:ℝ) (47/256:ℝ)) ≤
      thetaFirstModeFirst (91605462777481257/504167194710300160:ℝ)*(thetaPowerMass 11 (93/512:ℝ) (47/256:ℝ)-(91605462777481257/504167194710300160:ℝ)*thetaPowerMass 10 (93/512:ℝ) (47/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0144.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (93/512:ℝ) (47/256:ℝ)
    (91605462777481257/504167194710300160:ℝ) (1194557172351/50000000000000:ℝ) (-1019733508622841471817190211/5000000000000000000000000000:ℝ) (260065230803511589920163/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_093
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0281).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_093 :
    (∫ x in (93/512:ℝ)..(47/256:ℝ), x^10*thetaFirstMode x) ≤ (191026341399/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (93/512:ℝ) (47/256:ℝ)
    (2390259482727/100000000000000:ℝ) (2350661022913/100000000000000:ℝ) (260065230803511589920163/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_093 (thetaFirstMode_refined_node_0277).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_094 :
    (1044698653351/500000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(95/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-99470123958132555901611/500000000000000000000000:ℝ)*(thetaPowerMass 11 (47/256:ℝ) (95/512:ℝ)-(95/512:ℝ)*thetaPowerMass 10 (47/256:ℝ) (95/512:ℝ)) ≤
      thetaFirstModeFirst (95/512:ℝ)*(thetaPowerMass 11 (47/256:ℝ) (95/512:ℝ)-(95/512:ℝ)*thetaPowerMass 10 (47/256:ℝ) (95/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0146.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (47/256:ℝ) (95/512:ℝ)
    (95/512:ℝ) (92462209897/4000000000000:ℝ) (-99470123958132555901611/500000000000000000000000:ℝ) (12911508832914503896323/10000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_094
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0283).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_094 :
    (∫ x in (47/256:ℝ)..(95/512:ℝ), x^10*thetaFirstMode x) ≤ (417880118421/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (47/256:ℝ) (95/512:ℝ)
    (2350661022913/100000000000000:ℝ) (2311558597617/100000000000000:ℝ) (12911508832914503896323/10000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_094 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0283).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_095 :
    (2282617184207/1000000000000000000000000:ℝ) ≤ ∫ x in (95/512:ℝ)..(3/16:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2485873295490302234156004147927/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (95/512:ℝ) (3/16:ℝ)-(22186673770886955/119539193595863552:ℝ)*thetaPowerMass 10 (95/512:ℝ) (3/16:ℝ)) ≤
      thetaFirstModeFirst (22186673770886955/119539193595863552:ℝ)*(thetaPowerMass 11 (95/512:ℝ) (3/16:ℝ)-(22186673770886955/119539193595863552:ℝ)*thetaPowerMass 10 (95/512:ℝ) (3/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0147.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (95/512:ℝ) (3/16:ℝ)
    (22186673770886955/119539193595863552:ℝ) (2310465379561/100000000000000:ℝ) (-2485873295490302234156004147927/12500000000000000000000000000000:ℝ) (80121097504047355743007/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_095
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0287).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_095 :
    (∫ x in (95/512:ℝ)..(3/16:ℝ), x^10*thetaFirstMode x) ≤ (2282621072069/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (95/512:ℝ) (3/16:ℝ)
    (2311558597617/100000000000000:ℝ) (5682371767/250000000000:ℝ) (80121097504047355743007/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_095 (thetaFirstMode_refined_node_0283).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
