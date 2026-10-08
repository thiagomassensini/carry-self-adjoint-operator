import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature02
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative03
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative04

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_064 :
    (73080108816002075391/1000000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(65/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-445725857800306196260935340291/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (1/8:ℝ) (65/512:ℝ)-(1/8:ℝ)*thetaPowerMass 0 (1/8:ℝ) (65/512:ℝ)) ≤
      thetaFirstModeFirst (1/8:ℝ)*(thetaPowerMass 1 (1/8:ℝ) (65/512:ℝ)-(1/8:ℝ)*thetaPowerMass 0 (1/8:ℝ) (65/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0100.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (1/8:ℝ) (65/512:ℝ)
    (1/8:ℝ) (1884730660659/50000000000000:ℝ) (-445725857800306196260935340291/1562500000000000000000000000000:ℝ) (771616988138548525625321/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_064
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0192).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_064 :
    (∫ x in (1/8:ℝ)..(65/512:ℝ), x^0*thetaFirstMode x) ≤ (14616042536824559771/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/8:ℝ) (65/512:ℝ)
    (1884733080709/50000000000000:ℝ) (371404573361/10000000000000:ℝ) (771616988138548525625321/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_064 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0193).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_065 :
    (3600171711526146493/50000000000000000000000:ℝ) ≤ ∫ x in (65/512:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-440812068793677968734930153603/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (65/512:ℝ) (33/256:ℝ)-(730222341159285/5748281504317952:ℝ)*thetaPowerMass 0 (65/512:ℝ) (33/256:ℝ)) ≤
      thetaFirstModeFirst (730222341159285/5748281504317952:ℝ)*(thetaPowerMass 1 (65/512:ℝ) (33/256:ℝ)-(730222341159285/5748281504317952:ℝ)*thetaPowerMass 0 (65/512:ℝ) (33/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0102.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (65/512:ℝ) (33/256:ℝ)
    (730222341159285/5748281504317952:ℝ) (3711782621959/100000000000000:ℝ) (-440812068793677968734930153603/1562500000000000000000000000000:ℝ) (1535797490155883452378041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_065
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0197).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_065 :
    (∫ x in (65/512:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x) ≤ (72003536047619425231/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (65/512:ℝ) (33/256:ℝ)
    (371404573361/10000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1535797490155883452378041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_065 (thetaFirstMode_refined_node_0193).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_066 :
    (22168196154360129/312500000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(67/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-13961816701874181469687612947111/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (33/256:ℝ) (67/512:ℝ)-(33/256:ℝ)*thetaPowerMass 0 (33/256:ℝ) (67/512:ℝ)) ≤
      thetaFirstModeFirst (33/256:ℝ)*(thetaPowerMass 1 (33/256:ℝ) (67/512:ℝ)-(33/256:ℝ)*thetaPowerMass 0 (33/256:ℝ) (67/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0103.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (33/256:ℝ) (67/512:ℝ)
    (33/256:ℝ) (3659209265657/100000000000000:ℝ) (-13961816701874181469687612947111/50000000000000000000000000000000:ℝ) (382070368022873068008451/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_066
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0198).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_066 :
    (∫ x in (33/256:ℝ)..(67/512:ℝ), x^0*thetaFirstMode x) ≤ (70938329711677621621/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/256:ℝ) (67/512:ℝ)
    (3659214001041/100000000000000:ℝ) (1802484063477/50000000000000:ℝ) (382070368022873068008451/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_066 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0199).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_067 :
    (69884437989294546921/1000000000000000000000000:ℝ) ≤ ∫ x in (67/512:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-862891861876883622691457190309/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (67/512:ℝ) (17/128:ℝ)-(4795188919157943/36622101413148160:ℝ)*thetaPowerMass 0 (67/512:ℝ) (17/128:ℝ)) ≤
      thetaFirstModeFirst (4795188919157943/36622101413148160:ℝ)*(thetaPowerMass 1 (67/512:ℝ) (17/128:ℝ)-(4795188919157943/36622101413148160:ℝ)*thetaPowerMass 0 (67/512:ℝ) (17/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0105.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (67/512:ℝ) (17/128:ℝ)
    (4795188919157943/36622101413148160:ℝ) (3602818939147/100000000000000:ℝ) (-862891861876883622691457190309/3125000000000000000000000000000:ℝ) (1520687241082132602176131/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_067
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0203).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_067 :
    (∫ x in (67/512:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x) ≤ (69884537973720633653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (67/512:ℝ) (17/128:ℝ)
    (1802484063477/50000000000000:ℝ) (1775652622123/50000000000000:ℝ) (1520687241082132602176131/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_067 (thetaFirstMode_refined_node_0199).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_068 :
    (68842004361195028487/1000000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(69/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-426978946296379989904850928447/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (17/128:ℝ) (69/512:ℝ)-(17/128:ℝ)*thetaPowerMass 0 (17/128:ℝ) (69/512:ℝ)) ≤
      thetaFirstModeFirst (17/128:ℝ)*(thetaPowerMass 1 (17/128:ℝ) (69/512:ℝ)-(17/128:ℝ)*thetaPowerMass 0 (17/128:ℝ) (69/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0106.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (17/128:ℝ) (69/512:ℝ)
    (17/128:ℝ) (1775650306231/50000000000000:ℝ) (-426978946296379989904850928447/1562500000000000000000000000000:ℝ) (151301612701023632113533/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_068
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0204).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_068 :
    (∫ x in (17/128:ℝ)..(69/512:ℝ), x^0*thetaFirstMode x) ≤ (68842104543635652267/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/128:ℝ) (69/512:ℝ)
    (1775652622123/50000000000000:ℝ) (3498222455997/100000000000000:ℝ) (151301612701023632113533/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_068 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0205).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_069 :
    (13562174877234668637/200000000000000000000000:ℝ) ≤ ∫ x in (69/512:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-844343231971522615162708807799/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (69/512:ℝ) (35/256:ℝ)-(6247526395102641/46332533517852160:ℝ)*thetaPowerMass 0 (69/512:ℝ) (35/256:ℝ)) ≤
      thetaFirstModeFirst (6247526395102641/46332533517852160:ℝ)*(thetaPowerMass 1 (69/512:ℝ) (35/256:ℝ)-(6247526395102641/46332533517852160:ℝ)*thetaPowerMass 0 (69/512:ℝ) (35/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0108.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (69/512:ℝ) (35/256:ℝ)
    (6247526395102641/46332533517852160:ℝ) (3496180167453/100000000000000:ℝ) (-844343231971522615162708807799/3125000000000000000000000000000:ℝ) (1505269470331555588058513/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_069
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0209).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_069 :
    (∫ x in (69/512:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x) ≤ (33905486276828409621/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (69/512:ℝ) (35/256:ℝ)
    (3498222455997/100000000000000:ℝ) (3445716835953/100000000000000:ℝ) (1505269470331555588058513/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_069 (thetaFirstMode_refined_node_0205).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_070 :
    (33395493102656914571/500000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(71/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2673563457772826413547084387181/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (35/256:ℝ) (71/512:ℝ)-(35/256:ℝ)*thetaPowerMass 0 (35/256:ℝ) (71/512:ℝ)) ≤
      thetaFirstModeFirst (35/256:ℝ)*(thetaPowerMass 1 (35/256:ℝ) (71/512:ℝ)-(35/256:ℝ)*thetaPowerMass 0 (35/256:ℝ) (71/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0109.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (35/256:ℝ) (71/512:ℝ)
    (35/256:ℝ) (689142461327/20000000000000:ℝ) (-2673563457772826413547084387181/10000000000000000000000000000000:ℝ) (748724310880892193048397/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_070
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0210).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_070 :
    (∫ x in (35/256:ℝ)..(71/512:ℝ), x^0*thetaFirstMode x) ≤ (66791084568131046777/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/256:ℝ) (71/512:ℝ)
    (3445716835953/100000000000000:ℝ) (3393785429043/100000000000000:ℝ) (748724310880892193048397/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_070 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0211).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_071 :
    (65782286227163204889/1000000000000000000000000:ℝ) ≤ ∫ x in (71/512:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3303928266481065202744776473013/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (71/512:ℝ) (9/64:ℝ)-(8078499778926159/58225454071144960:ℝ)*thetaPowerMass 0 (71/512:ℝ) (9/64:ℝ)) ≤
      thetaFirstModeFirst (8078499778926159/58225454071144960:ℝ)*(thetaPowerMass 1 (71/512:ℝ) (9/64:ℝ)-(8078499778926159/58225454071144960:ℝ)*thetaPowerMass 0 (71/512:ℝ) (9/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0111.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (71/512:ℝ) (9/64:ℝ)
    (8078499778926159/58225454071144960:ℝ) (3391843597631/100000000000000:ℝ) (-3303928266481065202744776473013/12500000000000000000000000000000:ℝ) (744777470984011550919633/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_071
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0215).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_071 :
    (∫ x in (71/512:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x) ≤ (65782382593469380921/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (71/512:ℝ) (9/64:ℝ)
    (3393785429043/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (744777470984011550919633/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_071 (thetaFirstMode_refined_node_0211).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_072 :
    (64784711529626128763/1000000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(73/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-13075348738493213624644443723657/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (9/64:ℝ) (73/512:ℝ)-(9/64:ℝ)*thetaPowerMass 0 (9/64:ℝ) (73/512:ℝ)) ≤
      thetaFirstModeFirst (9/64:ℝ)*(thetaPowerMass 1 (9/64:ℝ) (73/512:ℝ)-(9/64:ℝ)*thetaPowerMass 0 (9/64:ℝ) (73/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0112.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (9/64:ℝ) (73/512:ℝ)
    (9/64:ℝ) (3342420823879/100000000000000:ℝ) (-13075348738493213624644443723657/50000000000000000000000000000000:ℝ) (370397450314778713904079/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_072
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0216).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_072 :
    (∫ x in (9/64:ℝ)..(73/512:ℝ), x^0*thetaFirstMode x) ≤ (64784808088420631343/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/64:ℝ) (73/512:ℝ)
    (3342425251881/100000000000000:ℝ) (822908323329/25000000000000:ℝ) (370397450314778713904079/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_072 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0217).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_073 :
    (1594955184834077963/25000000000000000000000:ℝ) ≤ ∫ x in (73/512:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12924992736998081823136428581811/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (73/512:ℝ) (37/256:ℝ)-(10371833391193857/72708564804252160:ℝ)*thetaPowerMass 0 (73/512:ℝ) (37/256:ℝ)) ≤
      thetaFirstModeFirst (10371833391193857/72708564804252160:ℝ)*(thetaPowerMass 1 (73/512:ℝ) (37/256:ℝ)-(10371833391193857/72708564804252160:ℝ)*thetaPowerMass 0 (73/512:ℝ) (37/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0114.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (73/512:ℝ) (37/256:ℝ)
    (10371833391193857/72708564804252160:ℝ) (3289785996133/100000000000000:ℝ) (-12924992736998081823136428581811/50000000000000000000000000000000:ℝ) (368388644815982758205847/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_073
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0221).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_073 :
    (∫ x in (73/512:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x) ≤ (63798301974296180451/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (73/512:ℝ) (37/256:ℝ)
    (822908323329/25000000000000:ℝ) (3241406514929/100000000000000:ℝ) (368388644815982758205847/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_073 (thetaFirstMode_refined_node_0217).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_074 :
    (31411354937130750709/500000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(75/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1278597752671478576101494157989/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (37/256:ℝ) (75/512:ℝ)-(37/256:ℝ)*thetaPowerMass 0 (37/256:ℝ) (75/512:ℝ)) ≤
      thetaFirstModeFirst (37/256:ℝ)*(thetaPowerMass 1 (37/256:ℝ) (75/512:ℝ)-(37/256:ℝ)*thetaPowerMass 0 (37/256:ℝ) (75/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0115.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (37/256:ℝ) (75/512:ℝ)
    (37/256:ℝ) (129656087483/4000000000000:ℝ) (-1278597752671478576101494157989/5000000000000000000000000000000:ℝ) (1465450664616607846771403/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_074
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0222).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_074 :
    (∫ x in (37/256:ℝ)..(75/512:ℝ), x^0*thetaFirstMode x) ≤ (62822804645204553823/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/256:ℝ) (75/512:ℝ)
    (3241406514929/100000000000000:ℝ) (49870966431/1562500000000:ℝ) (1465450664616607846771403/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_074 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0223).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_075 :
    (61858163166035841223/1000000000000000000000000:ℝ) ≤ ∫ x in (75/512:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2527477475311461353611027872753/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (75/512:ℝ) (19/128:ℝ)-(2645329456026675/18050233071498752:ℝ)*thetaPowerMass 0 (75/512:ℝ) (19/128:ℝ)) ≤
      thetaFirstModeFirst (2645329456026675/18050233071498752:ℝ)*(thetaPowerMass 1 (75/512:ℝ) (19/128:ℝ)-(2645329456026675/18050233071498752:ℝ)*thetaPowerMass 0 (75/512:ℝ) (19/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0117.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (75/512:ℝ) (19/128:ℝ)
    (2645329456026675/18050233071498752:ℝ) (3189983630081/100000000000000:ℝ) (-2527477475311461353611027872753/10000000000000000000000000000000:ℝ) (1457279454603692893258001/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_075
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0227).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_075 :
    (∫ x in (75/512:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x) ≤ (61858255978032108041/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (75/512:ℝ) (19/128:ℝ)
    (49870966431/1562500000000:ℝ) (3142636211899/100000000000000:ℝ) (1457279454603692893258001/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_075 (thetaFirstMode_refined_node_0223).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_076 :
    (60904502344049260539/1000000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(77/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-249995168035775104043002072727/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (19/128:ℝ) (77/512:ℝ)-(19/128:ℝ)*thetaPowerMass 0 (19/128:ℝ) (77/512:ℝ)) ≤
      thetaFirstModeFirst (19/128:ℝ)*(thetaPowerMass 1 (19/128:ℝ) (77/512:ℝ)-(19/128:ℝ)*thetaPowerMass 0 (19/128:ℝ) (77/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0118.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (19/128:ℝ) (77/512:ℝ)
    (19/128:ℝ) (785657995753/25000000000000:ℝ) (-249995168035775104043002072727/1000000000000000000000000000000:ℝ) (1449042354883298170445393/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_076
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0228).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_076 :
    (∫ x in (19/128:ℝ)..(77/512:ℝ), x^0*thetaFirstMode x) ≤ (60904595343175626933/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/128:ℝ) (77/512:ℝ)
    (3142636211899/100000000000000:ℝ) (1547043239437/50000000000000:ℝ) (1449042354883298170445393/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_076 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0229).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_077 :
    (29980835277661310729/500000000000000000000000:ℝ) ≤ ∫ x in (77/512:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1544118923500118761735787114851/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (77/512:ℝ) (39/256:ℝ)-(16759748134830393/111391385333532160:ℝ)*thetaPowerMass 0 (77/512:ℝ) (39/256:ℝ)) ≤
      thetaFirstModeFirst (16759748134830393/111391385333532160:ℝ)*(thetaPowerMass 1 (77/512:ℝ) (39/256:ℝ)-(16759748134830393/111391385333532160:ℝ)*thetaPowerMass 0 (77/512:ℝ) (39/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0120.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (77/512:ℝ) (39/256:ℝ)
    (16759748134830393/111391385333532160:ℝ) (309241229113/10000000000000:ℝ) (-1544118923500118761735787114851/6250000000000000000000000000000:ℝ) (57629631164214578349543/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_077
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0233).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_077 :
    (∫ x in (77/512:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x) ≤ (59961761614913651097/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (77/512:ℝ) (39/256:ℝ)
    (1547043239437/50000000000000:ℝ) (121843580413/4000000000000:ℝ) (57629631164214578349543/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_077 (thetaFirstMode_refined_node_0229).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_078 :
    (14757400484530081437/250000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(79/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-61083719677945524088057453319/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (39/256:ℝ) (79/512:ℝ)-(39/256:ℝ)*thetaPowerMass 0 (39/256:ℝ) (79/512:ℝ)) ≤
      thetaFirstModeFirst (39/256:ℝ)*(thetaPowerMass 1 (39/256:ℝ) (79/512:ℝ)-(39/256:ℝ)*thetaPowerMass 0 (39/256:ℝ) (79/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0121.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (39/256:ℝ) (79/512:ℝ)
    (39/256:ℝ) (380760672401/12500000000000:ℝ) (-61083719677945524088057453319/250000000000000000000000000000:ℝ) (358094037155113844769399/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_078
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0234).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_078 :
    (∫ x in (39/256:ℝ)..(79/512:ℝ), x^0*thetaFirstMode x) ≤ (11805938636371175491/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/256:ℝ) (79/512:ℝ)
    (121843580413/4000000000000:ℝ) (4685378343/156250000000:ℝ) (358094037155113844769399/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_078 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0235).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_079 :
    (14527059658463059557/250000000000000000000000:ℝ) ≤ ∫ x in (79/512:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6035868455077975671958567201281/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (79/512:ℝ) (5/32:ℝ)-(21108185233275591/136744035433576960:ℝ)*thetaPowerMass 0 (79/512:ℝ) (5/32:ℝ)) ≤
      thetaFirstModeFirst (21108185233275591/136744035433576960:ℝ)*(thetaPowerMass 1 (79/512:ℝ) (5/32:ℝ)-(21108185233275591/136744035433576960:ℝ)*thetaPowerMass 0 (79/512:ℝ) (5/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0123.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (79/512:ℝ) (5/32:ℝ)
    (21108185233275591/136744035433576960:ℝ) (599409463703/20000000000000:ℝ) (-6035868455077975671958567201281/25000000000000000000000000000000:ℝ) (142394989210521566569459/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_079
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0239).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_079 :
    (∫ x in (79/512:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x) ≤ (58108327957568391801/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (79/512:ℝ) (5/32:ℝ)
    (4685378343/156250000000:ℝ) (2951741175631/100000000000000:ℝ) (142394989210521566569459/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_079 (thetaFirstMode_refined_node_0235).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_080 :
    (28598756943038986359/500000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(81/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5968492248843275032829280057421/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/32:ℝ) (81/512:ℝ)-(5/32:ℝ)*thetaPowerMass 0 (5/32:ℝ) (81/512:ℝ)) ≤
      thetaFirstModeFirst (5/32:ℝ)*(thetaPowerMass 1 (5/32:ℝ) (81/512:ℝ)-(5/32:ℝ)*thetaPowerMass 0 (5/32:ℝ) (81/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0124.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/32:ℝ) (81/512:ℝ)
    (5/32:ℝ) (184483571317/6250000000000:ℝ) (-5968492248843275032829280057421/25000000000000000000000000000000:ℝ) (707731722623356296678787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_080
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0240).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_080 :
    (∫ x in (5/32:ℝ)..(81/512:ℝ), x^0*thetaFirstMode x) ≤ (28598801695457830829/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/32:ℝ) (81/512:ℝ)
    (2951741175631/100000000000000:ℝ) (2905383404341/100000000000000:ℝ) (707731722623356296678787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_080 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0241).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_081 :
    (2251894754912566847/40000000000000000000000:ℝ) ≤ ∫ x in (81/512:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-23034753518307205617771900509/97656250000000000000000000000:ℝ)*(thetaPowerMass 1 (81/512:ℝ) (41/256:ℝ)-(26432093791371609/167009112048540160:ℝ)*thetaPowerMass 0 (81/512:ℝ) (41/256:ℝ)) ≤
      thetaFirstModeFirst (26432093791371609/167009112048540160:ℝ)*(thetaPowerMass 1 (81/512:ℝ) (41/256:ℝ)-(26432093791371609/167009112048540160:ℝ)*thetaPowerMass 0 (81/512:ℝ) (41/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0126.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (81/512:ℝ) (41/256:ℝ)
    (26432093791371609/167009112048540160:ℝ) (2903863621341/100000000000000:ℝ) (-23034753518307205617771900509/97656250000000000000000000000:ℝ) (140691825040653213041507/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_081
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0245).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_081 :
    (∫ x in (81/512:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x) ≤ (2814872823867490367/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (81/512:ℝ) (41/256:ℝ)
    (2905383404341/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (140691825040653213041507/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_081 (thetaFirstMode_refined_node_0241).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_082 :
    (55407735986091842987/1000000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(83/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2915132057808324045787876744147/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (41/256:ℝ) (83/512:ℝ)-(41/256:ℝ)*thetaPowerMass 0 (41/256:ℝ) (83/512:ℝ)) ≤
      thetaFirstModeFirst (41/256:ℝ)*(thetaPowerMass 1 (41/256:ℝ) (83/512:ℝ)-(41/256:ℝ)*thetaPowerMass 0 (41/256:ℝ) (83/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0127.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (41/256:ℝ) (83/512:ℝ)
    (41/256:ℝ) (178722603073/6250000000000:ℝ) (-2915132057808324045787876744147/12500000000000000000000000000000:ℝ) (1398315756235929239638543/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_082
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0246).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_082 :
    (∫ x in (41/256:ℝ)..(83/512:ℝ), x^0*thetaFirstMode x) ≤ (27703911884474951697/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/256:ℝ) (83/512:ℝ)
    (2859565588393/100000000000000:ℝ) (2814284468069/100000000000000:ℝ) (1398315756235929239638543/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_082 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0247).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_083 :
    (6816069435371229999/125000000000000000000000:ℝ) ≤ ∫ x in (83/512:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5759584812271629765978533442441/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (83/512:ℝ) (21/128:ℝ)-(32917849303728807/202980990606108160:ℝ)*thetaPowerMass 0 (83/512:ℝ) (21/128:ℝ)) ≤
      thetaFirstModeFirst (32917849303728807/202980990606108160:ℝ)*(thetaPowerMass 1 (83/512:ℝ) (21/128:ℝ)-(32917849303728807/202980990606108160:ℝ)*thetaPowerMass 0 (83/512:ℝ) (21/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0129.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (83/512:ℝ) (21/128:ℝ)
    (32917849303728807/202980990606108160:ℝ) (351604462549/12500000000000:ℝ) (-5759584812271629765978533442441/25000000000000000000000000000000:ℝ) (69482870869170007236767/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_083
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0251).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_083 :
    (∫ x in (83/512:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x) ≤ (54528641385506144539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (83/512:ℝ) (21/128:ℝ)
    (2814284468069/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (69482870869170007236767/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_083 (thetaFirstMode_refined_node_0247).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_084 :
    (53659758947571356643/1000000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(85/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5693710515581249436465745500623/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (21/128:ℝ) (85/512:ℝ)-(21/128:ℝ)*thetaPowerMass 0 (21/128:ℝ) (85/512:ℝ)) ≤
      thetaFirstModeFirst (21/128:ℝ)*(thetaPowerMass 1 (21/128:ℝ) (85/512:ℝ)-(21/128:ℝ)*thetaPowerMass 0 (21/128:ℝ) (85/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0130.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (21/128:ℝ) (85/512:ℝ)
    (21/128:ℝ) (1384766458359/50000000000000:ℝ) (-5693710515581249436465745500623/25000000000000000000000000000000:ℝ) (55237787764003379295427/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_084
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0252).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_084 :
    (∫ x in (21/128:ℝ)..(85/512:ℝ), x^0*thetaFirstMode x) ≤ (53659845025477121917/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/128:ℝ) (85/512:ℝ)
    (1384768380923/50000000000000:ℝ) (1362659583431/50000000000000:ℝ) (55237787764003379295427/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_084 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0253).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_085 :
    (10560257151734798803/200000000000000000000000:ℝ) ≤ ∫ x in (85/512:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11247909633159162109304544626363/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (85/512:ℝ) (43/256:ℝ)-(8156311544891565/49111668780733952:ℝ)*thetaPowerMass 0 (85/512:ℝ) (43/256:ℝ)) ≤
      thetaFirstModeFirst (8156311544891565/49111668780733952:ℝ)*(thetaPowerMass 1 (85/512:ℝ) (43/256:ℝ)-(8156311544891565/49111668780733952:ℝ)*thetaPowerMass 0 (85/512:ℝ) (43/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0132.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (85/512:ℝ) (43/256:ℝ)
    (8156311544891565/49111668780733952:ℝ) (2723937669481/100000000000000:ℝ) (-11247909633159162109304544626363/50000000000000000000000000000000:ℝ) (27443581038305592302033/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_085
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0257).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_085 :
    (∫ x in (85/512:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x) ≤ (26400684988253801341/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (85/512:ℝ) (43/256:ℝ)
    (1362659583431/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (27443581038305592302033/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_085 (thetaFirstMode_refined_node_0253).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_086 :
    (1298826668413826293/25000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(87/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2223541304891261386854239462981/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (43/256:ℝ) (87/512:ℝ)-(43/256:ℝ)*thetaPowerMass 0 (43/256:ℝ) (87/512:ℝ)) ≤
      thetaFirstModeFirst (43/256:ℝ)*(thetaPowerMass 1 (43/256:ℝ) (87/512:ℝ)-(43/256:ℝ)*thetaPowerMass 0 (43/256:ℝ) (87/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0133.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (43/256:ℝ) (87/512:ℝ)
    (43/256:ℝ) (167601537953/6250000000000:ℝ) (-2223541304891261386854239462981/10000000000000000000000000000000:ℝ) (1363361961265949616345863/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_086
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0258).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_086 :
    (∫ x in (43/256:ℝ)..(87/512:ℝ), x^0*thetaFirstMode x) ≤ (6494143890822637973/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/256:ℝ) (87/512:ℝ)
    (2681628359527/100000000000000:ℝ) (1319230498027/50000000000000:ℝ) (1363361961265949616345863/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_086 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0259).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_087 :
    (12778760106116322373/250000000000000000000000:ℝ) ≤ ∫ x in (87/512:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1372507094811860412583584941229/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (87/512:ℝ) (11/64:ℝ)-(50272907626205343/295754822586012160:ℝ)*thetaPowerMass 0 (87/512:ℝ) (11/64:ℝ)) ≤
      thetaFirstModeFirst (50272907626205343/295754822586012160:ℝ)*(thetaPowerMass 1 (87/512:ℝ) (11/64:ℝ)-(50272907626205343/295754822586012160:ℝ)*thetaPowerMass 0 (87/512:ℝ) (11/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0135.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (87/512:ℝ) (11/64:ℝ)
    (50272907626205343/295754822586012160:ℝ) (2637143276417/100000000000000:ℝ) (-1372507094811860412583584941229/6250000000000000000000000000000:ℝ) (677247448577648422409407/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_087
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0263).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_087 :
    (∫ x in (87/512:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x) ≤ (12778780743712545519/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (87/512:ℝ) (11/64:ℝ)
    (1319230498027/50000000000000:ℝ) (2595813713037/100000000000000:ℝ) (677247448577648422409407/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_087 (thetaFirstMode_refined_node_0259).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_088 :
    (25143568461597816441/500000000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(89/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5425713026250097947953973193683/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/64:ℝ) (89/512:ℝ)-(11/64:ℝ)*thetaPowerMass 0 (11/64:ℝ) (89/512:ℝ)) ≤
      thetaFirstModeFirst (11/64:ℝ)*(thetaPowerMass 1 (11/64:ℝ) (89/512:ℝ)-(11/64:ℝ)*thetaPowerMass 0 (11/64:ℝ) (89/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0136.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/64:ℝ) (89/512:ℝ)
    (11/64:ℝ) (1297905026173/50000000000000:ℝ) (-5425713026250097947953973193683/25000000000000000000000000000000:ℝ) (1345579338786648282695207/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_088
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0264).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_088 :
    (∫ x in (11/64:ℝ)..(89/512:ℝ), x^0*thetaFirstMode x) ≤ (50287219642681583509/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/64:ℝ) (89/512:ℝ)
    (2595813713037/100000000000000:ℝ) (638420782001/25000000000000:ℝ) (1345579338786648282695207/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_088 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0265).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_089 :
    (24734646992099117149/500000000000000000000000:ℝ) ≤ ∫ x in (89/512:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10715651598204005518805144426309/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (89/512:ℝ) (45/256:ℝ)-(61679411798377041/354710535855669760:ℝ)*thetaPowerMass 0 (89/512:ℝ) (45/256:ℝ)) ≤
      thetaFirstModeFirst (61679411798377041/354710535855669760:ℝ)*(thetaPowerMass 1 (89/512:ℝ) (45/256:ℝ)-(61679411798377041/354710535855669760:ℝ)*thetaPowerMass 0 (89/512:ℝ) (45/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0138.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (89/512:ℝ) (45/256:ℝ)
    (61679411798377041/354710535855669760:ℝ) (2552425923669/100000000000000:ℝ) (-10715651598204005518805144426309/50000000000000000000000000000000:ℝ) (41769274037795552817787/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_089
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0269).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_089 :
    (∫ x in (89/512:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x) ≤ (24734687442321395521/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (89/512:ℝ) (45/256:ℝ)
    (638420782001/25000000000000:ℝ) (2512065839989/100000000000000:ℝ) (41769274037795552817787/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_089 (thetaFirstMode_refined_node_0265).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_090 :
    (48661441033031554289/1000000000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(91/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10588618655822651373377582342077/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (45/256:ℝ) (91/512:ℝ)-(45/256:ℝ)*thetaPowerMass 0 (45/256:ℝ) (91/512:ℝ)) ≤
      thetaFirstModeFirst (45/256:ℝ)*(thetaPowerMass 1 (45/256:ℝ) (91/512:ℝ)-(45/256:ℝ)*thetaPowerMass 0 (45/256:ℝ) (91/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0139.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (45/256:ℝ) (91/512:ℝ)
    (45/256:ℝ) (2512062269617/100000000000000:ℝ) (-10588618655822651373377582342077/50000000000000000000000000000000:ℝ) (663804337474992033484227/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_090
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0270).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_090 :
    (∫ x in (45/256:ℝ)..(91/512:ℝ), x^0*thetaFirstMode x) ≤ (121653805248648213/2500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/256:ℝ) (91/512:ℝ)
    (2512065839989/100000000000000:ℝ) (1235479215041/50000000000000:ℝ) (663804337474992033484227/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_090 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0271).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_091 :
    (957270301458968887/20000000000000000000000:ℝ) ≤ ∫ x in (91/512:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2613683101637881345539804340327/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (91/512:ℝ) (23/128:ℝ)-(75331067100848559/423704371432783360:ℝ)*thetaPowerMass 0 (91/512:ℝ) (23/128:ℝ)) ≤
      thetaFirstModeFirst (75331067100848559/423704371432783360:ℝ)*(thetaPowerMass 1 (91/512:ℝ) (23/128:ℝ)-(75331067100848559/423704371432783360:ℝ)*thetaPowerMass 0 (91/512:ℝ) (23/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0141.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (91/512:ℝ) (23/128:ℝ)
    (75331067100848559/423704371432783360:ℝ) (1234879344403/50000000000000:ℝ) (-2613683101637881345539804340327/12500000000000000000000000000000:ℝ) (659278272829284846706663/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_091
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0275).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_091 :
    (∫ x in (91/512:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x) ≤ (47863594341098747447/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (91/512:ℝ) (23/128:ℝ)
    (1235479215041/50000000000000:ℝ) (1215178731007/50000000000000:ℝ) (659278272829284846706663/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_091 (thetaFirstMode_refined_node_0271).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_092 :
    (11768861224749769559/250000000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(93/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2582330265224662741602061841233/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (23/128:ℝ) (93/512:ℝ)-(23/128:ℝ)*thetaPowerMass 0 (23/128:ℝ) (93/512:ℝ)) ≤
      thetaFirstModeFirst (23/128:ℝ)*(thetaPowerMass 1 (23/128:ℝ) (93/512:ℝ)-(23/128:ℝ)*thetaPowerMass 0 (23/128:ℝ) (93/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0142.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (23/128:ℝ) (93/512:ℝ)
    (23/128:ℝ) (1215176990341/50000000000000:ℝ) (-2582330265224662741602061841233/12500000000000000000000000000000:ℝ) (654730936874303803865293/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_092
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0276).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_092 :
    (∫ x in (23/128:ℝ)..(93/512:ℝ), x^0*thetaFirstMode x) ≤ (23537762165025290609/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/128:ℝ) (93/512:ℝ)
    (1215178731007/50000000000000:ℝ) (2390259482727/100000000000000:ℝ) (654730936874303803865293/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_092 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0277).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_093 :
    (46297166810397848571/1000000000000000000000000:ℝ) ≤ ∫ x in (93/512:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1019733508622841471817190211/5000000000000000000000000000:ℝ)*(thetaPowerMass 1 (93/512:ℝ) (47/256:ℝ)-(91605462777481257/504167194710300160:ℝ)*thetaPowerMass 0 (93/512:ℝ) (47/256:ℝ)) ≤
      thetaFirstModeFirst (91605462777481257/504167194710300160:ℝ)*(thetaPowerMass 1 (93/512:ℝ) (47/256:ℝ)-(91605462777481257/504167194710300160:ℝ)*thetaPowerMass 0 (93/512:ℝ) (47/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0144.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (93/512:ℝ) (47/256:ℝ)
    (91605462777481257/504167194710300160:ℝ) (1194557172351/50000000000000:ℝ) (-1019733508622841471817190211/5000000000000000000000000000:ℝ) (260065230803511589920163/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_093
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0281).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_093 :
    (∫ x in (93/512:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x) ≤ (925944889283124507/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (93/512:ℝ) (47/256:ℝ)
    (2390259482727/100000000000000:ℝ) (2350661022913/100000000000000:ℝ) (260065230803511589920163/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_093 (thetaFirstMode_refined_node_0277).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_094 :
    (2276430450820486921/50000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(95/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10073567669361363370601205553991/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (47/256:ℝ) (95/512:ℝ)-(47/256:ℝ)*thetaPowerMass 0 (47/256:ℝ) (95/512:ℝ)) ≤
      thetaFirstModeFirst (47/256:ℝ)*(thetaPowerMass 1 (47/256:ℝ) (95/512:ℝ)-(47/256:ℝ)*thetaPowerMass 0 (47/256:ℝ) (95/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0145.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (47/256:ℝ) (95/512:ℝ)
    (47/256:ℝ) (587664407333/25000000000000:ℝ) (-10073567669361363370601205553991/50000000000000000000000000000000:ℝ) (12911508832914503896323/10000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_094
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0282).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_094 :
    (∫ x in (47/256:ℝ)..(95/512:ℝ), x^0*thetaFirstMode x) ≤ (9105737365952343711/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/256:ℝ) (95/512:ℝ)
    (2350661022913/100000000000000:ℝ) (2311558597617/100000000000000:ℝ) (12911508832914503896323/10000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_094 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0283).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_095 :
    (5596213394483371337/125000000000000000000000:ℝ) ≤ ∫ x in (95/512:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2485873295490302234156004147927/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (95/512:ℝ) (3/16:ℝ)-(22186673770886955/119539193595863552:ℝ)*thetaPowerMass 0 (95/512:ℝ) (3/16:ℝ)) ≤
      thetaFirstModeFirst (22186673770886955/119539193595863552:ℝ)*(thetaPowerMass 1 (95/512:ℝ) (3/16:ℝ)-(22186673770886955/119539193595863552:ℝ)*thetaPowerMass 0 (95/512:ℝ) (3/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0147.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (95/512:ℝ) (3/16:ℝ)
    (22186673770886955/119539193595863552:ℝ) (2310465379561/100000000000000:ℝ) (-2485873295490302234156004147927/12500000000000000000000000000000:ℝ) (80121097504047355743007/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_095
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0287).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_095 :
    (∫ x in (95/512:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x) ≤ (22384891606552320881/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (95/512:ℝ) (3/16:ℝ)
    (2311558597617/100000000000000:ℝ) (5682371767/250000000000:ℝ) (80121097504047355743007/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_095 (thetaFirstMode_refined_node_0283).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
