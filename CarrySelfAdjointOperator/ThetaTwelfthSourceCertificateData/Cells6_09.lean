import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature09
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative13
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative14
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative15

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_6_288 :
    (10199549100847543/1000000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(289/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-75796730715399661167193/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (9/16:ℝ) (289/512:ℝ)-(289/512:ℝ)*thetaPowerMass 6 (9/16:ℝ) (289/512:ℝ)) ≤
      thetaFirstModeFirst (289/512:ℝ)*(thetaPowerMass 7 (9/16:ℝ) (289/512:ℝ)-(289/512:ℝ)*thetaPowerMass 6 (9/16:ℝ) (289/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0437.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (9/16:ℝ) (289/512:ℝ)
    (289/512:ℝ) (8008395751/50000000000000:ℝ) (-75796730715399661167193/25000000000000000000000000:ℝ) (25583653603413205650409/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_288
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0865).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_288 :
    (∫ x in (9/16:ℝ)..(289/512:ℝ), x^6*thetaFirstMode x) ≤ (1274951205403551/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/16:ℝ) (289/512:ℝ)
    (2077357167/12500000000000:ℝ) (16016841031/100000000000000:ℝ) (25583653603413205650409/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_288 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0865).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_289 :
    (10035520647549447/1000000000000000000000000:ℝ) ≤ ∫ x in (289/512:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-37886970455235311976951301697/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (289/512:ℝ) (145/256:ℝ)-(2472381744748202416041/4379996680278775605760:ℝ)*thetaPowerMass 6 (289/512:ℝ) (145/256:ℝ)) ≤
      thetaFirstModeFirst (2472381744748202416041/4379996680278775605760:ℝ)*(thetaPowerMass 7 (289/512:ℝ) (145/256:ℝ)-(2472381744748202416041/4379996680278775605760:ℝ)*thetaPowerMass 6 (289/512:ℝ) (145/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0438.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (289/512:ℝ) (145/256:ℝ)
    (2472381744748202416041/4379996680278775605760:ℝ) (8005664329/50000000000000:ℝ) (-37886970455235311976951301697/12500000000000000000000000000000:ℝ) (24864114131483293224261/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_289
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0869).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_289 :
    (∫ x in (289/512:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x) ≤ (5017804575819149/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (289/512:ℝ) (145/256:ℝ)
    (16016841031/100000000000000:ℝ) (3086868927/20000000000000:ℝ) (24864114131483293224261/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_289 (thetaFirstMode_refined_node_0865).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_290 :
    (1974402565901221/200000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(291/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-14187983494351461946011/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (145/256:ℝ) (291/512:ℝ)-(291/512:ℝ)*thetaPowerMass 6 (145/256:ℝ) (291/512:ℝ)) ≤
      thetaFirstModeFirst (291/512:ℝ)*(thetaPowerMass 7 (145/256:ℝ) (291/512:ℝ)-(291/512:ℝ)*thetaPowerMass 6 (145/256:ℝ) (291/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0440.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (145/256:ℝ) (291/512:ℝ)
    (291/512:ℝ) (14870772819/100000000000000:ℝ) (-14187983494351461946011/5000000000000000000000000:ℝ) (12080569058620188148461/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_290
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0871).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_290 :
    (∫ x in (145/256:ℝ)..(291/512:ℝ), x^6*thetaFirstMode x) ≤ (9872072453283909/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (145/256:ℝ) (291/512:ℝ)
    (3086868927/20000000000000:ℝ) (2974163833/20000000000000:ℝ) (12080569058620188148461/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_290 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0871).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_291 :
    (1941795020663157/200000000000000000000000:ℝ) ≤ ∫ x in (291/512:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1772963598784072678930509591/625000000000000000000000000000:ℝ)*(thetaPowerMass 7 (291/512:ℝ) (73/128:ℝ)-(2630697969772508777559/4628436250915918927360:ℝ)*thetaPowerMass 6 (291/512:ℝ) (73/128:ℝ)) ≤
      thetaFirstModeFirst (2630697969772508777559/4628436250915918927360:ℝ)*(thetaPowerMass 7 (291/512:ℝ) (73/128:ℝ)-(2630697969772508777559/4628436250915918927360:ℝ)*thetaPowerMass 6 (291/512:ℝ) (73/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0441.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (291/512:ℝ) (73/128:ℝ)
    (2630697969772508777559/4628436250915918927360:ℝ) (14865695153/100000000000000:ℝ) (-1772963598784072678930509591/625000000000000000000000000000:ℝ) (46948909398942769942027/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_291
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0875).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_291 :
    (∫ x in (291/512:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x) ≤ (2427265630384887/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (291/512:ℝ) (73/128:ℝ)
    (2974163833/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (46948909398942769942027/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_291 (thetaFirstMode_refined_node_0871).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_292 :
    (381863290128447/40000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(293/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-33177269885165861903363/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (73/128:ℝ) (293/512:ℝ)-(293/512:ℝ)*thetaPowerMass 6 (73/128:ℝ) (293/512:ℝ)) ≤
      thetaFirstModeFirst (293/512:ℝ)*(thetaPowerMass 7 (73/128:ℝ) (293/512:ℝ)-(293/512:ℝ)*thetaPowerMass 6 (73/128:ℝ) (293/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0443.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (73/128:ℝ) (293/512:ℝ)
    (293/512:ℝ) (6899252351/50000000000000:ℝ) (-33177269885165861903363/12500000000000000000000000:ℝ) (45607588912752387150693/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_292
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0877).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_292 :
    (∫ x in (73/128:ℝ)..(293/512:ℝ), x^6*thetaFirstMode x) ≤ (9546640925311521/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (73/128:ℝ) (293/512:ℝ)
    (14325728273/100000000000000:ℝ) (3449637011/25000000000000:ℝ) (45607588912752387150693/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_292 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0877).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_293 :
    (234619538236583/25000000000000000000000:ℝ) ≤ ∫ x in (293/512:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-6633450580908118564124625927/2500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (293/512:ℝ) (147/256:ℝ)-(2797962146921232130257/4889119879777782300160:ℝ)*thetaPowerMass 6 (293/512:ℝ) (147/256:ℝ)) ≤
      thetaFirstModeFirst (2797962146921232130257/4889119879777782300160:ℝ)*(thetaPowerMass 7 (293/512:ℝ) (147/256:ℝ)-(2797962146921232130257/4889119879777782300160:ℝ)*thetaPowerMass 6 (293/512:ℝ) (147/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0444.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (293/512:ℝ) (147/256:ℝ)
    (2797962146921232130257/4889119879777782300160:ℝ) (6896893831/50000000000000:ℝ) (-6633450580908118564124625927/2500000000000000000000000000000:ℝ) (22148889472059177758597/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_293
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0881).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_293 :
    (∫ x in (293/512:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x) ≤ (4692433901752709/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (293/512:ℝ) (147/256:ℝ)
    (3449637011/25000000000000:ℝ) (6644383393/50000000000000:ℝ) (22148889472059177758597/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_293 (thetaFirstMode_refined_node_0877).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_294 :
    (4611872076009669/500000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(295/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-387675493896549856977/156250000000000000000000:ℝ)*(thetaPowerMass 7 (147/256:ℝ) (295/512:ℝ)-(295/512:ℝ)*thetaPowerMass 6 (147/256:ℝ) (295/512:ℝ)) ≤
      thetaFirstModeFirst (295/512:ℝ)*(thetaPowerMass 7 (147/256:ℝ) (295/512:ℝ)-(295/512:ℝ)*thetaPowerMass 6 (147/256:ℝ) (295/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0446.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (147/256:ℝ) (295/512:ℝ)
    (295/512:ℝ) (79974027/625000000000:ℝ) (-387675493896549856977/156250000000000000000000:ℝ) (43018946814087568901247/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_294
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0883).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_294 :
    (∫ x in (147/256:ℝ)..(295/512:ℝ), x^6*thetaFirstMode x) ≤ (9223801840197479/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (147/256:ℝ) (295/512:ℝ)
    (6644383393/50000000000000:ℝ) (12795884827/100000000000000:ℝ) (43018946814087568901247/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_294 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0883).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_295 :
    (4531707584491453/500000000000000000000000:ℝ) ≤ ∫ x in (295/512:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-7751163915930783169895100477/3125000000000000000000000000000:ℝ)*(thetaPowerMass 7 (295/512:ℝ) (37/64:ℝ)-(594922741712509294755/1032512240214680279552:ℝ)*thetaPowerMass 6 (295/512:ℝ) (37/64:ℝ)) ≤
      thetaFirstModeFirst (594922741712509294755/1032512240214680279552:ℝ)*(thetaPowerMass 7 (295/512:ℝ) (37/64:ℝ)-(594922741712509294755/1032512240214680279552:ℝ)*thetaPowerMass 6 (295/512:ℝ) (37/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0447.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (295/512:ℝ) (37/64:ℝ)
    (594922741712509294755/1032512240214680279552:ℝ) (12791464733/100000000000000:ℝ) (-7751163915930783169895100477/3125000000000000000000000000000:ℝ) (41770563139424439673057/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_295
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0887).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_295 :
    (∫ x in (295/512:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x) ≤ (9063500243888877/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (295/512:ℝ) (37/64:ℝ)
    (12795884827/100000000000000:ℝ) (6159707157/50000000000000:ℝ) (41770563139424439673057/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_295 (thetaFirstMode_refined_node_0883).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_296 :
    (4451981025967817/500000000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(297/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-28974216979406574014411/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (37/64:ℝ) (297/512:ℝ)-(297/512:ℝ)*thetaPowerMass 6 (37/64:ℝ) (297/512:ℝ)) ≤
      thetaFirstModeFirst (297/512:ℝ)*(thetaPowerMass 7 (37/64:ℝ) (297/512:ℝ)-(297/512:ℝ)*thetaPowerMass 6 (37/64:ℝ) (297/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0449.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (37/64:ℝ) (297/512:ℝ)
    (297/512:ℝ) (11858841173/100000000000000:ℝ) (-28974216979406574014411/12500000000000000000000000:ℝ) (4055210198080225498853/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_296
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0889).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_296 :
    (∫ x in (37/64:ℝ)..(297/512:ℝ), x^6*thetaFirstMode x) ≤ (2226004681862269/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (37/64:ℝ) (297/512:ℝ)
    (6159707157/50000000000000:ℝ) (11858879009/100000000000000:ℝ) (4055210198080225498853/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_296 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0889).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_297 :
    (1749065532889621/200000000000000000000000:ℝ) ≤ ∫ x in (297/512:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5793086257565909963694339053/2500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (297/512:ℝ) (149/256:ℝ)-(3161110456538910701793/5449291680715587228160:ℝ)*thetaPowerMass 6 (297/512:ℝ) (149/256:ℝ)) ≤
      thetaFirstModeFirst (3161110456538910701793/5449291680715587228160:ℝ)*(thetaPowerMass 7 (297/512:ℝ) (149/256:ℝ)-(3161110456538910701793/5449291680715587228160:ℝ)*thetaPowerMass 6 (297/512:ℝ) (149/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0450.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (297/512:ℝ) (149/256:ℝ)
    (3161110456538910701793/5449291680715587228160:ℝ) (5927388593/50000000000000:ℝ) (-5793086257565909963694339053/2500000000000000000000000000000:ℝ) (7872608189018256901441/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_297
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0893).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_297 :
    (∫ x in (297/512:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x) ≤ (273294109005123/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (297/512:ℝ) (149/256:ℝ)
    (11858879009/100000000000000:ℝ) (5706907043/50000000000000:ℝ) (7872608189018256901441/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_297 (thetaFirstMode_refined_node_0889).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_298 :
    (4293837778750613/500000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(299/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5410391551783959098553/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (149/256:ℝ) (299/512:ℝ)-(299/512:ℝ)*thetaPowerMass 6 (149/256:ℝ) (299/512:ℝ)) ≤
      thetaFirstModeFirst (299/512:ℝ)*(thetaPowerMass 7 (149/256:ℝ) (299/512:ℝ)-(299/512:ℝ)*thetaPowerMass 6 (149/256:ℝ) (299/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0452.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (149/256:ℝ) (299/512:ℝ)
    (299/512:ℝ) (549186531/5000000000000:ℝ) (-5410391551783959098553/2500000000000000000000000:ℝ) (19101430668175905514963/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_298
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0895).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_298 :
    (∫ x in (149/256:ℝ)..(299/512:ℝ), x^6*thetaFirstMode x) ≤ (8587731192585601/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (149/256:ℝ) (299/512:ℝ)
    (5706907043/50000000000000:ℝ) (5491882969/50000000000000:ℝ) (19101430668175905514963/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_298 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0895).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_299 :
    (1686189288112861/200000000000000000000000:ℝ) ≤ ∫ x in (299/512:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-540874737123784668989891397/250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (299/512:ℝ) (75/128:ℝ)-(3357929197679323400991/5749861108172310146560:ℝ)*thetaPowerMass 6 (299/512:ℝ) (75/128:ℝ)) ≤
      thetaFirstModeFirst (3357929197679323400991/5749861108172310146560:ℝ)*(thetaPowerMass 7 (299/512:ℝ) (75/128:ℝ)-(3357929197679323400991/5749861108172310146560:ℝ)*thetaPowerMass 6 (299/512:ℝ) (75/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0453.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (299/512:ℝ) (75/128:ℝ)
    (3357929197679323400991/5749861108172310146560:ℝ) (343123801/3125000000000:ℝ) (-540874737123784668989891397/250000000000000000000000000000:ℝ) (7414209652781484338813/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_299
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0899).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_299 :
    (∫ x in (299/512:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x) ≤ (1686205792447299/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (299/512:ℝ) (75/128:ℝ)
    (5491882969/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (7414209652781484338813/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_299 (thetaFirstMode_refined_node_0895).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_300 :
    (8275299788866267/1000000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(301/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-807731860217241891219/400000000000000000000000:ℝ)*(thetaPowerMass 7 (75/128:ℝ) (301/512:ℝ)-(301/512:ℝ)*thetaPowerMass 6 (75/128:ℝ) (301/512:ℝ)) ≤
      thetaFirstModeFirst (301/512:ℝ)*(thetaPowerMass 7 (75/128:ℝ) (301/512:ℝ)-(301/512:ℝ)*thetaPowerMass 6 (75/128:ℝ) (301/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0455.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (75/128:ℝ) (301/512:ℝ)
    (301/512:ℝ) (406677099/4000000000000:ℝ) (-807731860217241891219/400000000000000000000000:ℝ) (35967090775677729233607/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_300
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0901).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_300 :
    (∫ x in (75/128:ℝ)..(301/512:ℝ), x^6*thetaFirstMode x) ≤ (8275354359220047/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (75/128:ℝ) (301/512:ℝ)
    (5284145987/50000000000000:ℝ) (1270870053/12500000000000:ℝ) (35967090775677729233607/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_300 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0901).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_301 :
    (4060337101213093/500000000000000000000000:ℝ) ≤ ∫ x in (301/512:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-10093573080502129060895716469/5000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (301/512:ℝ) (151/256:ℝ)-(3565566396780466626009/6064838098423837058560:ℝ)*thetaPowerMass 6 (301/512:ℝ) (151/256:ℝ)) ≤
      thetaFirstModeFirst (3565566396780466626009/6064838098423837058560:ℝ)*(thetaPowerMass 7 (301/512:ℝ) (151/256:ℝ)-(3565566396780466626009/6064838098423837058560:ℝ)*thetaPowerMass 6 (301/512:ℝ) (151/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0456.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (301/512:ℝ) (151/256:ℝ)
    (3565566396780466626009/6064838098423837058560:ℝ) (10163434077/100000000000000:ℝ) (-10093573080502129060895716469/5000000000000000000000000000000:ℝ) (8722620487668306256711/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_301
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0905).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_301 :
    (∫ x in (301/512:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x) ≤ (8120755375455359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (301/512:ℝ) (151/256:ℝ)
    (1270870053/12500000000000:ℝ) (76401173/781250000000:ℝ) (8722620487668306256711/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_301 (thetaFirstMode_refined_node_0901).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_302 :
    (7967224941091277/1000000000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(303/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2942220590874869405973/1562500000000000000000000:ℝ)*(thetaPowerMass 7 (151/256:ℝ) (303/512:ℝ)-(303/512:ℝ)*thetaPowerMass 6 (151/256:ℝ) (303/512:ℝ)) ≤
      thetaFirstModeFirst (303/512:ℝ)*(thetaPowerMass 7 (151/256:ℝ) (303/512:ℝ)-(303/512:ℝ)*thetaPowerMass 6 (151/256:ℝ) (303/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0458.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (151/256:ℝ) (303/512:ℝ)
    (303/512:ℝ) (1175627463/12500000000000:ℝ) (-2942220590874869405973/1562500000000000000000000:ℝ) (8460179755947246822237/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_302
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0907).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_302 :
    (∫ x in (151/256:ℝ)..(303/512:ℝ), x^6*thetaFirstMode x) ≤ (398363921163871/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (151/256:ℝ) (303/512:ℝ)
    (76401173/781250000000:ℝ) (9405050423/100000000000000:ℝ) (8460179755947246822237/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_302 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0907).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_303 :
    (7814888547515777/1000000000000000000000000:ℝ) ≤ ∫ x in (303/512:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x := by
  have hd : (-94122317810661185087674224321/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (303/512:ℝ) (19/32:ℝ)-(3784538847414433095207/6394810604163109788160:ℝ)*thetaPowerMass 6 (303/512:ℝ) (19/32:ℝ)) ≤
      thetaFirstModeFirst (3784538847414433095207/6394810604163109788160:ℝ)*(thetaPowerMass 7 (303/512:ℝ) (19/32:ℝ)-(3784538847414433095207/6394810604163109788160:ℝ)*thetaPowerMass 6 (303/512:ℝ) (19/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0459.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (303/512:ℝ) (19/32:ℝ)
    (3784538847414433095207/6394810604163109788160:ℝ) (9401783617/100000000000000:ℝ) (-94122317810661185087674224321/50000000000000000000000000000000:ℝ) (16408651743486612312083/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_303
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0911).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_303 :
    (∫ x in (303/512:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x) ≤ (7814968327710787/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (303/512:ℝ) (19/32:ℝ)
    (9405050423/100000000000000:ℝ) (9043660791/100000000000000:ℝ) (16408651743486612312083/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_303 (thetaFirstMode_refined_node_0907).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_304 :
    (59873562099131/7812500000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(305/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-87740585419504627457113/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (19/32:ℝ) (305/512:ℝ)-(305/512:ℝ)*thetaPowerMass 6 (19/32:ℝ) (305/512:ℝ)) ≤
      thetaFirstModeFirst (305/512:ℝ)*(thetaPowerMass 7 (19/32:ℝ) (305/512:ℝ)-(305/512:ℝ)*thetaPowerMass 6 (19/32:ℝ) (305/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0461.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (19/32:ℝ) (305/512:ℝ)
    (305/512:ℝ) (8694762209/100000000000000:ℝ) (-87740585419504627457113/50000000000000000000000000:ℝ) (15909870597333041190103/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_304
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0913).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_304 :
    (∫ x in (19/32:ℝ)..(305/512:ℝ), x^6*thetaFirstMode x) ≤ (3831934160610773/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/32:ℝ) (305/512:ℝ)
    (9043660791/100000000000000:ℝ) (8694790831/100000000000000:ℝ) (15909870597333041190103/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_304 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0913).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_305 :
    (1878485422937981/250000000000000000000000:ℝ) ≤ ∫ x in (305/512:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-8771373944516178740516536187/5000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (305/512:ℝ) (153/256:ℝ)-(803076872185116228645/1348077287675556311552:ℝ)*thetaPowerMass 6 (305/512:ℝ) (153/256:ℝ)) ≤
      thetaFirstModeFirst (803076872185116228645/1348077287675556311552:ℝ)*(thetaPowerMass 7 (305/512:ℝ) (153/256:ℝ)-(803076872185116228645/1348077287675556311552:ℝ)*thetaPowerMass 6 (305/512:ℝ) (153/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0462.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (305/512:ℝ) (153/256:ℝ)
    (803076872185116228645/1348077287675556311552:ℝ) (1086470779/12500000000000:ℝ) (-8771373944516178740516536187/5000000000000000000000000000000:ℝ) (30847542448055080598143/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_305
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0917).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_305 :
    (∫ x in (305/512:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x) ≤ (7514020037452377/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (305/512:ℝ) (153/256:ℝ)
    (8694790831/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30847542448055080598143/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_305 (thetaFirstMode_refined_node_0913).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_306 :
    (7365412265100297/1000000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(307/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-25535894612032480833/15625000000000000000000:ℝ)*(thetaPowerMass 7 (153/256:ℝ) (307/512:ℝ)-(307/512:ℝ)*thetaPowerMass 6 (153/256:ℝ) (307/512:ℝ)) ≤
      thetaFirstModeFirst (307/512:ℝ)*(thetaPowerMass 7 (153/256:ℝ) (307/512:ℝ)-(307/512:ℝ)*thetaPowerMass 6 (153/256:ℝ) (307/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0464.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (153/256:ℝ) (307/512:ℝ)
    (307/512:ℝ) (12551673/156250000000:ℝ) (-25535894612032480833/15625000000000000000000:ℝ) (14950111052747826858571/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_306
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0919).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_306 :
    (∫ x in (153/256:ℝ)..(307/512:ℝ), x^6*thetaFirstMode x) ≤ (460341469337111/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (153/256:ℝ) (307/512:ℝ)
    (522378749/6250000000000:ℝ) (8033097371/100000000000000:ℝ) (14950111052747826858571/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_306 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0919).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_307 :
    (1804540074164387/250000000000000000000000:ℝ) ≤ ∫ x in (307/512:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-20422450499662123467388661867/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (307/512:ℝ) (77/128:ℝ)-(4258662473983944316743/7102193807453257500160:ℝ)*thetaPowerMass 6 (307/512:ℝ) (77/128:ℝ)) ≤
      thetaFirstModeFirst (4258662473983944316743/7102193807453257500160:ℝ)*(thetaPowerMass 7 (307/512:ℝ) (77/128:ℝ)-(4258662473983944316743/7102193807453257500160:ℝ)*thetaPowerMass 6 (307/512:ℝ) (77/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0465.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (307/512:ℝ) (77/128:ℝ)
    (4258662473983944316743/7102193807453257500160:ℝ) (8030298673/100000000000000:ℝ) (-20422450499662123467388661867/12500000000000000000000000000000:ℝ) (452770307138013511551/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_307
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0923).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_307 :
    (∫ x in (307/512:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x) ≤ (1443647433809157/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (307/512:ℝ) (77/128:ℝ)
    (8033097371/100000000000000:ℝ) (7719541601/100000000000000:ℝ) (452770307138013511551/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_307 (thetaFirstMode_refined_node_0919).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_308 :
    (7072327746209799/1000000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(309/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-3802722657758633698493/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (77/128:ℝ) (309/512:ℝ)-(309/512:ℝ)*thetaPowerMass 6 (77/128:ℝ) (309/512:ℝ)) ≤
      thetaFirstModeFirst (309/512:ℝ)*(thetaPowerMass 7 (77/128:ℝ) (309/512:ℝ)-(309/512:ℝ)*thetaPowerMass 6 (77/128:ℝ) (309/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0467.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (77/128:ℝ) (309/512:ℝ)
    (309/512:ℝ) (741701579/10000000000000:ℝ) (-3802722657758633698493/2500000000000000000000000:ℝ) (28078299312739342725291/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_308
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0925).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_308 :
    (∫ x in (77/128:ℝ)..(309/512:ℝ), x^6*thetaFirstMode x) ≤ (7072377845762759/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (77/128:ℝ) (309/512:ℝ)
    (7719541601/100000000000000:ℝ) (741704059/10000000000000:ℝ) (28078299312739342725291/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_308 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0925).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_309 :
    (865980675910917/125000000000000000000000:ℝ) ≤ ∫ x in (309/512:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-15206214611497358587433543671/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (309/512:ℝ) (155/256:ℝ)-(4514955175067537709441/7480881854937014095360:ℝ)*thetaPowerMass 6 (309/512:ℝ) (155/256:ℝ)) ≤
      thetaFirstModeFirst (4514955175067537709441/7480881854937014095360:ℝ)*(thetaPowerMass 7 (309/512:ℝ) (155/256:ℝ)-(4514955175067537709441/7480881854937014095360:ℝ)*thetaPowerMass 6 (309/512:ℝ) (155/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0468.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (309/512:ℝ) (155/256:ℝ)
    (4514955175067537709441/7480881854937014095360:ℝ) (3707226231/50000000000000:ℝ) (-15206214611497358587433543671/10000000000000000000000000000000:ℝ) (27202750094728656016807/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_309
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0929).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_309 :
    (∫ x in (309/512:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x) ≤ (6927920770862011/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (309/512:ℝ) (155/256:ℝ)
    (741704059/10000000000000:ℝ) (7125251383/100000000000000:ℝ) (27202750094728656016807/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_309 (thetaFirstMode_refined_node_0925).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_310 :
    (3392425319506959/500000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(311/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-17685166475982467418957/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (155/256:ℝ) (311/512:ℝ)-(311/512:ℝ)*thetaPowerMass 6 (155/256:ℝ) (311/512:ℝ)) ≤
      thetaFirstModeFirst (311/512:ℝ)*(thetaPowerMass 7 (155/256:ℝ) (311/512:ℝ)-(311/512:ℝ)*thetaPowerMass 6 (155/256:ℝ) (311/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0470.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (155/256:ℝ) (311/512:ℝ)
    (311/512:ℝ) (6843816903/100000000000000:ℝ) (-17685166475982467418957/12500000000000000000000000:ℝ) (13175092945756406544489/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_310
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0931).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_310 :
    (∫ x in (155/256:ℝ)..(311/512:ℝ), x^6*thetaFirstMode x) ≤ (6784899578889559/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (155/256:ℝ) (311/512:ℝ)
    (7125251383/100000000000000:ℝ) (3421919983/50000000000000:ℝ) (13175092945756406544489/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_310 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0931).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_311 :
    (6643272490945143/1000000000000000000000000:ℝ) ≤ ∫ x in (311/512:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1767971676692178932262396061/1250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (311/512:ℝ) (39/64:ℝ)-(4784867650250851000959/7877121216105401397760:ℝ)*thetaPowerMass 6 (311/512:ℝ) (39/64:ℝ)) ≤
      thetaFirstModeFirst (4784867650250851000959/7877121216105401397760:ℝ)*(thetaPowerMass 7 (311/512:ℝ) (39/64:ℝ)-(4784867650250851000959/7877121216105401397760:ℝ)*thetaPowerMass 6 (311/512:ℝ) (39/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0471.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (311/512:ℝ) (39/64:ℝ)
    (4784867650250851000959/7877121216105401397760:ℝ) (3420724001/50000000000000:ℝ) (-1767971676692178932262396061/1250000000000000000000000000000:ℝ) (5104029109918624195953/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_311
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0935).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_311 :
    (∫ x in (311/512:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x) ≤ (6643346312780681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (311/512:ℝ) (39/64:ℝ)
    (3421919983/50000000000000:ℝ) (6572481097/100000000000000:ℝ) (5104029109918624195953/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_311 (thetaFirstMode_refined_node_0931).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_312 :
    (260129746590203/40000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(313/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4109721395284074488977/3125000000000000000000000:ℝ)*(thetaPowerMass 7 (39/64:ℝ) (313/512:ℝ)-(313/512:ℝ)*thetaPowerMass 6 (39/64:ℝ) (313/512:ℝ)) ≤
      thetaFirstModeFirst (313/512:ℝ)*(thetaPowerMass 7 (39/64:ℝ) (313/512:ℝ)-(313/512:ℝ)*thetaPowerMass 6 (39/64:ℝ) (313/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0473.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (39/64:ℝ) (313/512:ℝ)
    (313/512:ℝ) (1577709173/25000000000000:ℝ) (-4109721395284074488977/3125000000000000000000000:ℝ) (24712172933868604341027/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_312
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0937).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_312 :
    (∫ x in (39/64:ℝ)..(313/512:ℝ), x^6*thetaFirstMode x) ≤ (1625822858150233/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (39/64:ℝ) (313/512:ℝ)
    (6572481097/100000000000000:ℝ) (3155429063/50000000000000:ℝ) (24712172933868604341027/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_312 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0937).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_313 :
    (6364691569484483/1000000000000000000000000:ℝ) ≤ ∫ x in (313/512:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2629409213222150471003489169/2000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (313/512:ℝ) (157/256:ℝ)-(5069029048681798692657/8291604583475060892160:ℝ)*thetaPowerMass 6 (313/512:ℝ) (157/256:ℝ)) ≤
      thetaFirstModeFirst (5069029048681798692657/8291604583475060892160:ℝ)*(thetaPowerMass 7 (313/512:ℝ) (157/256:ℝ)-(5069029048681798692657/8291604583475060892160:ℝ)*thetaPowerMass 6 (313/512:ℝ) (157/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0474.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (313/512:ℝ) (157/256:ℝ)
    (5069029048681798692657/8291604583475060892160:ℝ) (3154324399/50000000000000:ℝ) (-2629409213222150471003489169/2000000000000000000000000000000:ℝ) (23925816996024384782671/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_313
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0941).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_313 :
    (∫ x in (313/512:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x) ≤ (1591190955240099/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (313/512:ℝ) (157/256:ℝ)
    (3155429063/50000000000000:ℝ) (302933141/5000000000000:ℝ) (23925816996024384782671/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_313 (thetaFirstMode_refined_node_0937).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_314 :
    (194617006474307/31250000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(315/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-15270460090085434897621/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (157/256:ℝ) (315/512:ℝ)-(315/512:ℝ)*thetaPowerMass 6 (157/256:ℝ) (315/512:ℝ)) ≤
      thetaFirstModeFirst (315/512:ℝ)*(thetaPowerMass 7 (157/256:ℝ) (315/512:ℝ)-(315/512:ℝ)*thetaPowerMass 6 (157/256:ℝ) (315/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0476.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (157/256:ℝ) (315/512:ℝ)
    (315/512:ℝ) (2907787643/50000000000000:ℝ) (-15270460090085434897621/12500000000000000000000000:ℝ) (2895078978439768447953/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_314
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0943).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_314 :
    (∫ x in (157/256:ℝ)..(315/512:ℝ), x^6*thetaFirstMode x) ≤ (3113895396371043/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (157/256:ℝ) (315/512:ℝ)
    (302933141/5000000000000:ℝ) (5815595193/100000000000000:ℝ) (2895078978439768447953/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_314 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0943).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_315 :
    (6092327451565331/1000000000000000000000000:ℝ) ≤ ∫ x in (315/512:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-190821642355199244379493817/156250000000000000000000000000:ℝ)*(thetaPowerMass 7 (315/512:ℝ) (79/128:ℝ)-(1073618653626882244035/1745009456680404157952:ℝ)*thetaPowerMass 6 (315/512:ℝ) (79/128:ℝ)) ≤
      thetaFirstModeFirst (1073618653626882244035/1745009456680404157952:ℝ)*(thetaPowerMass 7 (315/512:ℝ) (79/128:ℝ)-(1073618653626882244035/1745009456680404157952:ℝ)*thetaPowerMass 6 (315/512:ℝ) (79/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0477.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (315/512:ℝ) (79/128:ℝ)
    (1073618653626882244035/1745009456680404157952:ℝ) (1453388951/25000000000000:ℝ) (-190821642355199244379493817/156250000000000000000000000000:ℝ) (22416176724474318852911/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_315
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0947).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_315 :
    (∫ x in (315/512:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x) ≤ (609239810574299/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (315/512:ℝ) (79/128:ℝ)
    (5815595193/100000000000000:ℝ) (2790681667/50000000000000:ℝ) (22416176724474318852911/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_315 (thetaFirstMode_refined_node_0943).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_316 :
    (2979282289634667/500000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(317/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-56703018631762541438073/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (79/128:ℝ) (317/512:ℝ)-(317/512:ℝ)*thetaPowerMass 6 (79/128:ℝ) (317/512:ℝ)) ≤
      thetaFirstModeFirst (317/512:ℝ)*(thetaPowerMass 7 (79/128:ℝ) (317/512:ℝ)-(317/512:ℝ)*thetaPowerMass 6 (79/128:ℝ) (317/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0479.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (79/128:ℝ) (317/512:ℝ)
    (317/512:ℝ) (5355664767/100000000000000:ℝ) (-56703018631762541438073/50000000000000000000000000:ℝ) (10846008116516652901023/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_316
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0949).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_316 :
    (∫ x in (79/128:ℝ)..(317/512:ℝ), x^6*thetaFirstMode x) ≤ (1191721994862733/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (79/128:ℝ) (317/512:ℝ)
    (2790681667/50000000000000:ℝ) (1338920811/25000000000000:ℝ) (10846008116516652901023/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_316 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0949).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_317 :
    (1456595011554597/250000000000000000000000:ℝ) ≤ ∫ x in (317/512:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-7085676996472660790182265029/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (317/512:ℝ) (159/256:ℝ)-(5682739761029596469193/9178187863912459548160:ℝ)*thetaPowerMass 6 (317/512:ℝ) (159/256:ℝ)) ≤
      thetaFirstModeFirst (5682739761029596469193/9178187863912459548160:ℝ)*(thetaPowerMass 7 (317/512:ℝ) (159/256:ℝ)-(5682739761029596469193/9178187863912459548160:ℝ)*thetaPowerMass 6 (317/512:ℝ) (159/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0480.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (317/512:ℝ) (159/256:ℝ)
    (5682739761029596469193/9178187863912459548160:ℝ) (1070760377/20000000000000:ℝ) (-7085676996472660790182265029/6250000000000000000000000000000:ℝ) (1311732513438111663089/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_317
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0953).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_317 :
    (∫ x in (317/512:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x) ≤ (5826449079990907/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (317/512:ℝ) (159/256:ℝ)
    (1338920811/25000000000000:ℝ) (256913933/5000000000000:ℝ) (1311732513438111663089/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_317 (thetaFirstMode_refined_node_0949).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_318 :
    (227835695558099/40000000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(319/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-10520644050624667452087/10000000000000000000000000:ℝ)*(thetaPowerMass 7 (159/256:ℝ) (319/512:ℝ)-(319/512:ℝ)*thetaPowerMass 6 (159/256:ℝ) (319/512:ℝ)) ≤
      thetaFirstModeFirst (319/512:ℝ)*(thetaPowerMass 7 (159/256:ℝ) (319/512:ℝ)-(319/512:ℝ)*thetaPowerMass 6 (159/256:ℝ) (319/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0482.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (159/256:ℝ) (319/512:ℝ)
    (319/512:ℝ) (985772753/20000000000000:ℝ) (-10520644050624667452087/10000000000000000000000000:ℝ) (20302863861096708719893/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_318
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0955).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_318 :
    (∫ x in (159/256:ℝ)..(319/512:ℝ), x^6*thetaFirstMode x) ≤ (5695936587072167/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (159/256:ℝ) (319/512:ℝ)
    (256913933/5000000000000:ℝ) (4928880903/100000000000000:ℝ) (20302863861096708719893/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_318 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0955).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_319 :
    (5567024765701019/1000000000000000000000000:ℝ) ≤ ∫ x in (319/512:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x := by
  have hd : (-3286678066500038985541107551/3125000000000000000000000000000:ℝ)*(thetaPowerMass 7 (319/512:ℝ) (5/8:ℝ)-(6013674361321379726391/9651788693910057372160:ℝ)*thetaPowerMass 6 (319/512:ℝ) (5/8:ℝ)) ≤
      thetaFirstModeFirst (6013674361321379726391/9651788693910057372160:ℝ)*(thetaPowerMass 7 (319/512:ℝ) (5/8:ℝ)-(6013674361321379726391/9651788693910057372160:ℝ)*thetaPowerMass 6 (319/512:ℝ) (5/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0483.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (319/512:ℝ) (5/8:ℝ)
    (6013674361321379726391/9651788693910057372160:ℝ) (492714641/10000000000000:ℝ) (-3286678066500038985541107551/3125000000000000000000000000000:ℝ) (981851388666244180191/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_319
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0959).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_319 :
    (∫ x in (319/512:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x) ≤ (5567092158240737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (319/512:ℝ) (5/8:ℝ)
    (4928880903/100000000000000:ℝ) (147725897/3125000000000:ℝ) (981851388666244180191/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_319 (thetaFirstMode_refined_node_0955).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
