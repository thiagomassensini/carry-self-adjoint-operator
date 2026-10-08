import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature09
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative13
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative14
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative15

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_4_288 :
    (16062184376099357/500000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(289/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-75796730715399661167193/25000000000000000000000000:ℝ)*(thetaPowerMass 5 (9/16:ℝ) (289/512:ℝ)-(289/512:ℝ)*thetaPowerMass 4 (9/16:ℝ) (289/512:ℝ)) ≤
      thetaFirstModeFirst (289/512:ℝ)*(thetaPowerMass 5 (9/16:ℝ) (289/512:ℝ)-(289/512:ℝ)*thetaPowerMass 4 (9/16:ℝ) (289/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0437.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (9/16:ℝ) (289/512:ℝ)
    (289/512:ℝ) (8008395751/50000000000000:ℝ) (-75796730715399661167193/25000000000000000000000000:ℝ) (25583653603413205650409/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_288
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0865).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_288 :
    (∫ x in (9/16:ℝ)..(289/512:ℝ), x^4*thetaFirstMode x) ≤ (4015569942455983/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (9/16:ℝ) (289/512:ℝ)
    (2077357167/12500000000000:ℝ) (16016841031/100000000000000:ℝ) (25583653603413205650409/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_288 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0865).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_289 :
    (7847441415782057/250000000000000000000000:ℝ) ≤ ∫ x in (289/512:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-37886970455235311976951301697/12500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (289/512:ℝ) (145/256:ℝ)-(2472381744748202416041/4379996680278775605760:ℝ)*thetaPowerMass 4 (289/512:ℝ) (145/256:ℝ)) ≤
      thetaFirstModeFirst (2472381744748202416041/4379996680278775605760:ℝ)*(thetaPowerMass 5 (289/512:ℝ) (145/256:ℝ)-(2472381744748202416041/4379996680278775605760:ℝ)*thetaPowerMass 4 (289/512:ℝ) (145/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0438.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (289/512:ℝ) (145/256:ℝ)
    (2472381744748202416041/4379996680278775605760:ℝ) (8005664329/50000000000000:ℝ) (-37886970455235311976951301697/12500000000000000000000000000000:ℝ) (24864114131483293224261/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_289
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0869).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_289 :
    (∫ x in (289/512:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x) ≤ (6278008456401279/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (289/512:ℝ) (145/256:ℝ)
    (16016841031/100000000000000:ℝ) (3086868927/20000000000000:ℝ) (24864114131483293224261/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_289 (thetaFirstMode_refined_node_0865).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_290 :
    (7666528857308383/250000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(291/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-14187983494351461946011/5000000000000000000000000:ℝ)*(thetaPowerMass 5 (145/256:ℝ) (291/512:ℝ)-(291/512:ℝ)*thetaPowerMass 4 (145/256:ℝ) (291/512:ℝ)) ≤
      thetaFirstModeFirst (291/512:ℝ)*(thetaPowerMass 5 (145/256:ℝ) (291/512:ℝ)-(291/512:ℝ)*thetaPowerMass 4 (145/256:ℝ) (291/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0440.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (145/256:ℝ) (291/512:ℝ)
    (291/512:ℝ) (14870772819/100000000000000:ℝ) (-14187983494351461946011/5000000000000000000000000:ℝ) (12080569058620188148461/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_290
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0871).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_290 :
    (∫ x in (145/256:ℝ)..(291/512:ℝ), x^4*thetaFirstMode x) ≤ (7666575185994517/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (145/256:ℝ) (291/512:ℝ)
    (3086868927/20000000000000:ℝ) (2974163833/20000000000000:ℝ) (12080569058620188148461/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_290 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0871).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_291 :
    (14976545081858121/500000000000000000000000:ℝ) ≤ ∫ x in (291/512:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1772963598784072678930509591/625000000000000000000000000000:ℝ)*(thetaPowerMass 5 (291/512:ℝ) (73/128:ℝ)-(2630697969772508777559/4628436250915918927360:ℝ)*thetaPowerMass 4 (291/512:ℝ) (73/128:ℝ)) ≤
      thetaFirstModeFirst (2630697969772508777559/4628436250915918927360:ℝ)*(thetaPowerMass 5 (291/512:ℝ) (73/128:ℝ)-(2630697969772508777559/4628436250915918927360:ℝ)*thetaPowerMass 4 (291/512:ℝ) (73/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0441.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (291/512:ℝ) (73/128:ℝ)
    (2630697969772508777559/4628436250915918927360:ℝ) (14865695153/100000000000000:ℝ) (-1772963598784072678930509591/625000000000000000000000000000:ℝ) (46948909398942769942027/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_291
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0875).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_291 :
    (∫ x in (291/512:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x) ≤ (187208497827287/6250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (291/512:ℝ) (73/128:ℝ)
    (2974163833/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (46948909398942769942027/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_291 (thetaFirstMode_refined_node_0871).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_292 :
    (29251057372188519/1000000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(293/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-33177269885165861903363/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (73/128:ℝ) (293/512:ℝ)-(293/512:ℝ)*thetaPowerMass 4 (73/128:ℝ) (293/512:ℝ)) ≤
      thetaFirstModeFirst (293/512:ℝ)*(thetaPowerMass 5 (73/128:ℝ) (293/512:ℝ)-(293/512:ℝ)*thetaPowerMass 4 (73/128:ℝ) (293/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0443.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (73/128:ℝ) (293/512:ℝ)
    (293/512:ℝ) (6899252351/50000000000000:ℝ) (-33177269885165861903363/12500000000000000000000000:ℝ) (45607588912752387150693/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_292
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0877).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_292 :
    (∫ x in (73/128:ℝ)..(293/512:ℝ), x^4*thetaFirstMode x) ≤ (5850247448828691/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (73/128:ℝ) (293/512:ℝ)
    (14325728273/100000000000000:ℝ) (3449637011/25000000000000:ℝ) (45607588912752387150693/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_292 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0877).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_293 :
    (713992076366727/25000000000000000000000:ℝ) ≤ ∫ x in (293/512:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-6633450580908118564124625927/2500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (293/512:ℝ) (147/256:ℝ)-(2797962146921232130257/4889119879777782300160:ℝ)*thetaPowerMass 4 (293/512:ℝ) (147/256:ℝ)) ≤
      thetaFirstModeFirst (2797962146921232130257/4889119879777782300160:ℝ)*(thetaPowerMass 5 (293/512:ℝ) (147/256:ℝ)-(2797962146921232130257/4889119879777782300160:ℝ)*thetaPowerMass 4 (293/512:ℝ) (147/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0444.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (293/512:ℝ) (147/256:ℝ)
    (2797962146921232130257/4889119879777782300160:ℝ) (6896893831/50000000000000:ℝ) (-6633450580908118564124625927/2500000000000000000000000000000:ℝ) (22148889472059177758597/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_293
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0881).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_293 :
    (∫ x in (293/512:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x) ≤ (28559945403763329/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (293/512:ℝ) (147/256:ℝ)
    (3449637011/25000000000000:ℝ) (6644383393/50000000000000:ℝ) (22148889472059177758597/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_293 (thetaFirstMode_refined_node_0877).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_294 :
    (6969828834336461/250000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(295/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-387675493896549856977/156250000000000000000000:ℝ)*(thetaPowerMass 5 (147/256:ℝ) (295/512:ℝ)-(295/512:ℝ)*thetaPowerMass 4 (147/256:ℝ) (295/512:ℝ)) ≤
      thetaFirstModeFirst (295/512:ℝ)*(thetaPowerMass 5 (147/256:ℝ) (295/512:ℝ)-(295/512:ℝ)*thetaPowerMass 4 (147/256:ℝ) (295/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0446.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (147/256:ℝ) (295/512:ℝ)
    (295/512:ℝ) (79974027/625000000000:ℝ) (-387675493896549856977/156250000000000000000000:ℝ) (43018946814087568901247/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_294
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0883).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_294 :
    (∫ x in (147/256:ℝ)..(295/512:ℝ), x^4*thetaFirstMode x) ≤ (27879489799236631/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (147/256:ℝ) (295/512:ℝ)
    (6644383393/50000000000000:ℝ) (12795884827/100000000000000:ℝ) (43018946814087568901247/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_294 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0883).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_295 :
    (5441922962900327/200000000000000000000000:ℝ) ≤ ∫ x in (295/512:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x := by
  have hd : (-7751163915930783169895100477/3125000000000000000000000000000:ℝ)*(thetaPowerMass 5 (295/512:ℝ) (37/64:ℝ)-(594922741712509294755/1032512240214680279552:ℝ)*thetaPowerMass 4 (295/512:ℝ) (37/64:ℝ)) ≤
      thetaFirstModeFirst (594922741712509294755/1032512240214680279552:ℝ)*(thetaPowerMass 5 (295/512:ℝ) (37/64:ℝ)-(594922741712509294755/1032512240214680279552:ℝ)*thetaPowerMass 4 (295/512:ℝ) (37/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0447.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (295/512:ℝ) (37/64:ℝ)
    (594922741712509294755/1032512240214680279552:ℝ) (12791464733/100000000000000:ℝ) (-7751163915930783169895100477/3125000000000000000000000000000:ℝ) (41770563139424439673057/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_295
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0887).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_295 :
    (∫ x in (295/512:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x) ≤ (13604935013570397/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (295/512:ℝ) (37/64:ℝ)
    (12795884827/100000000000000:ℝ) (6159707157/50000000000000:ℝ) (41770563139424439673057/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_295 (thetaFirstMode_refined_node_0883).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_296 :
    (5310182132157723/200000000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(297/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-28974216979406574014411/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (37/64:ℝ) (297/512:ℝ)-(297/512:ℝ)*thetaPowerMass 4 (37/64:ℝ) (297/512:ℝ)) ≤
      thetaFirstModeFirst (297/512:ℝ)*(thetaPowerMass 5 (37/64:ℝ) (297/512:ℝ)-(297/512:ℝ)*thetaPowerMass 4 (37/64:ℝ) (297/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0449.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (37/64:ℝ) (297/512:ℝ)
    (297/512:ℝ) (11858841173/100000000000000:ℝ) (-28974216979406574014411/12500000000000000000000000:ℝ) (4055210198080225498853/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_296
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0889).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_296 :
    (∫ x in (37/64:ℝ)..(297/512:ℝ), x^4*thetaFirstMode x) ≤ (26551079755950937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (37/64:ℝ) (297/512:ℝ)
    (6159707157/50000000000000:ℝ) (11858879009/100000000000000:ℝ) (4055210198080225498853/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_296 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0889).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_297 :
    (12951429388142319/500000000000000000000000:ℝ) ≤ ∫ x in (297/512:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-5793086257565909963694339053/2500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (297/512:ℝ) (149/256:ℝ)-(3161110456538910701793/5449291680715587228160:ℝ)*thetaPowerMass 4 (297/512:ℝ) (149/256:ℝ)) ≤
      thetaFirstModeFirst (3161110456538910701793/5449291680715587228160:ℝ)*(thetaPowerMass 5 (297/512:ℝ) (149/256:ℝ)-(3161110456538910701793/5449291680715587228160:ℝ)*thetaPowerMass 4 (297/512:ℝ) (149/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0450.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (297/512:ℝ) (149/256:ℝ)
    (3161110456538910701793/5449291680715587228160:ℝ) (5927388593/50000000000000:ℝ) (-5793086257565909963694339053/2500000000000000000000000000000:ℝ) (7872608189018256901441/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_297
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0893).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_297 :
    (∫ x in (297/512:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x) ≤ (25903106865963409/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (297/512:ℝ) (149/256:ℝ)
    (11858879009/100000000000000:ℝ) (5706907043/50000000000000:ℝ) (7872608189018256901441/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_297 (thetaFirstMode_refined_node_0889).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_298 :
    (2526576982533987/100000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(299/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-5410391551783959098553/2500000000000000000000000:ℝ)*(thetaPowerMass 5 (149/256:ℝ) (299/512:ℝ)-(299/512:ℝ)*thetaPowerMass 4 (149/256:ℝ) (299/512:ℝ)) ≤
      thetaFirstModeFirst (299/512:ℝ)*(thetaPowerMass 5 (149/256:ℝ) (299/512:ℝ)-(299/512:ℝ)*thetaPowerMass 4 (149/256:ℝ) (299/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0452.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (149/256:ℝ) (299/512:ℝ)
    (299/512:ℝ) (549186531/5000000000000:ℝ) (-5410391551783959098553/2500000000000000000000000:ℝ) (19101430668175905514963/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_298
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0895).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_298 :
    (∫ x in (149/256:ℝ)..(299/512:ℝ), x^4*thetaFirstMode x) ≤ (25265933599715577/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (149/256:ℝ) (299/512:ℝ)
    (5706907043/50000000000000:ℝ) (5491882969/50000000000000:ℝ) (19101430668175905514963/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_298 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0895).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_299 :
    (4927859145152179/200000000000000000000000:ℝ) ≤ ∫ x in (299/512:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-540874737123784668989891397/250000000000000000000000000000:ℝ)*(thetaPowerMass 5 (299/512:ℝ) (75/128:ℝ)-(3357929197679323400991/5749861108172310146560:ℝ)*thetaPowerMass 4 (299/512:ℝ) (75/128:ℝ)) ≤
      thetaFirstModeFirst (3357929197679323400991/5749861108172310146560:ℝ)*(thetaPowerMass 5 (299/512:ℝ) (75/128:ℝ)-(3357929197679323400991/5749861108172310146560:ℝ)*thetaPowerMass 4 (299/512:ℝ) (75/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0453.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (299/512:ℝ) (75/128:ℝ)
    (3357929197679323400991/5749861108172310146560:ℝ) (343123801/3125000000000:ℝ) (-540874737123784668989891397/250000000000000000000000000000:ℝ) (7414209652781484338813/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_299
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0899).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_299 :
    (∫ x in (299/512:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x) ≤ (4927907342169047/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (299/512:ℝ) (75/128:ℝ)
    (5491882969/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (7414209652781484338813/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_299 (thetaFirstMode_refined_node_0895).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_300 :
    (24023729099415413/1000000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(301/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-807731860217241891219/400000000000000000000000:ℝ)*(thetaPowerMass 5 (75/128:ℝ) (301/512:ℝ)-(301/512:ℝ)*thetaPowerMass 4 (75/128:ℝ) (301/512:ℝ)) ≤
      thetaFirstModeFirst (301/512:ℝ)*(thetaPowerMass 5 (75/128:ℝ) (301/512:ℝ)-(301/512:ℝ)*thetaPowerMass 4 (75/128:ℝ) (301/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0455.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (75/128:ℝ) (301/512:ℝ)
    (301/512:ℝ) (406677099/4000000000000:ℝ) (-807731860217241891219/400000000000000000000000:ℝ) (35967090775677729233607/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_300
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0901).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_300 :
    (∫ x in (75/128:ℝ)..(301/512:ℝ), x^4*thetaFirstMode x) ≤ (750746487768631/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (75/128:ℝ) (301/512:ℝ)
    (5284145987/50000000000000:ℝ) (1270870053/12500000000000:ℝ) (35967090775677729233607/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_300 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0901).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_301 :
    (11709359298291201/500000000000000000000000:ℝ) ≤ ∫ x in (301/512:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-10093573080502129060895716469/5000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (301/512:ℝ) (151/256:ℝ)-(3565566396780466626009/6064838098423837058560:ℝ)*thetaPowerMass 4 (301/512:ℝ) (151/256:ℝ)) ≤
      thetaFirstModeFirst (3565566396780466626009/6064838098423837058560:ℝ)*(thetaPowerMass 5 (301/512:ℝ) (151/256:ℝ)-(3565566396780466626009/6064838098423837058560:ℝ)*thetaPowerMass 4 (301/512:ℝ) (151/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0456.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (301/512:ℝ) (151/256:ℝ)
    (3565566396780466626009/6064838098423837058560:ℝ) (10163434077/100000000000000:ℝ) (-10093573080502129060895716469/5000000000000000000000000000000:ℝ) (8722620487668306256711/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_301
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0905).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_301 :
    (∫ x in (301/512:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x) ≤ (11709476254426887/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (301/512:ℝ) (151/256:ℝ)
    (1270870053/12500000000000:ℝ) (76401173/781250000000:ℝ) (8722620487668306256711/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_301 (thetaFirstMode_refined_node_0901).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_302 :
    (2853067410450329/125000000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(303/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-2942220590874869405973/1562500000000000000000000:ℝ)*(thetaPowerMass 5 (151/256:ℝ) (303/512:ℝ)-(303/512:ℝ)*thetaPowerMass 4 (151/256:ℝ) (303/512:ℝ)) ≤
      thetaFirstModeFirst (303/512:ℝ)*(thetaPowerMass 5 (151/256:ℝ) (303/512:ℝ)-(303/512:ℝ)*thetaPowerMass 4 (151/256:ℝ) (303/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0458.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (151/256:ℝ) (303/512:ℝ)
    (303/512:ℝ) (1175627463/12500000000000:ℝ) (-2942220590874869405973/1562500000000000000000000:ℝ) (8460179755947246822237/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_302
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0907).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_302 :
    (∫ x in (151/256:ℝ)..(303/512:ℝ), x^4*thetaFirstMode x) ≤ (11412346292430289/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (151/256:ℝ) (303/512:ℝ)
    (76401173/781250000000:ℝ) (9405050423/100000000000000:ℝ) (8460179755947246822237/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_302 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0907).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_303 :
    (22240837239752341/1000000000000000000000000:ℝ) ≤ ∫ x in (303/512:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x := by
  have hd : (-94122317810661185087674224321/50000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (303/512:ℝ) (19/32:ℝ)-(3784538847414433095207/6394810604163109788160:ℝ)*thetaPowerMass 4 (303/512:ℝ) (19/32:ℝ)) ≤
      thetaFirstModeFirst (3784538847414433095207/6394810604163109788160:ℝ)*(thetaPowerMass 5 (303/512:ℝ) (19/32:ℝ)-(3784538847414433095207/6394810604163109788160:ℝ)*thetaPowerMass 4 (303/512:ℝ) (19/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0459.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (303/512:ℝ) (19/32:ℝ)
    (3784538847414433095207/6394810604163109788160:ℝ) (9401783617/100000000000000:ℝ) (-94122317810661185087674224321/50000000000000000000000000000000:ℝ) (16408651743486612312083/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_303
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0911).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_303 :
    (∫ x in (303/512:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x) ≤ (11120532059219141/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (303/512:ℝ) (19/32:ℝ)
    (9405050423/100000000000000:ℝ) (9043660791/100000000000000:ℝ) (16408651743486612312083/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_303 (thetaFirstMode_refined_node_0907).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_304 :
    (10833935249328141/500000000000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(305/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-87740585419504627457113/50000000000000000000000000:ℝ)*(thetaPowerMass 5 (19/32:ℝ) (305/512:ℝ)-(305/512:ℝ)*thetaPowerMass 4 (19/32:ℝ) (305/512:ℝ)) ≤
      thetaFirstModeFirst (305/512:ℝ)*(thetaPowerMass 5 (19/32:ℝ) (305/512:ℝ)-(305/512:ℝ)*thetaPowerMass 4 (19/32:ℝ) (305/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0461.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (19/32:ℝ) (305/512:ℝ)
    (305/512:ℝ) (8694762209/100000000000000:ℝ) (-87740585419504627457113/50000000000000000000000000:ℝ) (15909870597333041190103/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_304
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0913).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_304 :
    (∫ x in (19/32:ℝ)..(305/512:ℝ), x^4*thetaFirstMode x) ≤ (866720746155771/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (19/32:ℝ) (305/512:ℝ)
    (9043660791/100000000000000:ℝ) (8694790831/100000000000000:ℝ) (15909870597333041190103/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_304 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0913).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_305 :
    (5276320813228307/250000000000000000000000:ℝ) ≤ ∫ x in (305/512:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-8771373944516178740516536187/5000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (305/512:ℝ) (153/256:ℝ)-(803076872185116228645/1348077287675556311552:ℝ)*thetaPowerMass 4 (305/512:ℝ) (153/256:ℝ)) ≤
      thetaFirstModeFirst (803076872185116228645/1348077287675556311552:ℝ)*(thetaPowerMass 5 (305/512:ℝ) (153/256:ℝ)-(803076872185116228645/1348077287675556311552:ℝ)*thetaPowerMass 4 (305/512:ℝ) (153/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0462.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (305/512:ℝ) (153/256:ℝ)
    (803076872185116228645/1348077287675556311552:ℝ) (1086470779/12500000000000:ℝ) (-8771373944516178740516536187/5000000000000000000000000000000:ℝ) (30847542448055080598143/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_305
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0917).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_305 :
    (∫ x in (305/512:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x) ≤ (21105503144623517/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (305/512:ℝ) (153/256:ℝ)
    (8694790831/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30847542448055080598143/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_305 (thetaFirstMode_refined_node_0913).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_306 :
    (20553317029706207/1000000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(307/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-25535894612032480833/15625000000000000000000:ℝ)*(thetaPowerMass 5 (153/256:ℝ) (307/512:ℝ)-(307/512:ℝ)*thetaPowerMass 4 (153/256:ℝ) (307/512:ℝ)) ≤
      thetaFirstModeFirst (307/512:ℝ)*(thetaPowerMass 5 (153/256:ℝ) (307/512:ℝ)-(307/512:ℝ)*thetaPowerMass 4 (153/256:ℝ) (307/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0464.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (153/256:ℝ) (307/512:ℝ)
    (307/512:ℝ) (12551673/156250000000:ℝ) (-25535894612032480833/15625000000000000000000:ℝ) (14950111052747826858571/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_306
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0919).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_306 :
    (∫ x in (153/256:ℝ)..(307/512:ℝ), x^4*thetaFirstMode x) ≤ (4110692021568093/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (153/256:ℝ) (307/512:ℝ)
    (522378749/6250000000000:ℝ) (8033097371/100000000000000:ℝ) (14950111052747826858571/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_306 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0919).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_307 :
    (10005807409860391/500000000000000000000000:ℝ) ≤ ∫ x in (307/512:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-20422450499662123467388661867/12500000000000000000000000000000:ℝ)*(thetaPowerMass 5 (307/512:ℝ) (77/128:ℝ)-(4258662473983944316743/7102193807453257500160:ℝ)*thetaPowerMass 4 (307/512:ℝ) (77/128:ℝ)) ≤
      thetaFirstModeFirst (4258662473983944316743/7102193807453257500160:ℝ)*(thetaPowerMass 5 (307/512:ℝ) (77/128:ℝ)-(4258662473983944316743/7102193807453257500160:ℝ)*thetaPowerMass 4 (307/512:ℝ) (77/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0465.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (307/512:ℝ) (77/128:ℝ)
    (4258662473983944316743/7102193807453257500160:ℝ) (8030298673/100000000000000:ℝ) (-20422450499662123467388661867/12500000000000000000000000000000:ℝ) (452770307138013511551/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_307
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0923).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_307 :
    (∫ x in (307/512:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x) ≤ (20011827778912061/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (307/512:ℝ) (77/128:ℝ)
    (8033097371/100000000000000:ℝ) (7719541601/100000000000000:ℝ) (452770307138013511551/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_307 (thetaFirstMode_refined_node_0919).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_308 :
    (4870100545779701/250000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(309/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-3802722657758633698493/2500000000000000000000000:ℝ)*(thetaPowerMass 5 (77/128:ℝ) (309/512:ℝ)-(309/512:ℝ)*thetaPowerMass 4 (77/128:ℝ) (309/512:ℝ)) ≤
      thetaFirstModeFirst (309/512:ℝ)*(thetaPowerMass 5 (77/128:ℝ) (309/512:ℝ)-(309/512:ℝ)*thetaPowerMass 4 (77/128:ℝ) (309/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0467.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (77/128:ℝ) (309/512:ℝ)
    (309/512:ℝ) (741701579/10000000000000:ℝ) (-3802722657758633698493/2500000000000000000000000:ℝ) (28078299312739342725291/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_308
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0925).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_308 :
    (∫ x in (77/128:ℝ)..(309/512:ℝ), x^4*thetaFirstMode x) ≤ (19480540257435653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (77/128:ℝ) (309/512:ℝ)
    (7719541601/100000000000000:ℝ) (741704059/10000000000000:ℝ) (28078299312739342725291/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_308 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0925).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_309 :
    (18959321576310839/1000000000000000000000000:ℝ) ≤ ∫ x in (309/512:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-15206214611497358587433543671/10000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (309/512:ℝ) (155/256:ℝ)-(4514955175067537709441/7480881854937014095360:ℝ)*thetaPowerMass 4 (309/512:ℝ) (155/256:ℝ)) ≤
      thetaFirstModeFirst (4514955175067537709441/7480881854937014095360:ℝ)*(thetaPowerMass 5 (309/512:ℝ) (155/256:ℝ)-(4514955175067537709441/7480881854937014095360:ℝ)*thetaPowerMass 4 (309/512:ℝ) (155/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0468.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (309/512:ℝ) (155/256:ℝ)
    (4514955175067537709441/7480881854937014095360:ℝ) (3707226231/50000000000000:ℝ) (-15206214611497358587433543671/10000000000000000000000000000000:ℝ) (27202750094728656016807/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_309
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0929).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_309 :
    (∫ x in (309/512:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x) ≤ (4739881916538837/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (309/512:ℝ) (155/256:ℝ)
    (741704059/10000000000000:ℝ) (7125251383/100000000000000:ℝ) (27202750094728656016807/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_309 (thetaFirstMode_refined_node_0925).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_310 :
    (18448583149480991/1000000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(311/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-17685166475982467418957/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (155/256:ℝ) (311/512:ℝ)-(311/512:ℝ)*thetaPowerMass 4 (155/256:ℝ) (311/512:ℝ)) ≤
      thetaFirstModeFirst (311/512:ℝ)*(thetaPowerMass 5 (155/256:ℝ) (311/512:ℝ)-(311/512:ℝ)*thetaPowerMass 4 (155/256:ℝ) (311/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0470.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (155/256:ℝ) (311/512:ℝ)
    (311/512:ℝ) (6843816903/100000000000000:ℝ) (-17685166475982467418957/12500000000000000000000000:ℝ) (13175092945756406544489/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_310
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0931).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_310 :
    (∫ x in (155/256:ℝ)..(311/512:ℝ), x^4*thetaFirstMode x) ≤ (9224358147981239/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (155/256:ℝ) (311/512:ℝ)
    (7125251383/100000000000000:ℝ) (3421919983/50000000000000:ℝ) (13175092945756406544489/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_310 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0931).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_311 :
    (17947829467117507/1000000000000000000000000:ℝ) ≤ ∫ x in (311/512:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x := by
  have hd : (-1767971676692178932262396061/1250000000000000000000000000000:ℝ)*(thetaPowerMass 5 (311/512:ℝ) (39/64:ℝ)-(4784867650250851000959/7877121216105401397760:ℝ)*thetaPowerMass 4 (311/512:ℝ) (39/64:ℝ)) ≤
      thetaFirstModeFirst (4784867650250851000959/7877121216105401397760:ℝ)*(thetaPowerMass 5 (311/512:ℝ) (39/64:ℝ)-(4784867650250851000959/7877121216105401397760:ℝ)*thetaPowerMass 4 (311/512:ℝ) (39/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0471.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (311/512:ℝ) (39/64:ℝ)
    (4784867650250851000959/7877121216105401397760:ℝ) (3420724001/50000000000000:ℝ) (-1767971676692178932262396061/1250000000000000000000000000000:ℝ) (5104029109918624195953/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_311
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0935).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_311 :
    (∫ x in (311/512:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x) ≤ (17948028757031131/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (311/512:ℝ) (39/64:ℝ)
    (3421919983/50000000000000:ℝ) (6572481097/100000000000000:ℝ) (5104029109918624195953/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_311 (thetaFirstMode_refined_node_0931).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_312 :
    (17457255835097047/1000000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(313/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-4109721395284074488977/3125000000000000000000000:ℝ)*(thetaPowerMass 5 (39/64:ℝ) (313/512:ℝ)-(313/512:ℝ)*thetaPowerMass 4 (39/64:ℝ) (313/512:ℝ)) ≤
      thetaFirstModeFirst (313/512:ℝ)*(thetaPowerMass 5 (39/64:ℝ) (313/512:ℝ)-(313/512:ℝ)*thetaPowerMass 4 (39/64:ℝ) (313/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0473.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (39/64:ℝ) (313/512:ℝ)
    (313/512:ℝ) (1577709173/25000000000000:ℝ) (-4109721395284074488977/3125000000000000000000000:ℝ) (24712172933868604341027/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_312
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0937).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_312 :
    (∫ x in (39/64:ℝ)..(313/512:ℝ), x^4*thetaFirstMode x) ≤ (8728692067494413/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (39/64:ℝ) (313/512:ℝ)
    (6572481097/100000000000000:ℝ) (3155429063/50000000000000:ℝ) (24712172933868604341027/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_312 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0937).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_313 :
    (8488252781724669/500000000000000000000000:ℝ) ≤ ∫ x in (313/512:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-2629409213222150471003489169/2000000000000000000000000000000:ℝ)*(thetaPowerMass 5 (313/512:ℝ) (157/256:ℝ)-(5069029048681798692657/8291604583475060892160:ℝ)*thetaPowerMass 4 (313/512:ℝ) (157/256:ℝ)) ≤
      thetaFirstModeFirst (5069029048681798692657/8291604583475060892160:ℝ)*(thetaPowerMass 5 (313/512:ℝ) (157/256:ℝ)-(5069029048681798692657/8291604583475060892160:ℝ)*thetaPowerMass 4 (313/512:ℝ) (157/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0474.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (313/512:ℝ) (157/256:ℝ)
    (5069029048681798692657/8291604583475060892160:ℝ) (3154324399/50000000000000:ℝ) (-2629409213222150471003489169/2000000000000000000000000000000:ℝ) (23925816996024384782671/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_313
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0941).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_313 :
    (∫ x in (313/512:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x) ≤ (8488349066673857/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (313/512:ℝ) (157/256:ℝ)
    (3155429063/50000000000000:ℝ) (302933141/5000000000000:ℝ) (23925816996024384782671/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_313 (thetaFirstMode_refined_node_0937).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_314 :
    (16505759684787357/1000000000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(315/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-15270460090085434897621/12500000000000000000000000:ℝ)*(thetaPowerMass 5 (157/256:ℝ) (315/512:ℝ)-(315/512:ℝ)*thetaPowerMass 4 (157/256:ℝ) (315/512:ℝ)) ≤
      thetaFirstModeFirst (315/512:ℝ)*(thetaPowerMass 5 (157/256:ℝ) (315/512:ℝ)-(315/512:ℝ)*thetaPowerMass 4 (157/256:ℝ) (315/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0476.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (157/256:ℝ) (315/512:ℝ)
    (315/512:ℝ) (2907787643/50000000000000:ℝ) (-15270460090085434897621/12500000000000000000000000:ℝ) (2895078978439768447953/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_314
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0943).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_314 :
    (∫ x in (157/256:ℝ)..(315/512:ℝ), x^4*thetaFirstMode x) ≤ (16505883223012363/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (157/256:ℝ) (315/512:ℝ)
    (302933141/5000000000000:ℝ) (5815595193/100000000000000:ℝ) (2895078978439768447953/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_314 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0943).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_315 :
    (16044662856707091/1000000000000000000000000:ℝ) ≤ ∫ x in (315/512:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x := by
  have hd : (-190821642355199244379493817/156250000000000000000000000000:ℝ)*(thetaPowerMass 5 (315/512:ℝ) (79/128:ℝ)-(1073618653626882244035/1745009456680404157952:ℝ)*thetaPowerMass 4 (315/512:ℝ) (79/128:ℝ)) ≤
      thetaFirstModeFirst (1073618653626882244035/1745009456680404157952:ℝ)*(thetaPowerMass 5 (315/512:ℝ) (79/128:ℝ)-(1073618653626882244035/1745009456680404157952:ℝ)*thetaPowerMass 4 (315/512:ℝ) (79/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0477.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (315/512:ℝ) (79/128:ℝ)
    (1073618653626882244035/1745009456680404157952:ℝ) (1453388951/25000000000000:ℝ) (-190821642355199244379493817/156250000000000000000000000000:ℝ) (22416176724474318852911/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_315
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0947).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_315 :
    (∫ x in (315/512:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x) ≤ (4011212197385739/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (315/512:ℝ) (79/128:ℝ)
    (5815595193/100000000000000:ℝ) (2790681667/50000000000000:ℝ) (22416176724474318852911/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_315 (thetaFirstMode_refined_node_0943).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_316 :
    (15593382418939389/1000000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(317/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-56703018631762541438073/50000000000000000000000000:ℝ)*(thetaPowerMass 5 (79/128:ℝ) (317/512:ℝ)-(317/512:ℝ)*thetaPowerMass 4 (79/128:ℝ) (317/512:ℝ)) ≤
      thetaFirstModeFirst (317/512:ℝ)*(thetaPowerMass 5 (79/128:ℝ) (317/512:ℝ)-(317/512:ℝ)*thetaPowerMass 4 (79/128:ℝ) (317/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0479.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (79/128:ℝ) (317/512:ℝ)
    (317/512:ℝ) (5355664767/100000000000000:ℝ) (-56703018631762541438073/50000000000000000000000000:ℝ) (10846008116516652901023/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_316
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0949).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_316 :
    (∫ x in (79/128:ℝ)..(317/512:ℝ), x^4*thetaFirstMode x) ≤ (15593501283643107/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (79/128:ℝ) (317/512:ℝ)
    (2790681667/50000000000000:ℝ) (1338920811/25000000000000:ℝ) (10846008116516652901023/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_316 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0949).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_317 :
    (3030312994389213/200000000000000000000000:ℝ) ≤ ∫ x in (317/512:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x := by
  have hd : (-7085676996472660790182265029/6250000000000000000000000000000:ℝ)*(thetaPowerMass 5 (317/512:ℝ) (159/256:ℝ)-(5682739761029596469193/9178187863912459548160:ℝ)*thetaPowerMass 4 (317/512:ℝ) (159/256:ℝ)) ≤
      thetaFirstModeFirst (5682739761029596469193/9178187863912459548160:ℝ)*(thetaPowerMass 5 (317/512:ℝ) (159/256:ℝ)-(5682739761029596469193/9178187863912459548160:ℝ)*thetaPowerMass 4 (317/512:ℝ) (159/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0480.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (317/512:ℝ) (159/256:ℝ)
    (5682739761029596469193/9178187863912459548160:ℝ) (1070760377/20000000000000:ℝ) (-7085676996472660790182265029/6250000000000000000000000000000:ℝ) (1311732513438111663089/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_317
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0953).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_317 :
    (∫ x in (317/512:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x) ≤ (15151744359100209/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (317/512:ℝ) (159/256:ℝ)
    (1338920811/25000000000000:ℝ) (256913933/5000000000000:ℝ) (1311732513438111663089/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_317 (thetaFirstMode_refined_node_0949).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_318 :
    (7359682368616647/500000000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(319/512:ℝ), x^4*thetaFirstMode x := by
  have hd : (-10520644050624667452087/10000000000000000000000000:ℝ)*(thetaPowerMass 5 (159/256:ℝ) (319/512:ℝ)-(319/512:ℝ)*thetaPowerMass 4 (159/256:ℝ) (319/512:ℝ)) ≤
      thetaFirstModeFirst (319/512:ℝ)*(thetaPowerMass 5 (159/256:ℝ) (319/512:ℝ)-(319/512:ℝ)*thetaPowerMass 4 (159/256:ℝ) (319/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0482.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (159/256:ℝ) (319/512:ℝ)
    (319/512:ℝ) (985772753/20000000000000:ℝ) (-10520644050624667452087/10000000000000000000000000:ℝ) (20302863861096708719893/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_318
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0955).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_318 :
    (∫ x in (159/256:ℝ)..(319/512:ℝ), x^4*thetaFirstMode x) ≤ (7359739509560309/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (159/256:ℝ) (319/512:ℝ)
    (256913933/5000000000000:ℝ) (4928880903/100000000000000:ℝ) (20302863861096708719893/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_318 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0955).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_4_319 :
    (14296430821356543/1000000000000000000000000:ℝ) ≤ ∫ x in (319/512:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x := by
  have hd : (-3286678066500038985541107551/3125000000000000000000000000000:ℝ)*(thetaPowerMass 5 (319/512:ℝ) (5/8:ℝ)-(6013674361321379726391/9651788693910057372160:ℝ)*thetaPowerMass 4 (319/512:ℝ) (5/8:ℝ)) ≤
      thetaFirstModeFirst (6013674361321379726391/9651788693910057372160:ℝ)*(thetaPowerMass 5 (319/512:ℝ) (5/8:ℝ)-(6013674361321379726391/9651788693910057372160:ℝ)*thetaPowerMass 4 (319/512:ℝ) (5/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0483.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 4 (319/512:ℝ) (5/8:ℝ)
    (6013674361321379726391/9651788693910057372160:ℝ) (492714641/10000000000000:ℝ) (-3286678066500038985541107551/3125000000000000000000000000000:ℝ) (981851388666244180191/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_319
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0959).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_4_319 :
    (∫ x in (319/512:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x) ≤ (14296603758197663/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (319/512:ℝ) (5/8:ℝ)
    (4928880903/100000000000000:ℝ) (147725897/3125000000000:ℝ) (981851388666244180191/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_319 (thetaFirstMode_refined_node_0955).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
