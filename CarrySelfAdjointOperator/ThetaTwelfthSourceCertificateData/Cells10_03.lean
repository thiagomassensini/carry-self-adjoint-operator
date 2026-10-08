import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature03
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative04
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative05
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative06

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_096 :
    (2490800268533/1000000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(97/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-969663504433780707057507/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (3/16:ℝ) (97/512:ℝ)-(97/512:ℝ)*thetaPowerMass 10 (3/16:ℝ) (97/512:ℝ)) ≤
      thetaFirstModeFirst (97/512:ℝ)*(thetaPowerMass 11 (3/16:ℝ) (97/512:ℝ)-(97/512:ℝ)*thetaPowerMass 10 (3/16:ℝ) (97/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0149.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (3/16:ℝ) (97/512:ℝ)
    (97/512:ℝ) (1117412285759/50000000000000:ℝ) (-969663504433780707057507/5000000000000000000000000:ℝ) (79542980257604461978243/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_096
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0289).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_096 :
    (∫ x in (3/16:ℝ)..(97/512:ℝ), x^10*thetaFirstMode x) ≤ (77837632081/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/16:ℝ) (97/512:ℝ)
    (5682371767/250000000000:ℝ) (446965567181/20000000000000:ℝ) (79542980257604461978243/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_096 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0289).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_097 :
    (339357919737/125000000000000000000000:ℝ) ≤ ∫ x in (97/512:ℝ)..(49/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2423309469003666491290107722139/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (97/512:ℝ) (49/256:ℝ)-(133804837701602793/706068831528348160:ℝ)*thetaPowerMass 10 (97/512:ℝ) (49/256:ℝ)) ≤
      thetaFirstModeFirst (133804837701602793/706068831528348160:ℝ)*(thetaPowerMass 11 (97/512:ℝ) (49/256:ℝ)-(133804837701602793/706068831528348160:ℝ)*thetaPowerMass 10 (97/512:ℝ) (49/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0150.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (97/512:ℝ) (49/256:ℝ)
    (133804837701602793/706068831528348160:ℝ) (1116892008393/50000000000000:ℝ) (-2423309469003666491290107722139/12500000000000000000000000000000:ℝ) (631701378085954983459/500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_097
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0293).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_097 :
    (∫ x in (97/512:ℝ)..(49/256:ℝ), x^10*thetaFirstMode x) ≤ (2714868041919/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (97/512:ℝ) (49/256:ℝ)
    (446965567181/20000000000000:ℝ) (219719245643/10000000000000:ℝ) (631701378085954983459/500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_097 (thetaFirstMode_refined_node_0289).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_098 :
    (1477882539609/500000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(99/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1181234709499861645374897/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (49/256:ℝ) (99/512:ℝ)-(99/512:ℝ)*thetaPowerMass 10 (49/256:ℝ) (99/512:ℝ)) ≤
      thetaFirstModeFirst (99/512:ℝ)*(thetaPowerMass 11 (49/256:ℝ) (99/512:ℝ)-(99/512:ℝ)*thetaPowerMass 10 (49/256:ℝ) (99/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0152.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (49/256:ℝ) (99/512:ℝ)
    (99/512:ℝ) (540008961651/25000000000000:ℝ) (-1181234709499861645374897/6250000000000000000000000:ℝ) (250816855496097153114469/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_098
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0295).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_098 :
    (∫ x in (49/256:ℝ)..(99/512:ℝ), x^10*thetaFirstMode x) ≤ (295576982613/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (49/256:ℝ) (99/512:ℝ)
    (219719245643/10000000000000:ℝ) (1080019513247/50000000000000:ℝ) (250816855496097153114469/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_098 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0295).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_099 :
    (3214501257159/1000000000000000000000000:ℝ) ≤ ∫ x in (99/512:ℝ)..(25/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1889319597122152687153954521623/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (99/512:ℝ) (25/128:ℝ)-(160775853321491991/831261189349250560:ℝ)*thetaPowerMass 10 (99/512:ℝ) (25/128:ℝ)) ≤
      thetaFirstModeFirst (160775853321491991/831261189349250560:ℝ)*(thetaPowerMass 11 (99/512:ℝ) (25/128:ℝ)-(160775853321491991/831261189349250560:ℝ)*thetaPowerMass 10 (99/512:ℝ) (25/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0153.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (99/512:ℝ) (25/128:ℝ)
    (160775853321491991/831261189349250560:ℝ) (2159042234709/100000000000000:ℝ) (-1889319597122152687153954521623/10000000000000000000000000000000:ℝ) (311183437377524429533721/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_099
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0299).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_099 :
    (∫ x in (99/512:ℝ)..(25/128:ℝ), x^10*thetaFirstMode x) ≤ (1607253437779/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (99/512:ℝ) (25/128:ℝ)
    (1080019513247/50000000000000:ℝ) (530840997859/25000000000000:ℝ) (311183437377524429533721/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_099 (thetaFirstMode_refined_node_0295).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_100 :
    (873027856951/250000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(101/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-9206766502248011088955491/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (25/128:ℝ) (101/512:ℝ)-(101/512:ℝ)*thetaPowerMass 10 (25/128:ℝ) (101/512:ℝ)) ≤
      thetaFirstModeFirst (101/512:ℝ)*(thetaPowerMass 11 (25/128:ℝ) (101/512:ℝ)-(101/512:ℝ)*thetaPowerMass 10 (25/128:ℝ) (101/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0155.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (25/128:ℝ) (101/512:ℝ)
    (101/512:ℝ) (2087160687639/100000000000000:ℝ) (-9206766502248011088955491/50000000000000000000000000:ℝ) (1235352673532054159865149/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_100
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0301).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_100 :
    (∫ x in (25/128:ℝ)..(101/512:ℝ), x^10*thetaFirstMode x) ≤ (436514637007/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/128:ℝ) (101/512:ℝ)
    (530840997859/25000000000000:ℝ) (417432756869/20000000000000:ℝ) (1235352673532054159865149/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_100 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0301).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_101 :
    (473709108153/125000000000000000000000:ℝ) ≤ ∫ x in (101/512:ℝ)..(51/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-575224997641594188646699268061/3125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (101/512:ℝ) (51/256:ℝ)-(192475564448517009/975462843111554560:ℝ)*thetaPowerMass 10 (101/512:ℝ) (51/256:ℝ)) ≤
      thetaFirstModeFirst (192475564448517009/975462843111554560:ℝ)*(thetaPowerMass 11 (101/512:ℝ) (51/256:ℝ)-(192475564448517009/975462843111554560:ℝ)*thetaPowerMass 10 (101/512:ℝ) (51/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0156.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (101/512:ℝ) (51/256:ℝ)
    (192475564448517009/975462843111554560:ℝ) (2086211786141/100000000000000:ℝ) (-575224997641594188646699268061/3125000000000000000000000000000:ℝ) (1225942550278573731374667/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_101
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0305).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_101 :
    (∫ x in (101/512:ℝ)..(51/256:ℝ), x^10*thetaFirstMode x) ≤ (3789679575867/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (101/512:ℝ) (51/256:ℝ)
    (417432756869/20000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1225942550278573731374667/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_101 (thetaFirstMode_refined_node_0301).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_102 :
    (821661673353/200000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(103/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-560457836805157194420567/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (51/256:ℝ) (103/512:ℝ)-(103/512:ℝ)*thetaPowerMass 10 (51/256:ℝ) (103/512:ℝ)) ≤
      thetaFirstModeFirst (103/512:ℝ)*(thetaPowerMass 11 (51/256:ℝ) (103/512:ℝ)-(103/512:ℝ)*thetaPowerMass 10 (51/256:ℝ) (103/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0158.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (51/256:ℝ) (103/512:ℝ)
    (103/512:ℝ) (504042628491/25000000000000:ℝ) (-560457836805157194420567/3125000000000000000000000:ℝ) (608252439780117264523113/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_102
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0307).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_102 :
    (∫ x in (51/256:ℝ)..(103/512:ℝ), x^10*thetaFirstMode x) ≤ (2054157553431/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (51/256:ℝ) (103/512:ℝ)
    (2051434826679/100000000000000:ℝ) (403234705761/20000000000000:ℝ) (608252439780117264523113/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_102 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0307).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_103 :
    (4449178668303/1000000000000000000000000:ℝ) ≤ ∫ x in (103/512:ℝ)..(13/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-22410669733251202917470933647/125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (103/512:ℝ) (13/64:ℝ)-(229614139092996207/1141096218995868160:ℝ)*thetaPowerMass 10 (103/512:ℝ) (13/64:ℝ)) ≤
      thetaFirstModeFirst (229614139092996207/1141096218995868160:ℝ)*(thetaPowerMass 11 (103/512:ℝ) (13/64:ℝ)-(229614139092996207/1141096218995868160:ℝ)*thetaPowerMass 10 (103/512:ℝ) (13/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0159.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (103/512:ℝ) (13/64:ℝ)
    (229614139092996207/1141096218995868160:ℝ) (1007632108921/50000000000000:ℝ) (-22410669733251202917470933647/125000000000000000000000000000:ℝ) (603520579949104592553451/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_103
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0311).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_103 :
    (∫ x in (103/512:ℝ)..(13/64:ℝ), x^10*thetaFirstMode x) ≤ (4449186650849/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (103/512:ℝ) (13/64:ℝ)
    (403234705761/20000000000000:ℝ) (990688145289/50000000000000:ℝ) (603520579949104592553451/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_103 (thetaFirstMode_refined_node_0307).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_104 :
    (4813491765507/1000000000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(105/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-873157585778458523043039/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (13/64:ℝ) (105/512:ℝ)-(105/512:ℝ)*thetaPowerMass 10 (13/64:ℝ) (105/512:ℝ)) ≤
      thetaFirstModeFirst (105/512:ℝ)*(thetaPowerMass 11 (13/64:ℝ) (105/512:ℝ)-(105/512:ℝ)*thetaPowerMass 10 (13/64:ℝ) (105/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0161.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (13/64:ℝ) (105/512:ℝ)
    (105/512:ℝ) (194703656763/10000000000000:ℝ) (-873157585778458523043039/5000000000000000000000000:ℝ) (1197552888164553565647723/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_104
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0313).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_104 :
    (∫ x in (13/64:ℝ)..(105/512:ℝ), x^10*thetaFirstMode x) ≤ (4813499747803/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/64:ℝ) (105/512:ℝ)
    (990688145289/50000000000000:ℝ) (1947039501927/100000000000000:ℝ) (1197552888164553565647723/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_104 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0313).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_105 :
    (5202493404549/1000000000000000000000000:ℝ) ≤ ∫ x in (105/512:ℝ)..(53/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4364311752639487618421290283097/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (105/512:ℝ) (53/256:ℝ)-(54598255949620845/266167146581207552:ℝ)*thetaPowerMass 10 (105/512:ℝ) (53/256:ℝ)) ≤
      thetaFirstModeFirst (54598255949620845/266167146581207552:ℝ)*(thetaPowerMass 11 (105/512:ℝ) (53/256:ℝ)-(54598255949620845/266167146581207552:ℝ)*thetaPowerMass 10 (105/512:ℝ) (53/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0162.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (105/512:ℝ) (53/256:ℝ)
    (54598255949620845/266167146581207552:ℝ) (1946170889819/100000000000000:ℝ) (-4364311752639487618421290283097/25000000000000000000000000000000:ℝ) (237608311840065476240513/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_105
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0317).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_105 :
    (∫ x in (105/512:ℝ)..(53/256:ℝ), x^10*thetaFirstMode x) ≤ (5202502862751/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (105/512:ℝ) (53/256:ℝ)
    (1947039501927/100000000000000:ℝ) (1913159543403/100000000000000:ℝ) (237608311840065476240513/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_105 (thetaFirstMode_refined_node_0313).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_106 :
    (5617478251533/1000000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(107/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-8499537090908457057799183/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (53/256:ℝ) (107/512:ℝ)-(107/512:ℝ)*thetaPowerMass 10 (53/256:ℝ) (107/512:ℝ)) ≤
      thetaFirstModeFirst (107/512:ℝ)*(thetaPowerMass 11 (53/256:ℝ) (107/512:ℝ)-(107/512:ℝ)*thetaPowerMass 10 (53/256:ℝ) (107/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0164.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (53/256:ℝ) (107/512:ℝ)
    (107/512:ℝ) (1879729931687/100000000000000:ℝ) (-8499537090908457057799183/50000000000000000000000000:ℝ) (4714034661840215647083/4000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_106
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0319).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_106 :
    (∫ x in (53/256:ℝ)..(107/512:ℝ), x^10*thetaFirstMode x) ≤ (1404371917047/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/256:ℝ) (107/512:ℝ)
    (1913159543403/100000000000000:ℝ) (117483299173/6250000000000:ℝ) (4714034661840215647083/4000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_106 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0319).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_107 :
    (3029889047383/500000000000000000000000:ℝ) ≤ ∫ x in (107/512:ℝ)..(27/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-8496686169668207224991266035167/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (107/512:ℝ) (27/128:ℝ)-(323505440094667743/1547628340508700160:ℝ)*thetaPowerMass 10 (107/512:ℝ) (27/128:ℝ)) ≤
      thetaFirstModeFirst (323505440094667743/1547628340508700160:ℝ)*(thetaPowerMass 11 (107/512:ℝ) (27/128:ℝ)-(323505440094667743/1547628340508700160:ℝ)*thetaPowerMass 10 (107/512:ℝ) (27/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0165.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (107/512:ℝ) (27/128:ℝ)
    (323505440094667743/1547628340508700160:ℝ) (1878902994507/100000000000000:ℝ) (-8496686169668207224991266035167/50000000000000000000000000000000:ℝ) (73059731039782495279543/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_107
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0323).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_107 :
    (∫ x in (107/512:ℝ)..(27/128:ℝ), x^10*thetaFirstMode x) ≤ (189368414341/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (107/512:ℝ) (27/128:ℝ)
    (117483299173/6250000000000:ℝ) (1846755595551/100000000000000:ℝ) (73059731039782495279543/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_107 (thetaFirstMode_refined_node_0319).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_108 :
    (3265387614591/500000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(109/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-330849037463883572510537/2000000000000000000000000:ℝ)*(thetaPowerMass 11 (27/128:ℝ) (109/512:ℝ)-(109/512:ℝ)*thetaPowerMass 10 (27/128:ℝ) (109/512:ℝ)) ≤
      thetaFirstModeFirst (109/512:ℝ)*(thetaPowerMass 11 (27/128:ℝ) (109/512:ℝ)-(109/512:ℝ)*thetaPowerMass 10 (27/128:ℝ) (109/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0167.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (27/128:ℝ) (109/512:ℝ)
    (109/512:ℝ) (1814221548443/100000000000000:ℝ) (-330849037463883572510537/2000000000000000000000000:ℝ) (289846034826571327379441/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_108
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0325).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_108 :
    (∫ x in (27/128:ℝ)..(109/512:ℝ), x^10*thetaFirstMode x) ≤ (6530786296203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/128:ℝ) (109/512:ℝ)
    (1846755595551/100000000000000:ℝ) (1814224325637/100000000000000:ℝ) (289846034826571327379441/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_108 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0325).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_109 :
    (1406377589769/200000000000000000000000:ℝ) ≤ ∫ x in (109/512:ℝ)..(55/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-413423645529846024625133656701/2500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (109/512:ℝ) (55/256:ℝ)-(382163785687980441/1794715319477839360:ℝ)*thetaPowerMass 10 (109/512:ℝ) (55/256:ℝ)) ≤
      thetaFirstModeFirst (382163785687980441/1794715319477839360:ℝ)*(thetaPowerMass 11 (109/512:ℝ) (55/256:ℝ)-(382163785687980441/1794715319477839360:ℝ)*thetaPowerMass 10 (109/512:ℝ) (55/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0168.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (109/512:ℝ) (55/256:ℝ)
    (382163785687980441/1794715319477839360:ℝ) (113339473489/6250000000000:ℝ) (-413423645529846024625133656701/2500000000000000000000000000000:ℝ) (574897738276723779980301/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_109
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0329).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_109 :
    (∫ x in (109/512:ℝ)..(55/256:ℝ), x^10*thetaFirstMode x) ≤ (7031901078347/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (109/512:ℝ) (55/256:ℝ)
    (1814224325637/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (574897738276723779980301/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_109 (thetaFirstMode_refined_node_0325).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_110 :
    (1891146643781/250000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(111/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-8046656918293625337524409/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (55/256:ℝ) (111/512:ℝ)-(111/512:ℝ)*thetaPowerMass 10 (55/256:ℝ) (111/512:ℝ)) ≤
      thetaFirstModeFirst (111/512:ℝ)*(thetaPowerMass 11 (55/256:ℝ) (111/512:ℝ)-(111/512:ℝ)*thetaPowerMass 10 (55/256:ℝ) (111/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0170.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (55/256:ℝ) (111/512:ℝ)
    (111/512:ℝ) (1750482237681/100000000000000:ℝ) (-8046656918293625337524409/50000000000000000000000000:ℝ) (142523898450206933899489/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_110
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0331).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_110 :
    (∫ x in (55/256:ℝ)..(111/512:ℝ), x^10*thetaFirstMode x) ≤ (3782299767267/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/256:ℝ) (111/512:ℝ)
    (1782135325809/100000000000000:ℝ) (1750484938319/100000000000000:ℝ) (142523898450206933899489/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_110 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0331).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_111 :
    (2032593938307/250000000000000000000000:ℝ) ≤ ∫ x in (111/512:ℝ)..(7/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2010999603662724551427961111221/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (111/512:ℝ) (7/32:ℝ)-(450092942792761959/2075655332250933760:ℝ)*thetaPowerMass 10 (111/512:ℝ) (7/32:ℝ)) ≤
      thetaFirstModeFirst (450092942792761959/2075655332250933760:ℝ)*(thetaPowerMass 11 (111/512:ℝ) (7/32:ℝ)-(450092942792761959/2075655332250933760:ℝ)*thetaPowerMass 10 (111/512:ℝ) (7/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0171.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (111/512:ℝ) (7/32:ℝ)
    (450092942792761959/2075655332250933760:ℝ) (349945509609/20000000000000:ℝ) (-2010999603662724551427961111221/12500000000000000000000000000000:ℝ) (282643186868228365228189/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_111
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0335).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_111 :
    (∫ x in (111/512:ℝ)..(7/32:ℝ), x^10*thetaFirstMode x) ≤ (2032597784853/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (111/512:ℝ) (7/32:ℝ)
    (1750484938319/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (282643186868228365228189/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_111 (thetaFirstMode_refined_node_0331).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_112 :
    (1746162724667/200000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(113/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1956460561330618090902957/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (7/32:ℝ) (113/512:ℝ)-(113/512:ℝ)*thetaPowerMass 10 (7/32:ℝ) (113/512:ℝ)) ≤
      thetaFirstModeFirst (113/512:ℝ)*(thetaPowerMass 11 (7/32:ℝ) (113/512:ℝ)-(113/512:ℝ)*thetaPowerMass 10 (7/32:ℝ) (113/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0173.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (7/32:ℝ) (113/512:ℝ)
    (113/512:ℝ) (1688482714757/100000000000000:ℝ) (-1956460561330618090902957/12500000000000000000000000:ℝ) (70058851663064255029919/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_112
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0337).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_112 :
    (∫ x in (7/32:ℝ)..(113/512:ℝ), x^10*thetaFirstMode x) ≤ (545676796589/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/32:ℝ) (113/512:ℝ)
    (1719269499473/100000000000000:ℝ) (844242670087/50000000000000:ℝ) (70058851663064255029919/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_112 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0337).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_113 :
    (936749036117/100000000000000000000000:ℝ) ≤ ∫ x in (113/512:ℝ)..(57/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-7823275043007384070353665834951/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (113/512:ℝ) (57/256:ℝ)-(528550581246993657/2394348818532252160:ℝ)*thetaPowerMass 10 (113/512:ℝ) (57/256:ℝ)) ≤
      thetaFirstModeFirst (528550581246993657/2394348818532252160:ℝ)*(thetaPowerMass 11 (113/512:ℝ) (57/256:ℝ)-(528550581246993657/2394348818532252160:ℝ)*thetaPowerMass 10 (113/512:ℝ) (57/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0174.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (113/512:ℝ) (57/256:ℝ)
    (528550581246993657/2394348818532252160:ℝ) (1687761714569/100000000000000:ℝ) (-7823275043007384070353665834951/50000000000000000000000000000000:ℝ) (277824822626642708938421/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_113
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0341).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_113 :
    (∫ x in (113/512:ℝ)..(57/256:ℝ), x^10*thetaFirstMode x) ≤ (4683754165107/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (113/512:ℝ) (57/256:ℝ)
    (844242670087/50000000000000:ℝ) (1658128786473/100000000000000:ℝ) (277824822626642708938421/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_113 (thetaFirstMode_refined_node_0337).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_114 :
    (627628191937/62500000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(115/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1902197956516511742082467/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (57/256:ℝ) (115/512:ℝ)-(115/512:ℝ)*thetaPowerMass 10 (57/256:ℝ) (115/512:ℝ)) ≤
      thetaFirstModeFirst (115/512:ℝ)*(thetaPowerMass 11 (57/256:ℝ) (115/512:ℝ)-(115/512:ℝ)*thetaPowerMass 10 (57/256:ℝ) (115/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0176.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (57/256:ℝ) (115/512:ℝ)
    (115/512:ℝ) (1628193608631/100000000000000:ℝ) (-1902197956516511742082467/12500000000000000000000000:ℝ) (44065887975287776582341/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_114
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0343).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_114 :
    (∫ x in (57/256:ℝ)..(115/512:ℝ), x^10*thetaFirstMode x) ≤ (10042068656757/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (57/256:ℝ) (115/512:ℝ)
    (1658128786473/100000000000000:ℝ) (1628196160161/100000000000000:ℝ) (44065887975287776582341/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_114 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0343).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_115 :
    (2689042481929/250000000000000000000000:ℝ) ≤ ∫ x in (115/512:ℝ)..(29/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-7606312845547518452462719694997/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (115/512:ℝ) (29/128:ℝ)-(123787575796526235/551012753541565952:ℝ)*thetaPowerMass 10 (115/512:ℝ) (29/128:ℝ)) ≤
      thetaFirstModeFirst (123787575796526235/551012753541565952:ℝ)*(thetaPowerMass 11 (115/512:ℝ) (29/128:ℝ)-(123787575796526235/551012753541565952:ℝ)*thetaPowerMass 10 (115/512:ℝ) (29/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0177.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (115/512:ℝ) (29/128:ℝ)
    (123787575796526235/551012753541565952:ℝ) (813752393251/50000000000000:ℝ) (-7606312845547518452462719694997/50000000000000000000000000000000:ℝ) (545993403897977599816047/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_115
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0347).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_115 :
    (∫ x in (115/512:ℝ)..(29/128:ℝ), x^10*thetaFirstMode x) ≤ (1344523855453/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (115/512:ℝ) (29/128:ℝ)
    (1628196160161/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (545993403897977599816047/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_115 (thetaFirstMode_refined_node_0343).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_116 :
    (5755788729761/500000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(117/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-902772617614741520607/6103515625000000000000:ℝ)*(thetaPowerMass 11 (29/128:ℝ) (117/512:ℝ)-(117/512:ℝ)*thetaPowerMass 10 (29/128:ℝ) (117/512:ℝ)) ≤
      thetaFirstModeFirst (117/512:ℝ)*(thetaPowerMass 11 (29/128:ℝ) (117/512:ℝ)-(117/512:ℝ)*thetaPowerMass 10 (29/128:ℝ) (117/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0179.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (29/128:ℝ) (117/512:ℝ)
    (117/512:ℝ) (12262386561/781250000000:ℝ) (-902772617614741520607/6103515625000000000000:ℝ) (541159782154773469745817/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_116
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0349).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_116 :
    (∫ x in (29/128:ℝ)..(117/512:ℝ), x^10*thetaFirstMode x) ≤ (2877899460759/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/128:ℝ) (117/512:ℝ)
    (1598683779299/100000000000000:ℝ) (313917591757/20000000000000:ℝ) (541159782154773469745817/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_116 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0349).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_117 :
    (3077507389177/250000000000000000000000:ℝ) ≤ ∫ x in (117/512:ℝ)..(59/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1848279894301567142742243227311/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (117/512:ℝ) (59/256:ℝ)-(722812917611120193/3162462922265628160:ℝ)*thetaPowerMass 10 (117/512:ℝ) (59/256:ℝ)) ≤
      thetaFirstModeFirst (722812917611120193/3162462922265628160:ℝ)*(thetaPowerMass 11 (117/512:ℝ) (59/256:ℝ)-(722812917611120193/3162462922265628160:ℝ)*thetaPowerMass 10 (117/512:ℝ) (59/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0180.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (117/512:ℝ) (59/256:ℝ)
    (722812917611120193/3162462922265628160:ℝ) (156892740107/10000000000000:ℝ) (-1848279894301567142742243227311/12500000000000000000000000000000:ℝ) (536323455561854795423377/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_117
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0353).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_117 :
    (∫ x in (117/512:ℝ)..(59/256:ℝ), x^10*thetaFirstMode x) ≤ (246201076493/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (117/512:ℝ) (59/256:ℝ)
    (313917591757/20000000000000:ℝ) (1540905010899/100000000000000:ℝ) (536323455561854795423377/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_117 (thetaFirstMode_refined_node_0349).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_118 :
    (13153339911931/1000000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(119/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-898251496591968160648747/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (59/256:ℝ) (119/512:ℝ)-(119/512:ℝ)*thetaPowerMass 10 (59/256:ℝ) (119/512:ℝ)) ≤
      thetaFirstModeFirst (119/512:ℝ)*(thetaPowerMass 11 (59/256:ℝ) (119/512:ℝ)-(119/512:ℝ)*thetaPowerMass 10 (59/256:ℝ) (119/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0182.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (59/256:ℝ) (119/512:ℝ)
    (119/512:ℝ) (189078604763/12500000000000:ℝ) (-898251496591968160648747/6250000000000000000000000:ℝ) (1062970283742563086707513/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_118
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0355).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_118 :
    (∫ x in (59/256:ℝ)..(119/512:ℝ), x^10*thetaFirstMode x) ≤ (13153363462959/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (59/256:ℝ) (119/512:ℝ)
    (1540905010899/100000000000000:ℝ) (756315622931/50000000000000:ℝ) (1062970283742563086707513/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_118 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0355).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_119 :
    (561733722271/40000000000000000000000:ℝ) ≤ ∫ x in (119/512:ℝ)..(15/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-897962589555610564127376834331/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (119/512:ℝ) (15/64:ℝ)-(841905060294227391/3621632464243356160:ℝ)*thetaPowerMass 10 (119/512:ℝ) (15/64:ℝ)) ≤
      thetaFirstModeFirst (841905060294227391/3621632464243356160:ℝ)*(thetaPowerMass 11 (119/512:ℝ) (15/64:ℝ)-(841905060294227391/3621632464243356160:ℝ)*thetaPowerMass 10 (119/512:ℝ) (15/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0183.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (119/512:ℝ) (15/64:ℝ)
    (841905060294227391/3621632464243356160:ℝ) (378000034967/25000000000000:ℝ) (-897962589555610564127376834331/6250000000000000000000000000000:ℝ) (1053291110608192099983023/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_119
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0359).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_119 :
    (∫ x in (119/512:ℝ)..(15/64:ℝ), x^10*thetaFirstMode x) ≤ (7021685563211/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (119/512:ℝ) (15/64:ℝ)
    (756315622931/50000000000000:ℝ) (148476297237/10000000000000:ℝ) (1053291110608192099983023/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_119 (thetaFirstMode_refined_node_0355).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_120 :
    (7490966419993/500000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(121/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1745072750218572632757533/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (15/64:ℝ) (121/512:ℝ)-(121/512:ℝ)*thetaPowerMass 10 (15/64:ℝ) (121/512:ℝ)) ≤
      thetaFirstModeFirst (121/512:ℝ)*(thetaPowerMass 11 (15/64:ℝ) (121/512:ℝ)-(121/512:ℝ)*thetaPowerMass 10 (15/64:ℝ) (121/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0185.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (15/64:ℝ) (121/512:ℝ)
    (121/512:ℝ) (728647080143/50000000000000:ℝ) (-1745072750218572632757533/12500000000000000000000000:ℝ) (521805406388959194943977/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_120
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0361).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_120 :
    (∫ x in (15/64:ℝ)..(121/512:ℝ), x^10*thetaFirstMode x) ≤ (14981959966641/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/64:ℝ) (121/512:ℝ)
    (148476297237/10000000000000:ℝ) (728648249079/50000000000000:ℝ) (521805406388959194943977/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_120 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0361).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_121 :
    (15971018537049/1000000000000000000000000:ℝ) ≤ ∫ x in (121/512:ℝ)..(61/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1744514871464821679415714520549/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (121/512:ℝ) (61/256:ℝ)-(978130364965943409/4138112237655400960:ℝ)*thetaPowerMass 10 (121/512:ℝ) (61/256:ℝ)) ≤
      thetaFirstModeFirst (978130364965943409/4138112237655400960:ℝ)*(thetaPowerMass 11 (121/512:ℝ) (61/256:ℝ)-(978130364965943409/4138112237655400960:ℝ)*thetaPowerMass 10 (121/512:ℝ) (61/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0186.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (121/512:ℝ) (61/256:ℝ)
    (978130364965943409/4138112237655400960:ℝ) (1456693546909/100000000000000:ℝ) (-1744514871464821679415714520549/12500000000000000000000000000000:ℝ) (516965401780457664772741/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_121
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0365).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_121 :
    (∫ x in (121/512:ℝ)..(61/256:ℝ), x^10*thetaFirstMode x) ≤ (319421018119/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (121/512:ℝ) (61/256:ℝ)
    (728648249079/50000000000000:ℝ) (35755703263/2500000000000:ℝ) (516965401780457664772741/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_121 (thetaFirstMode_refined_node_0361).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_122 :
    (17012570370747/1000000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(123/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-338917562455355858244801/2500000000000000000000000:ℝ)*(thetaPowerMass 11 (61/256:ℝ) (123/512:ℝ)-(123/512:ℝ)*thetaPowerMass 10 (61/256:ℝ) (123/512:ℝ)) ≤
      thetaFirstModeFirst (123/512:ℝ)*(thetaPowerMass 11 (61/256:ℝ) (123/512:ℝ)-(123/512:ℝ)*thetaPowerMass 10 (61/256:ℝ) (123/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0188.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (61/256:ℝ) (123/512:ℝ)
    (123/512:ℝ) (280710381513/20000000000000:ℝ) (-338917562455355858244801/2500000000000000000000000:ℝ) (40970099528116381110747/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_122
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0367).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_122 :
    (∫ x in (61/256:ℝ)..(123/512:ℝ), x^10*thetaFirstMode x) ≤ (17012601522119/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (61/256:ℝ) (123/512:ℝ)
    (35755703263/2500000000000:ℝ) (17544427211/1250000000000:ℝ) (40970099528116381110747/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_122 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0367).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_123 :
    (9054283805649/500000000000000000000000:ℝ) ≤ ∫ x in (123/512:ℝ)..(31/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-169404921870063426903633550137/1250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (123/512:ℝ) (31/128:ℝ)-(1133608087849118607/4717927560779292160:ℝ)*thetaPowerMass 10 (123/512:ℝ) (31/128:ℝ)) ≤
      thetaFirstModeFirst (1133608087849118607/4717927560779292160:ℝ)*(thetaPowerMass 11 (123/512:ℝ) (31/128:ℝ)-(1133608087849118607/4717927560779292160:ℝ)*thetaPowerMass 10 (123/512:ℝ) (31/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0189.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (123/512:ℝ) (31/128:ℝ)
    (1133608087849118607/4717927560779292160:ℝ) (28059562929/2000000000000:ℝ) (-169404921870063426903633550137/1250000000000000000000000000000:ℝ) (50728863175888107675219/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_123
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0371).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_123 :
    (∫ x in (123/512:ℝ)..(31/128:ℝ), x^10*thetaFirstMode x) ≤ (3621720965751/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (123/512:ℝ) (31/128:ℝ)
    (17544427211/1250000000000:ℝ) (537996463/39062500000:ℝ) (50728863175888107675219/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_123 (thetaFirstMode_refined_node_0367).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_124 :
    (19261052281529/1000000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(125/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-6580191396819706755270939/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (31/128:ℝ) (125/512:ℝ)-(125/512:ℝ)*thetaPowerMass 10 (31/128:ℝ) (125/512:ℝ)) ≤
      thetaFirstModeFirst (125/512:ℝ)*(thetaPowerMass 11 (31/128:ℝ) (125/512:ℝ)-(125/512:ℝ)*thetaPowerMass 10 (31/128:ℝ) (125/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0191.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (31/128:ℝ) (125/512:ℝ)
    (125/512:ℝ) (1351372542879/100000000000000:ℝ) (-6580191396819706755270939/50000000000000000000000000:ℝ) (1004906517591051750832173/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_124
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0373).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_124 :
    (∫ x in (31/128:ℝ)..(125/512:ℝ), x^10*thetaFirstMode x) ≤ (19261087950599/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/128:ℝ) (125/512:ℝ)
    (537996463/39062500000:ℝ) (270274948993/20000000000000:ℝ) (1004906517591051750832173/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_124 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0373).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_125 :
    (2559008502783/125000000000000000000000:ℝ) ≤ ∫ x in (125/512:ℝ)..(63/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-411131979016656269324453890137/3125000000000000000000000000000:ℝ)*(thetaPowerMass 11 (125/512:ℝ) (63/256:ℝ)-(262135666824211125/1073524536622218752:ℝ)*thetaPowerMass 10 (125/512:ℝ) (63/256:ℝ)) ≤
      thetaFirstModeFirst (262135666824211125/1073524536622218752:ℝ)*(thetaPowerMass 11 (125/512:ℝ) (63/256:ℝ)-(262135666824211125/1073524536622218752:ℝ)*thetaPowerMass 10 (125/512:ℝ) (63/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0192.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (125/512:ℝ) (63/256:ℝ)
    (262135666824211125/1073524536622218752:ℝ) (168853057581/12500000000000:ℝ) (-411131979016656269324453890137/3125000000000000000000000000000:ℝ) (248810407355786208215281/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_125
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0377).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_125 :
    (∫ x in (125/512:ℝ)..(63/256:ℝ), x^10*thetaFirstMode x) ≤ (2047211069289/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (125/512:ℝ) (63/256:ℝ)
    (270274948993/20000000000000:ℝ) (1325861886877/100000000000000:ℝ) (248810407355786208215281/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_125 (thetaFirstMode_refined_node_0373).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_126 :
    (10871861638709/500000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(127/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-9977824918679670288629/78125000000000000000000:ℝ)*(thetaPowerMass 11 (63/256:ℝ) (127/512:ℝ)-(127/512:ℝ)*thetaPowerMass 10 (63/256:ℝ) (127/512:ℝ)) ≤
      thetaFirstModeFirst (127/512:ℝ)*(thetaPowerMass 11 (63/256:ℝ) (127/512:ℝ)-(127/512:ℝ)*thetaPowerMass 10 (63/256:ℝ) (127/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0194.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (63/256:ℝ) (127/512:ℝ)
    (127/512:ℝ) (162590818501/12500000000000:ℝ) (-9977824918679670288629/78125000000000000000000:ℝ) (492791984305824218247837/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_126
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0379).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_126 :
    (∫ x in (63/256:ℝ)..(127/512:ℝ), x^10*thetaFirstMode x) ≤ (5435941000941/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (63/256:ℝ) (127/512:ℝ)
    (1325861886877/100000000000000:ℝ) (130072868419/10000000000000:ℝ) (492791984305824218247837/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_126 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0379).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_127 :
    (11539059771087/500000000000000000000000:ℝ) ≤ ∫ x in (127/512:ℝ)..(1/4:ℝ), x^10*thetaFirstMode x := by
  have hd : (-159595011340944729628889603367/1250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (127/512:ℝ) (1/4:ℝ)-(1511920914525505143/6094295942728092160:ℝ)*thetaPowerMass 10 (127/512:ℝ) (1/4:ℝ)) ≤
      thetaFirstModeFirst (1511920914525505143/6094295942728092160:ℝ)*(thetaPowerMass 11 (127/512:ℝ) (1/4:ℝ)-(1511920914525505143/6094295942728092160:ℝ)*thetaPowerMass 10 (127/512:ℝ) (1/4:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0195.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (127/512:ℝ) (1/4:ℝ)
    (1511920914525505143/6094295942728092160:ℝ) (650101513471/50000000000000:ℝ) (-159595011340944729628889603367/1250000000000000000000000000000:ℝ) (975934895029726802729679/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_127
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0383).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_127 :
    (∫ x in (127/512:ℝ)..(1/4:ℝ), x^10*thetaFirstMode x) ≤ (5769542082453/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (127/512:ℝ) (1/4:ℝ)
    (130072868419/10000000000000:ℝ) (1275971452837/100000000000000:ℝ) (975934895029726802729679/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_127 (thetaFirstMode_refined_node_0379).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
