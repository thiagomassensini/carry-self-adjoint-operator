import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature03
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative04
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative05
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative06

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_096 :
    (1760815555906553723/40000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(97/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-24553476373019469343849424389/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/16:ℝ) (97/512:ℝ)-(3/16:ℝ)*thetaPowerMass 0 (3/16:ℝ) (97/512:ℝ)) ≤
      thetaFirstModeFirst (3/16:ℝ)*(thetaPowerMass 1 (3/16:ℝ) (97/512:ℝ)-(3/16:ℝ)*thetaPowerMass 0 (3/16:ℝ) (97/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0148.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/16:ℝ) (97/512:ℝ)
    (3/16:ℝ) (2272945399673/100000000000000:ℝ) (-24553476373019469343849424389/125000000000000000000000000000:ℝ) (79542980257604461978243/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_096
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0288).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_096 :
    (∫ x in (3/16:ℝ)..(97/512:ℝ), x^0*thetaFirstMode x) ≤ (2751279069458733993/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/16:ℝ) (97/512:ℝ)
    (5682371767/250000000000:ℝ) (446965567181/20000000000000:ℝ) (79542980257604461978243/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_096 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0289).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_097 :
    (43280589264707831867/1000000000000000000000000:ℝ) ≤ ∫ x in (97/512:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2423309469003666491290107722139/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (97/512:ℝ) (49/256:ℝ)-(133804837701602793/706068831528348160:ℝ)*thetaPowerMass 0 (97/512:ℝ) (49/256:ℝ)) ≤
      thetaFirstModeFirst (133804837701602793/706068831528348160:ℝ)*(thetaPowerMass 1 (97/512:ℝ) (49/256:ℝ)-(133804837701602793/706068831528348160:ℝ)*thetaPowerMass 0 (97/512:ℝ) (49/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0150.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (97/512:ℝ) (49/256:ℝ)
    (133804837701602793/706068831528348160:ℝ) (1116892008393/50000000000000:ℝ) (-2423309469003666491290107722139/12500000000000000000000000000000:ℝ) (631701378085954983459/500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_097
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0293).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_097 :
    (∫ x in (97/512:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x) ≤ (2705041483978888427/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (97/512:ℝ) (49/256:ℝ)
    (446965567181/20000000000000:ℝ) (219719245643/10000000000000:ℝ) (631701378085954983459/500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_097 (thetaFirstMode_refined_node_0289).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_098 :
    (21275117715228526801/500000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(99/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-478640971434709097493736141841/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (49/256:ℝ) (99/512:ℝ)-(49/256:ℝ)*thetaPowerMass 0 (49/256:ℝ) (99/512:ℝ)) ≤
      thetaFirstModeFirst (49/256:ℝ)*(thetaPowerMass 1 (49/256:ℝ) (99/512:ℝ)-(49/256:ℝ)*thetaPowerMass 0 (49/256:ℝ) (99/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0151.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (49/256:ℝ) (99/512:ℝ)
    (49/256:ℝ) (439437846891/20000000000000:ℝ) (-478640971434709097493736141841/2500000000000000000000000000000:ℝ) (250816855496097153114469/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_098
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0294).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_098 :
    (∫ x in (49/256:ℝ)..(99/512:ℝ), x^0*thetaFirstMode x) ≤ (21275155031215481111/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/256:ℝ) (99/512:ℝ)
    (219719245643/10000000000000:ℝ) (1080019513247/50000000000000:ℝ) (250816855496097153114469/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_098 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0295).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_099 :
    (8365852369151521757/200000000000000000000000:ℝ) ≤ ∫ x in (99/512:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1889319597122152687153954521623/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (99/512:ℝ) (25/128:ℝ)-(160775853321491991/831261189349250560:ℝ)*thetaPowerMass 0 (99/512:ℝ) (25/128:ℝ)) ≤
      thetaFirstModeFirst (160775853321491991/831261189349250560:ℝ)*(thetaPowerMass 1 (99/512:ℝ) (25/128:ℝ)-(160775853321491991/831261189349250560:ℝ)*thetaPowerMass 0 (99/512:ℝ) (25/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0153.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (99/512:ℝ) (25/128:ℝ)
    (160775853321491991/831261189349250560:ℝ) (2159042234709/100000000000000:ℝ) (-1889319597122152687153954521623/10000000000000000000000000000000:ℝ) (311183437377524429533721/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_099
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0299).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_099 :
    (∫ x in (99/512:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x) ≤ (41829334764545786569/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (99/512:ℝ) (25/128:ℝ)
    (1080019513247/50000000000000:ℝ) (530840997859/25000000000000:ℝ) (311183437377524429533721/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_099 (thetaFirstMode_refined_node_0295).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_100 :
    (1644703809359282371/40000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(101/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-582992605756223555107765103111/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (25/128:ℝ) (101/512:ℝ)-(25/128:ℝ)*thetaPowerMass 0 (25/128:ℝ) (101/512:ℝ)) ≤
      thetaFirstModeFirst (25/128:ℝ)*(thetaPowerMass 1 (25/128:ℝ) (101/512:ℝ)-(25/128:ℝ)*thetaPowerMass 0 (25/128:ℝ) (101/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0154.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (25/128:ℝ) (101/512:ℝ)
    (25/128:ℝ) (1061680426651/50000000000000:ℝ) (-582992605756223555107765103111/3125000000000000000000000000000:ℝ) (1235352673532054159865149/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_100
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0300).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_100 :
    (∫ x in (25/128:ℝ)..(101/512:ℝ), x^0*thetaFirstMode x) ≤ (41117668302473013467/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/128:ℝ) (101/512:ℝ)
    (530840997859/25000000000000:ℝ) (417432756869/20000000000000:ℝ) (1235352673532054159865149/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_100 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0301).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_101 :
    (20207584759260477783/500000000000000000000000:ℝ) ≤ ∫ x in (101/512:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-575224997641594188646699268061/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (101/512:ℝ) (51/256:ℝ)-(192475564448517009/975462843111554560:ℝ)*thetaPowerMass 0 (101/512:ℝ) (51/256:ℝ)) ≤
      thetaFirstModeFirst (192475564448517009/975462843111554560:ℝ)*(thetaPowerMass 1 (101/512:ℝ) (51/256:ℝ)-(192475564448517009/975462843111554560:ℝ)*thetaPowerMass 0 (101/512:ℝ) (51/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0156.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (101/512:ℝ) (51/256:ℝ)
    (192475564448517009/975462843111554560:ℝ) (2086211786141/100000000000000:ℝ) (-575224997641594188646699268061/3125000000000000000000000000000:ℝ) (1225942550278573731374667/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_101
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0305).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_101 :
    (∫ x in (101/512:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x) ≤ (10103810223866603149/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (101/512:ℝ) (51/256:ℝ)
    (417432756869/20000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1225942550278573731374667/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_101 (thetaFirstMode_refined_node_0301).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_102 :
    (9930477754387745881/250000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(103/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9086602378078348879272635627313/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (51/256:ℝ) (103/512:ℝ)-(51/256:ℝ)*thetaPowerMass 0 (51/256:ℝ) (103/512:ℝ)) ≤
      thetaFirstModeFirst (51/256:ℝ)*(thetaPowerMass 1 (51/256:ℝ) (103/512:ℝ)-(51/256:ℝ)*thetaPowerMass 0 (51/256:ℝ) (103/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0157.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (51/256:ℝ) (103/512:ℝ)
    (51/256:ℝ) (2051431771071/100000000000000:ℝ) (-9086602378078348879272635627313/50000000000000000000000000000000:ℝ) (608252439780117264523113/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_102
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0306).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_102 :
    (∫ x in (51/256:ℝ)..(103/512:ℝ), x^0*thetaFirstMode x) ≤ (19860991270442897307/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/256:ℝ) (103/512:ℝ)
    (2051434826679/100000000000000:ℝ) (403234705761/20000000000000:ℝ) (608252439780117264523113/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_102 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0307).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_103 :
    (39037753171575524673/1000000000000000000000000:ℝ) ≤ ∫ x in (103/512:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-22410669733251202917470933647/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (103/512:ℝ) (13/64:ℝ)-(229614139092996207/1141096218995868160:ℝ)*thetaPowerMass 0 (103/512:ℝ) (13/64:ℝ)) ≤
      thetaFirstModeFirst (229614139092996207/1141096218995868160:ℝ)*(thetaPowerMass 1 (103/512:ℝ) (13/64:ℝ)-(229614139092996207/1141096218995868160:ℝ)*thetaPowerMass 0 (103/512:ℝ) (13/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0159.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (103/512:ℝ) (13/64:ℝ)
    (229614139092996207/1141096218995868160:ℝ) (1007632108921/50000000000000:ℝ) (-22410669733251202917470933647/125000000000000000000000000000:ℝ) (603520579949104592553451/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_103
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0311).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_103 :
    (∫ x in (103/512:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x) ≤ (39037823025124973873/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (103/512:ℝ) (13/64:ℝ)
    (403234705761/20000000000000:ℝ) (990688145289/50000000000000:ℝ) (603520579949104592553451/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_103 (thetaFirstMode_refined_node_0307).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_104 :
    (38362621938429580473/1000000000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(105/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4424502090121606102395453505377/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (13/64:ℝ) (105/512:ℝ)-(13/64:ℝ)*thetaPowerMass 0 (13/64:ℝ) (105/512:ℝ)) ≤
      thetaFirstModeFirst (13/64:ℝ)*(thetaPowerMass 1 (13/64:ℝ) (105/512:ℝ)-(13/64:ℝ)*thetaPowerMass 0 (13/64:ℝ) (105/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0160.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (13/64:ℝ) (105/512:ℝ)
    (13/64:ℝ) (79254932647/4000000000000:ℝ) (-4424502090121606102395453505377/25000000000000000000000000000000:ℝ) (1197552888164553565647723/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_104
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0312).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_104 :
    (∫ x in (13/64:ℝ)..(105/512:ℝ), x^0*thetaFirstMode x) ≤ (38362691934988944883/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/64:ℝ) (105/512:ℝ)
    (990688145289/50000000000000:ℝ) (1947039501927/100000000000000:ℝ) (1197552888164553565647723/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_104 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0313).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_105 :
    (37696450320031779681/1000000000000000000000000:ℝ) ≤ ∫ x in (105/512:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4364311752639487618421290283097/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (105/512:ℝ) (53/256:ℝ)-(54598255949620845/266167146581207552:ℝ)*thetaPowerMass 0 (105/512:ℝ) (53/256:ℝ)) ≤
      thetaFirstModeFirst (54598255949620845/266167146581207552:ℝ)*(thetaPowerMass 1 (105/512:ℝ) (53/256:ℝ)-(54598255949620845/266167146581207552:ℝ)*thetaPowerMass 0 (105/512:ℝ) (53/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0162.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (105/512:ℝ) (53/256:ℝ)
    (54598255949620845/266167146581207552:ℝ) (1946170889819/100000000000000:ℝ) (-4364311752639487618421290283097/25000000000000000000000000000000:ℝ) (237608311840065476240513/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_105
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0317).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_105 :
    (∫ x in (105/512:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x) ≤ (471206483359604227/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (105/512:ℝ) (53/256:ℝ)
    (1947039501927/100000000000000:ℝ) (1913159543403/100000000000000:ℝ) (237608311840065476240513/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_105 (thetaFirstMode_refined_node_0313).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_106 :
    (4629895494884848081/125000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(107/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-861510744997221884050428265839/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (53/256:ℝ) (107/512:ℝ)-(53/256:ℝ)*thetaPowerMass 0 (53/256:ℝ) (107/512:ℝ)) ≤
      thetaFirstModeFirst (53/256:ℝ)*(thetaPowerMass 1 (53/256:ℝ) (107/512:ℝ)-(53/256:ℝ)*thetaPowerMass 0 (53/256:ℝ) (107/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0163.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (53/256:ℝ) (107/512:ℝ)
    (53/256:ℝ) (23914458111/1250000000000:ℝ) (-861510744997221884050428265839/5000000000000000000000000000000:ℝ) (4714034661840215647083/4000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_106
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0318).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_106 :
    (∫ x in (53/256:ℝ)..(107/512:ℝ), x^0*thetaFirstMode x) ≤ (37039232447343156603/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (53/256:ℝ) (107/512:ℝ)
    (1913159543403/100000000000000:ℝ) (117483299173/6250000000000:ℝ) (4714034661840215647083/4000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_106 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0319).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_107 :
    (7278139092557224281/200000000000000000000000:ℝ) ≤ ∫ x in (107/512:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-8496686169668207224991266035167/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (107/512:ℝ) (27/128:ℝ)-(323505440094667743/1547628340508700160:ℝ)*thetaPowerMass 0 (107/512:ℝ) (27/128:ℝ)) ≤
      thetaFirstModeFirst (323505440094667743/1547628340508700160:ℝ)*(thetaPowerMass 1 (107/512:ℝ) (27/128:ℝ)-(323505440094667743/1547628340508700160:ℝ)*thetaPowerMass 0 (107/512:ℝ) (27/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0165.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (107/512:ℝ) (27/128:ℝ)
    (323505440094667743/1547628340508700160:ℝ) (1878902994507/100000000000000:ℝ) (-8496686169668207224991266035167/50000000000000000000000000000000:ℝ) (73059731039782495279543/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_107
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0323).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_107 :
    (∫ x in (107/512:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x) ≤ (36390762325364649073/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (107/512:ℝ) (27/128:ℝ)
    (117483299173/6250000000000:ℝ) (1846755595551/100000000000000:ℝ) (73059731039782495279543/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_107 (thetaFirstMode_refined_node_0319).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_108 :
    (35750970203896569949/1000000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(109/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2096232550390949966932539197319/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (27/128:ℝ) (109/512:ℝ)-(27/128:ℝ)*thetaPowerMass 0 (27/128:ℝ) (109/512:ℝ)) ≤
      thetaFirstModeFirst (27/128:ℝ)*(thetaPowerMass 1 (27/128:ℝ) (109/512:ℝ)-(27/128:ℝ)*thetaPowerMass 0 (27/128:ℝ) (109/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0166.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (27/128:ℝ) (109/512:ℝ)
    (27/128:ℝ) (1846752779581/100000000000000:ℝ) (-2096232550390949966932539197319/12500000000000000000000000000000:ℝ) (289846034826571327379441/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_108
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0324).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_108 :
    (∫ x in (27/128:ℝ)..(109/512:ℝ), x^0*thetaFirstMode x) ≤ (17875518601218585557/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/128:ℝ) (109/512:ℝ)
    (1846755595551/100000000000000:ℝ) (1814224325637/100000000000000:ℝ) (289846034826571327379441/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_108 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0325).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_109 :
    (35119920439119391027/1000000000000000000000000:ℝ) ≤ ∫ x in (109/512:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-413423645529846024625133656701/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (109/512:ℝ) (55/256:ℝ)-(382163785687980441/1794715319477839360:ℝ)*thetaPowerMass 0 (109/512:ℝ) (55/256:ℝ)) ≤
      thetaFirstModeFirst (382163785687980441/1794715319477839360:ℝ)*(thetaPowerMass 1 (109/512:ℝ) (55/256:ℝ)-(382163785687980441/1794715319477839360:ℝ)*thetaPowerMass 0 (109/512:ℝ) (55/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0168.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (109/512:ℝ) (55/256:ℝ)
    (382163785687980441/1794715319477839360:ℝ) (113339473489/6250000000000:ℝ) (-413423645529846024625133656701/2500000000000000000000000000000:ℝ) (574897738276723779980301/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_109
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0329).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_109 :
    (∫ x in (109/512:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x) ≤ (1404799433366533617/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (109/512:ℝ) (55/256:ℝ)
    (1814224325637/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (574897738276723779980301/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_109 (thetaFirstMode_refined_node_0325).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_110 :
    (34497471315515493611/1000000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(111/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4079244059912692827950150222181/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (55/256:ℝ) (111/512:ℝ)-(55/256:ℝ)*thetaPowerMass 0 (55/256:ℝ) (111/512:ℝ)) ≤
      thetaFirstModeFirst (55/256:ℝ)*(thetaPowerMass 1 (55/256:ℝ) (111/512:ℝ)-(55/256:ℝ)*thetaPowerMass 0 (55/256:ℝ) (111/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0169.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (55/256:ℝ) (111/512:ℝ)
    (55/256:ℝ) (89106629353/5000000000000:ℝ) (-4079244059912692827950150222181/25000000000000000000000000000000:ℝ) (142523898450206933899489/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_110
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0330).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_110 :
    (∫ x in (55/256:ℝ)..(111/512:ℝ), x^0*thetaFirstMode x) ≤ (6899507368602681193/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (55/256:ℝ) (111/512:ℝ)
    (1782135325809/100000000000000:ℝ) (1750484938319/100000000000000:ℝ) (142523898450206933899489/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_110 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0331).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_111 :
    (33883554783331406197/1000000000000000000000000:ℝ) ≤ ∫ x in (111/512:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2010999603662724551427961111221/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (111/512:ℝ) (7/32:ℝ)-(450092942792761959/2075655332250933760:ℝ)*thetaPowerMass 0 (111/512:ℝ) (7/32:ℝ)) ≤
      thetaFirstModeFirst (450092942792761959/2075655332250933760:ℝ)*(thetaPowerMass 1 (111/512:ℝ) (7/32:ℝ)-(450092942792761959/2075655332250933760:ℝ)*thetaPowerMass 0 (111/512:ℝ) (7/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0171.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (111/512:ℝ) (7/32:ℝ)
    (450092942792761959/2075655332250933760:ℝ) (349945509609/20000000000000:ℝ) (-2010999603662724551427961111221/12500000000000000000000000000000:ℝ) (282643186868228365228189/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_111
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0335).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_111 :
    (∫ x in (111/512:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x) ≤ (2117726170600907643/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (111/512:ℝ) (7/32:ℝ)
    (1750484938319/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (282643186868228365228189/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_111 (thetaFirstMode_refined_node_0331).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_112 :
    (16639047904222712637/500000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(113/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1587158913934684595296801966503/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/32:ℝ) (113/512:ℝ)-(7/32:ℝ)*thetaPowerMass 0 (7/32:ℝ) (113/512:ℝ)) ≤
      thetaFirstModeFirst (7/32:ℝ)*(thetaPowerMass 1 (7/32:ℝ) (113/512:ℝ)-(7/32:ℝ)*thetaPowerMass 0 (7/32:ℝ) (113/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0172.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/32:ℝ) (113/512:ℝ)
    (7/32:ℝ) (429816709153/25000000000000:ℝ) (-1587158913934684595296801966503/10000000000000000000000000000000:ℝ) (70058851663064255029919/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_112
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0336).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_112 :
    (∫ x in (7/32:ℝ)..(113/512:ℝ), x^0*thetaFirstMode x) ≤ (33278159883766609587/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/32:ℝ) (113/512:ℝ)
    (1719269499473/100000000000000:ℝ) (844242670087/50000000000000:ℝ) (70058851663064255029919/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_112 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0337).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_113 :
    (16340513039321190707/500000000000000000000000:ℝ) ≤ ∫ x in (113/512:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7823275043007384070353665834951/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (113/512:ℝ) (57/256:ℝ)-(528550581246993657/2394348818532252160:ℝ)*thetaPowerMass 0 (113/512:ℝ) (57/256:ℝ)) ≤
      thetaFirstModeFirst (528550581246993657/2394348818532252160:ℝ)*(thetaPowerMass 1 (113/512:ℝ) (57/256:ℝ)-(528550581246993657/2394348818532252160:ℝ)*thetaPowerMass 0 (113/512:ℝ) (57/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0174.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (113/512:ℝ) (57/256:ℝ)
    (528550581246993657/2394348818532252160:ℝ) (1687761714569/100000000000000:ℝ) (-7823275043007384070353665834951/50000000000000000000000000000000:ℝ) (277824822626642708938421/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_113
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0341).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_113 :
    (∫ x in (113/512:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x) ≤ (16340544297563087043/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (113/512:ℝ) (57/256:ℝ)
    (844242670087/50000000000000:ℝ) (1658128786473/100000000000000:ℝ) (277824822626642708938421/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_113 (thetaFirstMode_refined_node_0337).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_114 :
    (32092270422519260409/1000000000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(115/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7716860608341322408476982267047/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (57/256:ℝ) (115/512:ℝ)-(57/256:ℝ)*thetaPowerMass 0 (57/256:ℝ) (115/512:ℝ)) ≤
      thetaFirstModeFirst (57/256:ℝ)*(thetaPowerMass 1 (57/256:ℝ) (115/512:ℝ)-(57/256:ℝ)*thetaPowerMass 0 (57/256:ℝ) (115/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0175.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (57/256:ℝ) (115/512:ℝ)
    (57/256:ℝ) (829063099083/50000000000000:ℝ) (-7716860608341322408476982267047/50000000000000000000000000000000:ℝ) (44065887975287776582341/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_114
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0342).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_114 :
    (∫ x in (57/256:ℝ)..(115/512:ℝ), x^0*thetaFirstMode x) ≤ (32092333064368625213/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/256:ℝ) (115/512:ℝ)
    (1658128786473/100000000000000:ℝ) (1628196160161/100000000000000:ℝ) (44065887975287776582341/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_114 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0343).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_115 :
    (31511760308694834407/1000000000000000000000000:ℝ) ≤ ∫ x in (115/512:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7606312845547518452462719694997/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (115/512:ℝ) (29/128:ℝ)-(123787575796526235/551012753541565952:ℝ)*thetaPowerMass 0 (115/512:ℝ) (29/128:ℝ)) ≤
      thetaFirstModeFirst (123787575796526235/551012753541565952:ℝ)*(thetaPowerMass 1 (115/512:ℝ) (29/128:ℝ)-(123787575796526235/551012753541565952:ℝ)*thetaPowerMass 0 (115/512:ℝ) (29/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0177.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (115/512:ℝ) (29/128:ℝ)
    (123787575796526235/551012753541565952:ℝ) (813752393251/50000000000000:ℝ) (-7606312845547518452462719694997/50000000000000000000000000000000:ℝ) (545993403897977599816047/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_115
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0347).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_115 :
    (∫ x in (115/512:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x) ≤ (31511821414145540723/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (115/512:ℝ) (29/128:ℝ)
    (1628196160161/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (545993403897977599816047/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_115 (thetaFirstMode_refined_node_0343).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_116 :
    (30939420472476951937/1000000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(117/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1875423749873723130045309540049/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (29/128:ℝ) (117/512:ℝ)-(29/128:ℝ)*thetaPowerMass 0 (29/128:ℝ) (117/512:ℝ)) ≤
      thetaFirstModeFirst (29/128:ℝ)*(thetaPowerMass 1 (29/128:ℝ) (117/512:ℝ)-(29/128:ℝ)*thetaPowerMass 0 (29/128:ℝ) (117/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0178.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (29/128:ℝ) (117/512:ℝ)
    (29/128:ℝ) (399670316053/25000000000000:ℝ) (-1875423749873723130045309540049/12500000000000000000000000000000:ℝ) (541159782154773469745817/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_116
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0348).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_116 :
    (∫ x in (29/128:ℝ)..(117/512:ℝ), x^0*thetaFirstMode x) ≤ (386743521247472119/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/128:ℝ) (117/512:ℝ)
    (1598683779299/100000000000000:ℝ) (313917591757/20000000000000:ℝ) (541159782154773469745817/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_116 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0349).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_117 :
    (30375182206768639999/1000000000000000000000000:ℝ) ≤ ∫ x in (117/512:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1848279894301567142742243227311/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (117/512:ℝ) (59/256:ℝ)-(722812917611120193/3162462922265628160:ℝ)*thetaPowerMass 0 (117/512:ℝ) (59/256:ℝ)) ≤
      thetaFirstModeFirst (722812917611120193/3162462922265628160:ℝ)*(thetaPowerMass 1 (117/512:ℝ) (59/256:ℝ)-(722812917611120193/3162462922265628160:ℝ)*thetaPowerMass 0 (117/512:ℝ) (59/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0180.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (117/512:ℝ) (59/256:ℝ)
    (722812917611120193/3162462922265628160:ℝ) (156892740107/10000000000000:ℝ) (-1848279894301567142742243227311/12500000000000000000000000000000:ℝ) (536323455561854795423377/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_117
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0353).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_117 :
    (∫ x in (117/512:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x) ≤ (6075048384043006357/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (117/512:ℝ) (59/256:ℝ)
    (313917591757/20000000000000:ℝ) (1540905010899/100000000000000:ℝ) (536323455561854795423377/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_117 (thetaFirstMode_refined_node_0349).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_118 :
    (2981897019686515741/100000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(119/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-72903042299312624648030487249/500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (59/256:ℝ) (119/512:ℝ)-(59/256:ℝ)*thetaPowerMass 0 (59/256:ℝ) (119/512:ℝ)) ≤
      thetaFirstModeFirst (59/256:ℝ)*(thetaPowerMass 1 (59/256:ℝ) (119/512:ℝ)-(59/256:ℝ)*thetaPowerMass 0 (59/256:ℝ) (119/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0181.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (59/256:ℝ) (119/512:ℝ)
    (59/256:ℝ) (770451283849/50000000000000:ℝ) (-72903042299312624648030487249/500000000000000000000000000000:ℝ) (1062970283742563086707513/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_118
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0354).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_118 :
    (∫ x in (59/256:ℝ)..(119/512:ℝ), x^0*thetaFirstMode x) ≤ (29819030028617377379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/256:ℝ) (119/512:ℝ)
    (1540905010899/100000000000000:ℝ) (756315622931/50000000000000:ℝ) (1062970283742563086707513/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_118 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0355).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_119 :
    (29270715602699262507/1000000000000000000000000:ℝ) ≤ ∫ x in (119/512:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-897962589555610564127376834331/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (119/512:ℝ) (15/64:ℝ)-(841905060294227391/3621632464243356160:ℝ)*thetaPowerMass 0 (119/512:ℝ) (15/64:ℝ)) ≤
      thetaFirstModeFirst (841905060294227391/3621632464243356160:ℝ)*(thetaPowerMass 1 (119/512:ℝ) (15/64:ℝ)-(841905060294227391/3621632464243356160:ℝ)*thetaPowerMass 0 (119/512:ℝ) (15/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0183.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (119/512:ℝ) (15/64:ℝ)
    (841905060294227391/3621632464243356160:ℝ) (378000034967/25000000000000:ℝ) (-897962589555610564127376834331/6250000000000000000000000000000:ℝ) (1053291110608192099983023/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_119
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0359).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_119 :
    (∫ x in (119/512:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x) ≤ (5854154788645848171/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (119/512:ℝ) (15/64:ℝ)
    (756315622931/50000000000000:ℝ) (148476297237/10000000000000:ℝ) (1053291110608192099983023/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_119 (thetaFirstMode_refined_node_0355).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_120 :
    (28730343102838859709/1000000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(121/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-708269252823811056973420201491/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/64:ℝ) (121/512:ℝ)-(15/64:ℝ)*thetaPowerMass 0 (15/64:ℝ) (121/512:ℝ)) ≤
      thetaFirstModeFirst (15/64:ℝ)*(thetaPowerMass 1 (15/64:ℝ) (121/512:ℝ)-(15/64:ℝ)*thetaPowerMass 0 (15/64:ℝ) (121/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0184.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/64:ℝ) (121/512:ℝ)
    (15/64:ℝ) (1484760599721/100000000000000:ℝ) (-708269252823811056973420201491/5000000000000000000000000000000:ℝ) (521805406388959194943977/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_120
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0360).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_120 :
    (∫ x in (15/64:ℝ)..(121/512:ℝ), x^0*thetaFirstMode x) ≤ (14365200779001149039/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/64:ℝ) (121/512:ℝ)
    (148476297237/10000000000000:ℝ) (728648249079/50000000000000:ℝ) (521805406388959194943977/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_120 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0361).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_121 :
    (28197783766681725419/1000000000000000000000000:ℝ) ≤ ∫ x in (121/512:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1744514871464821679415714520549/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (121/512:ℝ) (61/256:ℝ)-(978130364965943409/4138112237655400960:ℝ)*thetaPowerMass 0 (121/512:ℝ) (61/256:ℝ)) ≤
      thetaFirstModeFirst (978130364965943409/4138112237655400960:ℝ)*(thetaPowerMass 1 (121/512:ℝ) (61/256:ℝ)-(978130364965943409/4138112237655400960:ℝ)*thetaPowerMass 0 (121/512:ℝ) (61/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0186.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (121/512:ℝ) (61/256:ℝ)
    (978130364965943409/4138112237655400960:ℝ) (1456693546909/100000000000000:ℝ) (-1744514871464821679415714520549/12500000000000000000000000000000:ℝ) (516965401780457664772741/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_121
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0365).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_121 :
    (∫ x in (121/512:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x) ≤ (28197840753201629349/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (121/512:ℝ) (61/256:ℝ)
    (728648249079/50000000000000:ℝ) (35755703263/2500000000000:ℝ) (516965401780457664772741/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_121 (thetaFirstMode_refined_node_0361).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_122 :
    (2767296230843457133/100000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(123/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-171971547143478210791669890359/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (61/256:ℝ) (123/512:ℝ)-(61/256:ℝ)*thetaPowerMass 0 (61/256:ℝ) (123/512:ℝ)) ≤
      thetaFirstModeFirst (61/256:ℝ)*(thetaPowerMass 1 (61/256:ℝ) (123/512:ℝ)-(61/256:ℝ)*thetaPowerMass 0 (61/256:ℝ) (123/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0187.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (61/256:ℝ) (123/512:ℝ)
    (61/256:ℝ) (1430225827093/100000000000000:ℝ) (-171971547143478210791669890359/1250000000000000000000000000000:ℝ) (40970099528116381110747/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_122
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0366).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_122 :
    (∫ x in (61/256:ℝ)..(123/512:ℝ), x^0*thetaFirstMode x) ≤ (13836509703030106019/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/256:ℝ) (123/512:ℝ)
    (35755703263/2500000000000:ℝ) (17544427211/1250000000000:ℝ) (40970099528116381110747/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_122 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0367).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_123 :
    (27155809749416413119/1000000000000000000000000:ℝ) ≤ ∫ x in (123/512:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-169404921870063426903633550137/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (123/512:ℝ) (31/128:ℝ)-(1133608087849118607/4717927560779292160:ℝ)*thetaPowerMass 0 (123/512:ℝ) (31/128:ℝ)) ≤
      thetaFirstModeFirst (1133608087849118607/4717927560779292160:ℝ)*(thetaPowerMass 1 (123/512:ℝ) (31/128:ℝ)-(1133608087849118607/4717927560779292160:ℝ)*thetaPowerMass 0 (123/512:ℝ) (31/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0189.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (123/512:ℝ) (31/128:ℝ)
    (1133608087849118607/4717927560779292160:ℝ) (28059562929/2000000000000:ℝ) (-169404921870063426903633550137/1250000000000000000000000000000:ℝ) (50728863175888107675219/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_123
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0371).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_123 :
    (∫ x in (123/512:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x) ≤ (848620793785029569/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (123/512:ℝ) (31/128:ℝ)
    (17544427211/1250000000000:ℝ) (537996463/39062500000:ℝ) (50728863175888107675219/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_123 (thetaFirstMode_refined_node_0367).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_124 :
    (5329250176318771297/200000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(125/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-130445548431422700513789529/976562500000000000000000000:ℝ)*(thetaPowerMass 1 (31/128:ℝ) (125/512:ℝ)-(31/128:ℝ)*thetaPowerMass 0 (31/128:ℝ) (125/512:ℝ)) ≤
      thetaFirstModeFirst (31/128:ℝ)*(thetaPowerMass 1 (31/128:ℝ) (125/512:ℝ)-(31/128:ℝ)*thetaPowerMass 0 (31/128:ℝ) (125/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0190.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (31/128:ℝ) (125/512:ℝ)
    (31/128:ℝ) (275453741949/20000000000000:ℝ) (-130445548431422700513789529/976562500000000000000000000:ℝ) (1004906517591051750832173/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_124
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0372).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_124 :
    (∫ x in (31/128:ℝ)..(125/512:ℝ), x^0*thetaFirstMode x) ≤ (26646306640715354277/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/128:ℝ) (125/512:ℝ)
    (537996463/39062500000:ℝ) (270274948993/20000000000000:ℝ) (1004906517591051750832173/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_124 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0373).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_125 :
    (26144216719536417219/1000000000000000000000000:ℝ) ≤ ∫ x in (125/512:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-411131979016656269324453890137/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (125/512:ℝ) (63/256:ℝ)-(262135666824211125/1073524536622218752:ℝ)*thetaPowerMass 0 (125/512:ℝ) (63/256:ℝ)) ≤
      thetaFirstModeFirst (262135666824211125/1073524536622218752:ℝ)*(thetaPowerMass 1 (125/512:ℝ) (63/256:ℝ)-(262135666824211125/1073524536622218752:ℝ)*thetaPowerMass 0 (125/512:ℝ) (63/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0192.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (125/512:ℝ) (63/256:ℝ)
    (262135666824211125/1073524536622218752:ℝ) (168853057581/12500000000000:ℝ) (-411131979016656269324453890137/3125000000000000000000000000000:ℝ) (248810407355786208215281/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_125
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0377).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_125 :
    (∫ x in (125/512:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x) ≤ (13072135527750456003/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (125/512:ℝ) (63/256:ℝ)
    (270274948993/20000000000000:ℝ) (1325861886877/100000000000000:ℝ) (248810407355786208215281/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_125 (thetaFirstMode_refined_node_0373).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_126 :
    (12824816087378975189/500000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(127/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-324127034919971467866762425939/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (63/256:ℝ) (127/512:ℝ)-(63/256:ℝ)*thetaPowerMass 0 (63/256:ℝ) (127/512:ℝ)) ≤
      thetaFirstModeFirst (63/256:ℝ)*(thetaPowerMass 1 (63/256:ℝ) (127/512:ℝ)-(63/256:ℝ)*thetaPowerMass 0 (63/256:ℝ) (127/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0193.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (63/256:ℝ) (127/512:ℝ)
    (63/256:ℝ) (331464929477/25000000000000:ℝ) (-324127034919971467866762425939/2500000000000000000000000000000:ℝ) (492791984305824218247837/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_126
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0378).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_126 :
    (∫ x in (63/256:ℝ)..(127/512:ℝ), x^0*thetaFirstMode x) ≤ (25649686614510073781/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/256:ℝ) (127/512:ℝ)
    (1325861886877/100000000000000:ℝ) (130072868419/10000000000000:ℝ) (492791984305824218247837/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_126 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0379).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_127 :
    (5032485659244733771/200000000000000000000000:ℝ) ≤ ∫ x in (127/512:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x := by
  have hd : (-159595011340944729628889603367/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (127/512:ℝ) (1/4:ℝ)-(1511920914525505143/6094295942728092160:ℝ)*thetaPowerMass 0 (127/512:ℝ) (1/4:ℝ)) ≤
      thetaFirstModeFirst (1511920914525505143/6094295942728092160:ℝ)*(thetaPowerMass 1 (127/512:ℝ) (1/4:ℝ)-(1511920914525505143/6094295942728092160:ℝ)*thetaPowerMass 0 (127/512:ℝ) (1/4:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0195.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (127/512:ℝ) (1/4:ℝ)
    (1511920914525505143/6094295942728092160:ℝ) (650101513471/50000000000000:ℝ) (-159595011340944729628889603367/1250000000000000000000000000000:ℝ) (975934895029726802729679/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_127
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0383).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_127 :
    (∫ x in (127/512:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x) ≤ (12581240667760783047/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (127/512:ℝ) (1/4:ℝ)
    (130072868419/10000000000000:ℝ) (1275971452837/100000000000000:ℝ) (975934895029726802729679/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_127 (thetaFirstMode_refined_node_0379).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
