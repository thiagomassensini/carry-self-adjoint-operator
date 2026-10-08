import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_096 :
    (1485598435935127629/125000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/8:ℝ) (97/256:ℝ)
    (193/512:ℝ) (304224667353/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_096
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0577).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x) ≤ (2376983600304466587/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_097 :
    (5650251309883692599/500000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (97/256:ℝ) (49/128:ℝ)
    (195/512:ℝ) (56497619/19531250000:ℝ) (394124895899789529/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_097
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0583).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x) ≤ (706289329919213569/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_098 :
    (10740530653251901789/1000000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (49/128:ℝ) (99/256:ℝ)
    (197/512:ℝ) (274933345111/100000000000000:ℝ) (76251226959833959/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_098
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0589).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x) ≤ (10740653524726665171/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_099 :
    (10204082412194289851/1000000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (99/256:ℝ) (25/64:ℝ)
    (199/512:ℝ) (65300267963/25000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_099
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0595).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x) ≤ (5102100782063522649/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_100 :
    (1938076885202610251/200000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (25/64:ℝ) (101/256:ℝ)
    (201/512:ℝ) (248051188579/100000000000000:ℝ) (356296586964953583/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_100
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0601).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x) ≤ (9690499926723897489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_101 :
    (4599339504979919469/500000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (101/256:ℝ) (51/128:ℝ)
    (203/512:ℝ) (235464298503/100000000000000:ℝ) (34420794807094063/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_101
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0607).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x) ≤ (4599395463995239187/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_102 :
    (872822432845052461/100000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (51/128:ℝ) (103/256:ℝ)
    (205/512:ℝ) (223421410591/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_102
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0613).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x) ≤ (8728332732552075779/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_103 :
    (1034786805229379863/125000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (103/256:ℝ) (13/32:ℝ)
    (207/512:ℝ) (211903940763/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_103
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0619).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x) ≤ (8278399400978359691/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_104 :
    (7848179336878815441/1000000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (13/32:ℝ) (105/256:ℝ)
    (209/512:ℝ) (6277928521/3125000000000:ℝ) (30951371593757961/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_104
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0625).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x) ≤ (981035115011253171/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_105 :
    (1487436988175569617/200000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (105/256:ℝ) (53/128:ℝ)
    (211/512:ℝ) (38074591613/20000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_105
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0631).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x) ≤ (7437283217228678829/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_106 :
    (880579140008931381/125000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (53/128:ℝ) (107/256:ℝ)
    (213/512:ℝ) (90162158371/50000000000000:ℝ) (143847313866595999/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_106
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0637).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x) ≤ (880591019835652863/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_107 :
    (13027073560121791/1953125000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (107/256:ℝ) (27/64:ℝ)
    (215/512:ℝ) (42682709031/25000000000000:ℝ) (55435413091796449/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_107
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0643).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x) ≤ (1333990706535494703/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_108 :
    (315611212356385113/50000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (27/64:ℝ) (109/256:ℝ)
    (217/512:ℝ) (80787985213/50000000000000:ℝ) (133459873385764947/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_108
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0649).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x) ≤ (6312313017287564229/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_109 :
    (1194218078855531813/200000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (109/256:ℝ) (55/128:ℝ)
    (219/512:ℝ) (7642178973/5000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_109
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0655).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x) ≤ (5971176133554056869/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_110 :
    (2822922703630761863/500000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (55/128:ℝ) (111/256:ℝ)
    (221/512:ℝ) (36129481767/25000000000000:ℝ) (247181206801729151/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_110
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0661).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x) ≤ (2822964092162304399/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_111 :
    (1333972573996323577/250000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (111/256:ℝ) (7/16:ℝ)
    (223/512:ℝ) (68291839601/50000000000000:ℝ) (59424277358972619/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_111
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0667).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x) ≤ (2667985089610408817/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_112 :
    (1260160422115208371/250000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/16:ℝ) (113/256:ℝ)
    (225/512:ℝ) (129025901651/100000000000000:ℝ) (57116879476505503/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_112
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0673).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x) ≤ (5040718746027551781/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_113 :
    (4759531729418109927/1000000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (113/256:ℝ) (57/128:ℝ)
    (227/512:ℝ) (24366011489/20000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_113
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0679).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x) ≤ (2379803014546733823/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_114 :
    (4492007965754149673/1000000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (57/128:ℝ) (115/256:ℝ)
    (229/512:ℝ) (57491001961/50000000000000:ℝ) (105381898272623603/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_114
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0685).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x) ≤ (1123019893758667351/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_115 :
    (4237533220458634799/1000000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (115/256:ℝ) (29/64:ℝ)
    (231/512:ℝ) (216935979/200000000000:ℝ) (4045703083264843/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_115
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0691).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x) ≤ (1059400551591971663/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_116 :
    (998896363597909087/250000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (29/64:ℝ) (117/256:ℝ)
    (233/512:ℝ) (51137325069/50000000000000:ℝ) (97026004163419267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_116
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0697).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x) ≤ (998912970880353701/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_117 :
    (376565761704595253/100000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (117/256:ℝ) (59/128:ℝ)
    (235/512:ℝ) (19277801103/20000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_117
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0703).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x) ≤ (3765721555478407439/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_118 :
    (1773628743244700037/500000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (59/128:ℝ) (119/256:ℝ)
    (237/512:ℝ) (22699613733/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_118
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0709).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x) ≤ (443414874974329669/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_119 :
    (3339907499424562807/1000000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (119/256:ℝ) (15/32:ℝ)
    (239/512:ℝ) (85490772961/100000000000000:ℝ) (42699420868835591/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_119
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0715).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x) ≤ (667993330511424877/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_120 :
    (3143144571014318863/1000000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (15/32:ℝ) (121/256:ℝ)
    (241/512:ℝ) (314273847/390625000000:ℝ) (3270357328822397/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_120
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0721).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x) ≤ (1571600714180993637/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_121 :
    (2956519905996512629/1000000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (121/256:ℝ) (61/128:ℝ)
    (243/512:ℝ) (75676961597/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_121
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0727).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x) ≤ (739143632817173373/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_122 :
    (27795988008925637/10000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (61/128:ℝ) (123/256:ℝ)
    (245/512:ℝ) (35574107533/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_122
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0733).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x) ≤ (55593025141250577/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_123 :
    (16324752736359893/6250000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (123/256:ℝ) (31/64:ℝ)
    (247/512:ℝ) (4178568283/6250000000000:ℝ) (35761737420459491/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_123
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0739).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x) ≤ (261201078723592799/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_124 :
    (1226598835571080611/500000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (31/64:ℝ) (125/256:ℝ)
    (249/512:ℝ) (62793171289/100000000000000:ℝ) (68333801879586489/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_124
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0745).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x) ≤ (490649195078291761/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_125 :
    (287864600826863707/125000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (125/256:ℝ) (63/128:ℝ)
    (251/512:ℝ) (58946373017/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_125
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0751).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x) ≤ (2302963126438149437/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_126 :
    (1080368686941733969/500000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (63/128:ℝ) (127/256:ℝ)
    (253/512:ℝ) (27653478959/50000000000000:ℝ) (24910558921058049/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_126
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0757).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x) ≤ (270097721153156453/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_127 :
    (1013145946519392137/500000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (127/256:ℝ) (1/2:ℝ)
    (255/512:ℝ) (51865518759/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_127
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0763).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x) ≤ (2026334422984931451/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator
