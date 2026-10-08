import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_096 :
    (239932353156228567/1000000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (3/8:ℝ) (97/256:ℝ)
    (251071076165/666029999616:ℝ) (38021488771/12500000000000:ℝ) (814502165006677/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_096
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0579).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^4*thetaFirstMode x) ≤ (23993498591851203/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_097 :
    (29717622729478943/125000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (97/256:ℝ) (49/128:ℝ)
    (88117293225/231356268032:ℝ) (289217755749/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_097
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0585).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x) ≤ (23774364439521983/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_098 :
    (117686918026441079/500000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (49/128:ℝ) (99/256:ℝ)
    (278188842685/722983727616:ℝ) (34360733913/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_098
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0591).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^4*thetaFirstMode x) ≤ (29422065825112151/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_099 :
    (232837810432488311/1000000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (99/256:ℝ) (25/64:ℝ)
    (292599252995/752792833536:ℝ) (65289014729/25000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_099
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0597).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x) ≤ (232840527110388431/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_100 :
    (23014004128284717/100000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (25/64:ℝ) (101/256:ℝ)
    (102533584335/261171456512:ℝ) (62002130637/25000000000000:ℝ) (356296586964953583/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_100
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0603).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^4*thetaFirstMode x) ≤ (230142782184785937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_101 :
    (45457576152371773/200000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (101/256:ℝ) (51/128:ℝ)
    (323211343315/815166767616:ℝ) (235423870107/100000000000000:ℝ) (34420794807094063/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_101
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0609).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x) ≤ (113645321969930621/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_102 :
    (28036108875362123/125000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (51/128:ℝ) (103/256:ℝ)
    (339449386325/847768644096:ℝ) (223383115081/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_102
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0615).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^4*thetaFirstMode x) ≤ (112145827234046407/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_103 :
    (55287679569762607/250000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (103/256:ℝ) (13/32:ℝ)
    (118777869945/293779599872:ℝ) (211867677739/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_103
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0621).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x) ≤ (55288380001876449/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_104 :
    (54470316827557367/250000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (13/32:ℝ) (105/256:ℝ)
    (373883110645/915896219136:ℝ) (40171877183/20000000000000:ℝ) (30951371593757961/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_104
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0627).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^4*thetaFirstMode x) ≤ (217884085247558691/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_105 :
    (214488475800263091/1000000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (105/256:ℝ) (53/128:ℝ)
    (392117358155/951460071936:ℝ) (190340475381/100000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_105
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0633).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x) ≤ (107245653932349521/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_106 :
    (210980389282923971/1000000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (53/128:ℝ) (107/256:ℝ)
    (137018732655/329349903872:ℝ) (180293589811/100000000000000:ℝ) (143847313866595999/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_106
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0639).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^4*thetaFirstMode x) ≤ (105491616685033401/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_107 :
    (207365116370163589/1000000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (107/256:ℝ) (27/64:ℝ)
    (430719855475/1025684676096:ℝ) (34140356071/20000000000000:ℝ) (55435413091796449/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_107
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0645).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x) ≤ (51841992588165337/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_108 :
    (203650804455998029/1000000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (27/64:ℝ) (109/256:ℝ)
    (451128939485/1064384687616:ℝ) (161548504811/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_108
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0651).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^4*thetaFirstMode x) ≤ (40730733239594187/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_109 :
    (199845616000815743/1000000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (109/256:ℝ) (55/128:ℝ)
    (157434815265/368056550912:ℝ) (152817626447/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_109
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0657).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x) ≤ (19984848335072229/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_110 :
    (7838308215799547/40000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (55/128:ℝ) (111/256:ℝ)
    (494267760805/1145059662336:ℝ) (18061676553/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_110
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0663).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^4*thetaFirstMode x) ≤ (195960576198311183/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_111 :
    (7679807861564133/40000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (111/256:ℝ) (7/16:ℝ)
    (517040665115/1187074991616:ℝ) (136560531889/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_111
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0669).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x) ≤ (191998068639154911/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_112 :
    (187966161151571731/1000000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (7/16:ℝ) (113/256:ℝ)
    (180215112375/410078700032:ℝ) (32251013427/25000000000000:ℝ) (57116879476505503/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_112
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0675).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^4*thetaFirstMode x) ≤ (11748064524593207/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_113 :
    (45969649470146143/250000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (113/256:ℝ) (57/128:ℝ)
    (565104356635/1274563631616:ℝ) (121809443867/100000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_113
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0681).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x) ≤ (11492591632383747/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_114 :
    (179740412273826927/1000000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (57/128:ℝ) (115/256:ℝ)
    (590440708445/1320078414336:ℝ) (114962562553/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_114
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0687).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^4*thetaFirstMode x) ≤ (7189731014856863/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_115 :
    (175559397646234631/1000000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (115/256:ℝ) (29/64:ℝ)
    (205559261985/455600486912:ℝ) (54224830461/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_115
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0693).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x) ≤ (21945281685153561/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_116 :
    (42835804220931903/250000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (29/64:ℝ) (117/256:ℝ)
    (643839394765/1414753967616:ℝ) (25564344391/25000000000000:ℝ) (97026004163419267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_116
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0699).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^4*thetaFirstMode x) ≤ (1713460633580081/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_117 :
    (83549692621953493/500000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (117/256:ℝ) (59/128:ℝ)
    (671949756275/1463957316096:ℝ) (24093183673/25000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_117
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0705).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x) ≤ (83551110140173377/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_118 :
    (81417627073150397/500000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (59/128:ℝ) (119/256:ℝ)
    (233677837095/504811023872:ℝ) (90783134043/100000000000000:ℝ) (89155610570721081/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_118
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0711).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^4*thetaFirstMode x) ≤ (20354759461910627/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_119 :
    (79278998009385859/500000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (119/256:ℝ) (15/32:ℝ)
    (731115723595/1566202983936:ℝ) (5342272033/6250000000000:ℝ) (42699420868835591/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_119
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0717).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x) ≤ (158560802064610681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_120 :
    (77137295099162153/500000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (15/32:ℝ) (121/256:ℝ)
    (762221883605/1619288987136:ℝ) (80440537629/100000000000000:ℝ) (3270357328822397/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_120
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0723).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^4*thetaFirstMode x) ≤ (38569344690090967/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_121 :
    (74995904954945211/500000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (121/256:ℝ) (61/128:ℝ)
    (264792637305/557904399872:ℝ) (236450633/312500000000:ℝ) (156468455838422989/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_121
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0729).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x) ≤ (7499728952351461/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_122 :
    (145716210343616701/1000000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (61/128:ℝ) (123/256:ℝ)
    (827610162925/1729497924096:ℝ) (71136221209/100000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_122
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0735).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^4*thetaFirstMode x) ≤ (14571895815531609/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_123 :
    (2829082356291211/20000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (123/256:ℝ) (31/64:ℝ)
    (861945428435/1786665647616:ℝ) (33422911431/50000000000000:ℝ) (35761737420459491/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_123
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0741).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x) ≤ (884105265314521/6250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_124 :
    (34302905011845489/250000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (31/64:ℝ) (125/256:ℝ)
    (299136980415/615079680512:ℝ) (31391293371/50000000000000:ℝ) (68333801879586489/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_124
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0747).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^4*thetaFirstMode x) ≤ (68607159853185179/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_125 :
    (132994557546954917/1000000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (125/256:ℝ) (63/128:ℝ)
    (934034378755/1905240961536:ℝ) (58936436357/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_125
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0753).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x) ≤ (26599446096060923/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_126 :
    (128808516068443277/1000000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (63/128:ℝ) (127/256:ℝ)
    (971843866565/1966694447616:ℝ) (691220421/1250000000000:ℝ) (24910558921058049/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_126
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0759).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^4*thetaFirstMode x) ≤ (12881116058460119/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_127 :
    (31164705044429871/250000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (127/256:ℝ) (1/2:ℝ)
    (336955994025/676540908032:ℝ) (25928386587/50000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_127
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0765).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x) ≤ (124661434642856949/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
