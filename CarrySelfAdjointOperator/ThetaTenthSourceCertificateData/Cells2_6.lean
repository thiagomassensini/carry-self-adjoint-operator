import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature6

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_192 :
    (2338449789284587/500000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/4:ℝ) (193/256:ℝ)
    (85600515/113837056:ℝ) (52913951/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_192
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1154).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x) ≤ (935461664714487/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/4:ℝ) (193/256:ℝ)
    (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_192 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_193 :
    (4238026386096227/1000000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (193/256:ℝ) (97/128:ℝ)
    (86941485/115022848:ℝ) (23726973/12500000000000:ℝ) (323729221238183/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_193
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1160).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x) ≤ (2119202580830067/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (193/256:ℝ) (97/128:ℝ)
    (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ) (323729221238183/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_193 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_194 :
    (479599269301707/125000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (97/128:ℝ) (195/256:ℝ)
    (88296387/116214784:ℝ) (17008141/10000000000000:ℝ) (589561754626943/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_194
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1166).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x) ≤ (959286213004731/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (97/128:ℝ) (195/256:ℝ)
    (179715241/100000000000000:ℝ) (257537/160000000000:ℝ) (589561754626943/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_194 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_195 :
    (3470322653313149/1000000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (195/256:ℝ) (49/64:ℝ)
    (89665293/117412864:ℝ) (152265249/100000000000000:ℝ) (536365970577363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_195
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1172).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x) ≤ (3470647047219359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (195/256:ℝ) (49/64:ℝ)
    (257537/160000000000:ℝ) (72018211/50000000000000:ℝ) (536365970577363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_195 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_196 :
    (3135919959832909/1000000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (49/64:ℝ) (197/256:ℝ)
    (91048275/118617088:ℝ) (68097503/50000000000000:ℝ) (975067464150909/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_196
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1178).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x) ≤ (196013734270627/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (49/64:ℝ) (197/256:ℝ)
    (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ) (975067464150909/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_196 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_197 :
    (2831073005720449/1000000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (197/256:ℝ) (99/128:ℝ)
    (92445405/119827456:ℝ) (121712449/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_197
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1184).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x) ≤ (2831349783518633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (197/256:ℝ) (99/128:ℝ)
    (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_197 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_198 :
    (510687632932251/200000000000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (99/128:ℝ) (199/256:ℝ)
    (93856755/121043968:ℝ) (108672389/100000000000000:ℝ) (100427867549897/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_198
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1190).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x) ≤ (1276846743308737/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (99/128:ℝ) (199/256:ℝ)
    (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ) (100427867549897/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_198 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_199 :
    (287604043402679/125000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (199/256:ℝ) (25/32:ℝ)
    (95282397/122266624:ℝ) (24235433/25000000000000:ℝ) (36414495119801/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_199
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1196).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x) ≤ (1150533813801911/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (199/256:ℝ) (25/32:ℝ)
    (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_199 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_200 :
    (1035612049487373/500000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (25/32:ℝ) (201/256:ℝ)
    (96722403/123495424:ℝ) (43199289/50000000000000:ℝ) (659574402541617/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_200
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1202).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x) ≤ (103572035972547/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (25/32:ℝ) (201/256:ℝ)
    (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_200 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_201 :
    (465681322353961/250000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (201/256:ℝ) (101/128:ℝ)
    (98176845/124730368:ℝ) (76931389/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_201
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1208).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x) ≤ (58216391891361/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (201/256:ℝ) (101/128:ℝ)
    (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_201 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_202 :
    (20919785928261/12500000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (101/128:ℝ) (203/256:ℝ)
    (99645795/125971456:ℝ) (68438201/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_202
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1214).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x) ≤ (1673765965003289/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (101/128:ℝ) (203/256:ℝ)
    (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_202 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_203 :
    (1502171031863991/1000000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (203/256:ℝ) (51/64:ℝ)
    (101129325/127218688:ℝ) (6082589/10000000000000:ℝ) (12180020474541/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_203
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1220).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x) ≤ (1502339121108709/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (203/256:ℝ) (51/64:ℝ)
    (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ) (12180020474541/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_203 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_204 :
    (1346983646039519/1000000000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (51/64:ℝ) (205/256:ℝ)
    (102627507/128472064:ℝ) (3375593/6250000000000:ℝ) (54947028858241/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_204
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1226).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x) ≤ (1347137810083989/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (51/64:ℝ) (205/256:ℝ)
    (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ) (54947028858241/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_204 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_205 :
    (1206627026409611/1000000000000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (205/256:ℝ) (103/128:ℝ)
    (104140413/129731584:ℝ) (23955771/50000000000000:ℝ) (396227085824353/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_205
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1232).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x) ≤ (1206768284034289/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (205/256:ℝ) (103/128:ℝ)
    (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ) (396227085824353/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_205 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_206 :
    (1079812973853191/1000000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (103/128:ℝ) (207/256:ℝ)
    (105668115/130997248:ℝ) (21230759/50000000000000:ℝ) (22300504829651/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_206
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1238).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x) ≤ (539971128787059/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (103/128:ℝ) (207/256:ℝ)
    (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_206 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_207 :
    (965352073088811/1000000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (207/256:ℝ) (13/16:ℝ)
    (107210685/132269056:ℝ) (37595243/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_207
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1244).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x) ≤ (965470284497719/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (207/256:ℝ) (13/16:ℝ)
    (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_207 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_208 :
    (215536861199547/250000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (13/16:ℝ) (209/256:ℝ)
    (108768195/133547008:ℝ) (4156799/12500000000000:ℝ) (28849907635213/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_208
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1250).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^2*thetaFirstMode x) ≤ (862255429879181/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (13/16:ℝ) (209/256:ℝ)
    (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_208 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_209 :
    (6009286372133/7812500000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (209/256:ℝ) (105/128:ℝ)
    (110340717/134831104:ℝ) (14693003/50000000000000:ℝ) (25903420067651/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_209
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1256).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x) ≤ (30771487990567/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (209/256:ℝ) (105/128:ℝ)
    (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ) (25903420067651/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_209 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_210 :
    (685545959543941/1000000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (105/128:ℝ) (211/256:ℝ)
    (111928323/136121344:ℝ) (12971023/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_210
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1262).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^2*thetaFirstMode x) ≤ (85704473723033/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (105/128:ℝ) (211/256:ℝ)
    (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_210 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_211 :
    (610364815193091/1000000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (211/256:ℝ) (53/64:ℝ)
    (113531085/137417728:ℝ) (22878979/100000000000000:ℝ) (26025045292513/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_211
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1268).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x) ≤ (610446623302197/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (211/256:ℝ) (53/64:ℝ)
    (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ) (26025045292513/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_211 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_212 :
    (542860697955361/1000000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (53/64:ℝ) (213/256:ℝ)
    (115149075/138720256:ℝ) (4031479/20000000000000:ℝ) (46593623740507/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_212
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1274).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^2*thetaFirstMode x) ≤ (542935144387079/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (53/64:ℝ) (213/256:ℝ)
    (10740033/50000000000000:ℝ) (151323/800000000000:ℝ) (46593623740507/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_212 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_213 :
    (241157139155473/500000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (213/256:ℝ) (107/128:ℝ)
    (116782365/140028928:ℝ) (2217707/12500000000000:ℝ) (41666673119801/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_213
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1280).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x) ≤ (120595480492611/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (213/256:ℝ) (107/128:ℝ)
    (151323/800000000000:ℝ) (16640047/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_213 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_214 :
    (428066603067743/1000000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (107/128:ℝ) (215/256:ℝ)
    (118431027/141343744:ℝ) (7799781/50000000000000:ℝ) (74444924862353/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_214
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1286).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^2*thetaFirstMode x) ≤ (214064012872789/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (107/128:ℝ) (215/256:ℝ)
    (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_214 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_215 :
    (379514909814563/1000000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (215/256:ℝ) (27/32:ℝ)
    (120095133/142664704:ℝ) (1712757/12500000000000:ℝ) (33217875238267/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_215
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1292).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x) ≤ (379570603823071/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (215/256:ℝ) (27/32:ℝ)
    (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_215 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_216 :
    (168054163291521/500000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (27/32:ℝ) (217/256:ℝ)
    (121774755/143991808:ℝ) (12022939/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_216
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1298).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^2*thetaFirstMode x) ≤ (42019845555679/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (27/32:ℝ) (217/256:ℝ)
    (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_216 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_217 :
    (29734405935647/100000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (217/256:ℝ) (109/128:ℝ)
    (123469965/145325056:ℝ) (1317327/12500000000000:ℝ) (1054879510589/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_217
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1304).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x) ≤ (74347425532981/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (217/256:ℝ) (109/128:ℝ)
    (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ) (1054879510589/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_217 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_218 :
    (52552755097743/200000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (109/128:ℝ) (219/256:ℝ)
    (125180835/146664448:ℝ) (9227861/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_218
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1310).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^2*thetaFirstMode x) ≤ (131402514784467/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (109/128:ℝ) (219/256:ℝ)
    (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_218 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_219 :
    (23195006738493/100000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (219/256:ℝ) (55/64:ℝ)
    (126907437/148009984:ℝ) (2017899/25000000000000:ℝ) (16678757434983/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_219
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1316).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x) ≤ (231987331054957/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (219/256:ℝ) (55/64:ℝ)
    (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_219 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_220 :
    (51130841150789/250000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (55/64:ℝ) (221/256:ℝ)
    (128649843/149361664:ℝ) (881587/12500000000000:ℝ) (37014350035403/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_220
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1322).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^2*thetaFirstMode x) ≤ (102278489855891/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (55/64:ℝ) (221/256:ℝ)
    (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ) (37014350035403/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_220 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_221 :
    (7205551221351/40000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (221/256:ℝ) (111/128:ℝ)
    (130408125/150719488:ℝ) (6155801/100000000000000:ℝ) (410275687759/6250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_221
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1328).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x) ≤ (11260568074727/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (221/256:ℝ) (111/128:ℝ)
    (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ) (410275687759/6250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_221 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_222 :
    (158483462886441/1000000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (111/128:ℝ) (223/256:ℝ)
    (132182355/152083456:ℝ) (2683577/50000000000000:ℝ) (11629122491573/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_222
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1334).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^2*thetaFirstMode x) ≤ (158510738537899/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (111/128:ℝ) (223/256:ℝ)
    (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_222 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_223 :
    (27854773239929/200000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (223/256:ℝ) (7/8:ℝ)
    (133972605/153453568:ℝ) (1168611/25000000000000:ℝ) (6430874207139/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_223
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1340).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x) ≤ (69649182220107/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (223/256:ℝ) (7/8:ℝ)
    (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ) (6430874207139/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_223 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
