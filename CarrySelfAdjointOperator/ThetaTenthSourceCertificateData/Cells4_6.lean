import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature6

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_192 :
    (2644257178125147/1000000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (3/4:ℝ) (193/256:ℝ)
    (7930210043525/10546054596096:ℝ) (211635927/100000000000000:ℝ) (14208294001147/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_192
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1155).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^4*thetaFirstMode x) ≤ (2644488198927987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (3/4:ℝ) (193/256:ℝ)
    (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_192 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_193 :
    (484216523729773/200000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (193/256:ℝ) (97/128:ℝ)
    (2712779610345/3588968463872:ℝ) (47449477/25000000000000:ℝ) (323729221238183/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_193
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1161).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x) ≤ (605324734573317/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (193/256:ℝ) (97/128:ℝ)
    (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ) (323729221238183/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_193 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_194 :
    (1107290483310099/500000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (97/128:ℝ) (195/256:ℝ)
    (8350814750845/10991206887936:ℝ) (42516337/25000000000000:ℝ) (589561754626943/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_194
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1167).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^4*thetaFirstMode x) ≤ (1107391660807477/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (97/128:ℝ) (195/256:ℝ)
    (179715241/100000000000000:ℝ) (257537/160000000000:ℝ) (589561754626943/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_194 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_195 :
    (2023704356419059/1000000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (195/256:ℝ) (49/64:ℝ)
    (8567705548355/11218994843136:ℝ) (152250829/100000000000000:ℝ) (536365970577363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_195
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1173).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x) ≤ (404778692402169/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (195/256:ℝ) (49/64:ℝ)
    (257537/160000000000:ℝ) (72018211/50000000000000:ℝ) (536365970577363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_195 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_196 :
    (923726931182823/500000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (49/64:ℝ) (197/256:ℝ)
    (2929693223055/3816768399872:ℝ) (136182071/100000000000000:ℝ) (975067464150909/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_196
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1179).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^4*thetaFirstMode x) ≤ (923815209243039/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (49/64:ℝ) (197/256:ℝ)
    (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ) (975067464150909/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_196 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_197 :
    (842439320421483/500000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (197/256:ℝ) (99/128:ℝ)
    (9015006262675/11685174084096:ℝ) (15212607/12500000000000:ℝ) (885496145229559/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_197
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1185).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x) ≤ (33700866231981/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (197/256:ℝ) (99/128:ℝ)
    (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_197 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_198 :
    (191884356533247/125000000000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (99/128:ℝ) (199/256:ℝ)
    (9245555185685/11923637807616:ℝ) (13582751/12500000000000:ℝ) (100427867549897/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_198
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1191).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^4*thetaFirstMode x) ≤ (153522830034659/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (99/128:ℝ) (199/256:ℝ)
    (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ) (100427867549897/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_198 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_199 :
    (698592307911007/500000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (199/256:ℝ) (25/32:ℝ)
    (3160265668665/4055244288512:ℝ) (24233111/25000000000000:ℝ) (36414495119801/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_199
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1197).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x) ≤ (698663727165979/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (199/256:ℝ) (25/32:ℝ)
    (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_199 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_200 :
    (635197387304443/500000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (25/32:ℝ) (201/256:ℝ)
    (9720803006005/12411495937536:ℝ) (21597569/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_200
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1203).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^4*thetaFirstMode x) ≤ (1270527602305877/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (25/32:ℝ) (201/256:ℝ)
    (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_200 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_201 :
    (144241959112071/125000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (201/256:ℝ) (101/128:ℝ)
    (9965645186315/12660963887616:ℝ) (3076959/4000000000000:ℝ) (298393710712757/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_201
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1209).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x) ≤ (1154059067543463/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (201/256:ℝ) (101/128:ℝ)
    (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_201 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_202 :
    (209415968249959/200000000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (101/128:ℝ) (203/256:ℝ)
    (3405132089775/4304724588032:ℝ) (34215793/50000000000000:ℝ) (539471835378099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_202
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1215).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^4*thetaFirstMode x) ≤ (209438870432231/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (101/128:ℝ) (203/256:ℝ)
    (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_202 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_203 :
    (237285155090661/250000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (203/256:ℝ) (51/64:ℝ)
    (10470129702835/13171162799616:ℝ) (60819993/100000000000000:ℝ) (12180020474541/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_203
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1221).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x) ≤ (474623395102477/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (203/256:ℝ) (51/64:ℝ)
    (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ) (12180020474541/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_203 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_204 :
    (107433850502353/125000000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (51/64:ℝ) (205/256:ℝ)
    (10729919663645/13431968411136:ℝ) (13501059/25000000000000:ℝ) (54947028858241/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_204
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1227).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^4*thetaFirstMode x) ≤ (859569136287227/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (51/64:ℝ) (205/256:ℝ)
    (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ) (54947028858241/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_204 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_205 :
    (1214783094623/1562500000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (205/256:ℝ) (103/128:ℝ)
    (3664947020385/4565542733312:ℝ) (47906869/100000000000000:ℝ) (396227085824353/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_205
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1233).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x) ≤ (777552159032847/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (205/256:ℝ) (103/128:ℝ)
    (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ) (396227085824353/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_205 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_206 :
    (35126953860223/50000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (103/128:ℝ) (207/256:ℝ)
    (11264969540965/13965179951616:ℝ) (42457363/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_206
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1239).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^4*thetaFirstMode x) ≤ (140524633803447/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (103/128:ℝ) (207/256:ℝ)
    (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_206 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_207 :
    (317083470700623/500000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (207/256:ℝ) (13/16:ℝ)
    (11540381488475/14237661636096:ℝ) (37591553/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_207
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1245).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x) ≤ (634244573270253/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (207/256:ℝ) (13/16:ℝ)
    (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_207 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_208 :
    (571840823251/1000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (13/16:ℝ) (209/256:ℝ)
    (3940384677495/4838037135872:ℝ) (16625559/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_208
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1251).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^4*thetaFirstMode x) ≤ (571912421552257/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (13/16:ℝ) (209/256:ℝ)
    (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_208 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_209 :
    (257544483157339/500000000000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (209/256:ℝ) (105/128:ℝ)
    (12107365048795/14794567604736:ℝ) (459111/1562500000000:ℝ) (25903420067651/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_209
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1257).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x) ≤ (515154928414229/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (209/256:ℝ) (105/128:ℝ)
    (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ) (25903420067651/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_209 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_210 :
    (92694063088703/200000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (105/128:ℝ) (211/256:ℝ)
    (12399093163805/15079068750336:ℝ) (6484869/25000000000000:ℝ) (232347092922457/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_210
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1263).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^4*thetaFirstMode x) ≤ (46353101970261/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (105/128:ℝ) (211/256:ℝ)
    (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_210 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_211 :
    (208286540355831/500000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (211/256:ℝ) (53/64:ℝ)
    (4232139252705/5122551183872:ℝ) (4575341/20000000000000:ℝ) (26025045292513/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_211
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1269).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x) ≤ (208314447073713/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (211/256:ℝ) (53/64:ℝ)
    (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ) (26025045292513/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_211 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_212 :
    (374013311907077/1000000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (53/64:ℝ) (213/256:ℝ)
    (12999418970125/15660360900096:ℝ) (4031077/20000000000000:ℝ) (46593623740507/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_212
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1275).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^4*thetaFirstMode x) ≤ (187032292662677/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (53/64:ℝ) (213/256:ℝ)
    (10740033/50000000000000:ℝ) (151323/800000000000:ℝ) (46593623740507/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_212 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_213 :
    (67086708210751/200000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (213/256:ℝ) (107/128:ℝ)
    (13308177699635/15957229871616:ℝ) (17739881/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_213
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1281).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x) ≤ (335480571611409/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (213/256:ℝ) (107/128:ℝ)
    (151323/800000000000:ℝ) (16640047/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_213 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_214 :
    (300501325664609/1000000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (107/128:ℝ) (215/256:ℝ)
    (4540925203815/5419433242112:ℝ) (15597997/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_214
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1287).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^4*thetaFirstMode x) ≤ (150272208444839/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (107/128:ℝ) (215/256:ℝ)
    (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_214 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_215 :
    (268907947819769/1000000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (215/256:ℝ) (27/32:ℝ)
    (13943295138955/16563609908736:ℝ) (3425169/25000000000000:ℝ) (33217875238267/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_215
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1293).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x) ≤ (268947402171223/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (215/256:ℝ) (27/32:ℝ)
    (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_215 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_216 :
    (240367162066513/1000000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (27/32:ℝ) (217/256:ℝ)
    (14269819487765/16873200047616:ℝ) (3005431/25000000000000:ℝ) (118452877704869/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_216
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1299).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^4*thetaFirstMode x) ≤ (60100806854763/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (27/32:ℝ) (217/256:ℝ)
    (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_216 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_217 :
    (53653456020007/250000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (217/256:ℝ) (109/128:ℝ)
    (4867477546425/5729036652032:ℝ) (2634387/25000000000000:ℝ) (1054879510589/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_217
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1305).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x) ≤ (107323375919387/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (217/256:ℝ) (109/128:ℝ)
    (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ) (1054879510589/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_217 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_218 :
    (191402702484541/1000000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (109/128:ℝ) (219/256:ℝ)
    (14941219354285/17505379631616:ℝ) (4613461/50000000000000:ℝ) (93842617334969/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_218
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1311).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^4*thetaFirstMode x) ≤ (19143275317913/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (109/128:ℝ) (219/256:ℝ)
    (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_218 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_219 :
    (21313419425387/125000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (219/256:ℝ) (55/64:ℝ)
    (15286265176595/17828049255936:ℝ) (8070773/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_219
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1317).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x) ≤ (170534724884121/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (219/256:ℝ) (55/64:ℝ)
    (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_219 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_220 :
    (151718825199329/1000000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (55/64:ℝ) (221/256:ℝ)
    (5212552145535/6051719731712:ℝ) (3525987/50000000000000:ℝ) (37014350035403/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_220
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1323).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^4*thetaFirstMode x) ≤ (151743750429831/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (55/64:ℝ) (221/256:ℝ)
    (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ) (37014350035403/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_220 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_221 :
    (134844697462487/1000000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (221/256:ℝ) (111/128:ℝ)
    (15995480254915/18486749999616:ℝ) (6155169/100000000000000:ℝ) (410275687759/6250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_221
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1329).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x) ≤ (134867368167227/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (221/256:ℝ) (111/128:ℝ)
    (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ) (410275687759/6250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_221 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_222 :
    (29926986879161/250000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (111/128:ℝ) (223/256:ℝ)
    (16359824545925/18822862404096:ℝ) (5366601/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_222
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1335).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^4*thetaFirstMode x) ≤ (29932134046193/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (111/128:ℝ) (223/256:ℝ)
    (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_222 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_223 :
    (106145951875619/1000000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (223/256:ℝ) (7/8:ℝ)
    (5576926007145/6387845775872:ℝ) (116849/2500000000000:ℝ) (6430874207139/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_223
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1341).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x) ≤ (106164626968417/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (223/256:ℝ) (7/8:ℝ)
    (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ) (6430874207139/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_223 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
