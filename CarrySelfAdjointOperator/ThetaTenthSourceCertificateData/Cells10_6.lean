import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature6

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^10*thetaFirstMode x) ≤ (477971462156149/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/4:ℝ) (193/256:ℝ)
    (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_192 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^10*thetaFirstMode x) ≤ (9028995200463/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (193/256:ℝ) (97/128:ℝ)
    (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ) (323729221238183/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_193 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^10*thetaFirstMode x) ≤ (425915403546939/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (97/128:ℝ) (195/256:ℝ)
    (179715241/100000000000000:ℝ) (257537/160000000000:ℝ) (589561754626943/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_194 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^10*thetaFirstMode x) ≤ (401367273257937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (195/256:ℝ) (49/64:ℝ)
    (257537/160000000000:ℝ) (72018211/50000000000000:ℝ) (536365970577363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_195 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^10*thetaFirstMode x) ≤ (75560259555621/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (49/64:ℝ) (197/256:ℝ)
    (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ) (975067464150909/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_196 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^10*thetaFirstMode x) ≤ (35521063207107/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (197/256:ℝ) (99/128:ℝ)
    (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_197 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^10*thetaFirstMode x) ≤ (333585833517559/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (99/128:ℝ) (199/256:ℝ)
    (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ) (100427867549897/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_198 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^10*thetaFirstMode x) ≤ (2503320303961/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (199/256:ℝ) (25/32:ℝ)
    (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_199 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^10*thetaFirstMode x) ≤ (293184150086517/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/32:ℝ) (201/256:ℝ)
    (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_200 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^10*thetaFirstMode x) ≤ (274377024791917/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (201/256:ℝ) (101/128:ℝ)
    (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_201 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^10*thetaFirstMode x) ≤ (256475650453243/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (101/128:ℝ) (203/256:ℝ)
    (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_202 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^10*thetaFirstMode x) ≤ (119730167096441/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (203/256:ℝ) (51/64:ℝ)
    (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ) (12180020474541/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_203 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^10*thetaFirstMode x) ≤ (13956867434157/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (51/64:ℝ) (205/256:ℝ)
    (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ) (54947028858241/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_204 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^10*thetaFirstMode x) ≤ (26000220708717/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (205/256:ℝ) (103/128:ℝ)
    (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ) (396227085824353/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_205 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^10*thetaFirstMode x) ≤ (193512320046611/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (103/128:ℝ) (207/256:ℝ)
    (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_206 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^10*thetaFirstMode x) ≤ (89908442227093/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (207/256:ℝ) (13/16:ℝ)
    (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_207 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^10*thetaFirstMode x) ≤ (83444992027969/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/16:ℝ) (209/256:ℝ)
    (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_208 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^10*thetaFirstMode x) ≤ (154705479769687/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (209/256:ℝ) (105/128:ℝ)
    (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ) (25903420067651/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_209 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^10*thetaFirstMode x) ≤ (35809179726547/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (105/128:ℝ) (211/256:ℝ)
    (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_210 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^10*thetaFirstMode x) ≤ (132456679387321/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (211/256:ℝ) (53/64:ℝ)
    (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ) (26025045292513/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_211 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^10*thetaFirstMode x) ≤ (122338100565649/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/64:ℝ) (213/256:ℝ)
    (10740033/50000000000000:ℝ) (151323/800000000000:ℝ) (46593623740507/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_212 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^10*thetaFirstMode x) ≤ (112853613919379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (213/256:ℝ) (107/128:ℝ)
    (151323/800000000000:ℝ) (16640047/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_213 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^10*thetaFirstMode x) ≤ (10397586717043/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (107/128:ℝ) (215/256:ℝ)
    (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_214 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^10*thetaFirstMode x) ≤ (47838813417451/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (215/256:ℝ) (27/32:ℝ)
    (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_215 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^10*thetaFirstMode x) ≤ (43965942001129/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/32:ℝ) (217/256:ℝ)
    (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_216 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^10*thetaFirstMode x) ≤ (10088994103823/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (217/256:ℝ) (109/128:ℝ)
    (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ) (1054879510589/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_217 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^10*thetaFirstMode x) ≤ (14798310700243/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (109/128:ℝ) (219/256:ℝ)
    (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_218 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^10*thetaFirstMode x) ≤ (67744885061547/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (219/256:ℝ) (55/64:ℝ)
    (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_219 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^10*thetaFirstMode x) ≤ (3871668961367/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/64:ℝ) (221/256:ℝ)
    (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ) (37014350035403/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_220 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^10*thetaFirstMode x) ≤ (11314474001283/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (221/256:ℝ) (111/128:ℝ)
    (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ) (410275687759/6250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_221 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^10*thetaFirstMode x) ≤ (25798957672417/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (111/128:ℝ) (223/256:ℝ)
    (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_222 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^10*thetaFirstMode x) ≤ (9400017723099/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (223/256:ℝ) (7/8:ℝ)
    (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ) (6430874207139/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_223 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
