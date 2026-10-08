import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature6

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_192 :
    (422645945076337/500000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/4:ℝ) (193/256:ℝ)
    (6534077305948613955765/8689317914228980285952:ℝ) (10579809/5000000000000:ℝ) (14208294001147/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_192
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1157).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^8*thetaFirstMode x) ≤ (845365689112887/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/4:ℝ) (193/256:ℝ)
    (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_192 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_193 :
    (395078249236749/500000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (193/256:ℝ) (97/128:ℝ)
    (34229931486855451316343/45285304621504058652160:ℝ) (47440541/25000000000000:ℝ) (323729221238183/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_193
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1163).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^8*thetaFirstMode x) ≤ (395113523034381/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (193/256:ℝ) (97/128:ℝ)
    (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ) (323729221238183/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_193 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_194 :
    (737817865183603/1000000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (97/128:ℝ) (195/256:ℝ)
    (35855303234927171773041/47191752594083278773760:ℝ) (17003323/10000000000000:ℝ) (589561754626943/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_194
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1169).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^8*thetaFirstMode x) ≤ (184471308870787/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (97/128:ℝ) (195/256:ℝ)
    (179715241/100000000000000:ℝ) (257537/160000000000:ℝ) (589561754626943/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_194 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_195 :
    (344098555751759/500000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (195/256:ℝ) (49/64:ℝ)
    (37548920246270157404559/49168060985435061199360:ℝ) (152221993/100000000000000:ℝ) (536365970577363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_195
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1175).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^8*thetaFirstMode x) ≤ (172065345163779/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (195/256:ℝ) (49/64:ℝ)
    (257537/160000000000:ℝ) (72018211/50000000000000:ℝ) (536365970577363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_195 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_196 :
    (320606346186441/500000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (49/64:ℝ) (197/256:ℝ)
    (39313276758463040392257/51216412690723244700160:ℝ) (68078103/50000000000000:ℝ) (975067464150909/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_196
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1181).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^8*thetaFirstMode x) ≤ (641273928185857/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (49/64:ℝ) (197/256:ℝ)
    (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ) (975067464150909/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_196 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_197 :
    (596780833383633/1000000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (197/256:ℝ) (99/128:ℝ)
    (8230188948417592711155/10667809430360898647552:ℝ) (60838837/50000000000000:ℝ) (885496145229559/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_197
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1187).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^8*thetaFirstMode x) ≤ (149209780774843/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (197/256:ℝ) (99/128:ℝ)
    (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_197 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_198 :
    (2167250136927/3906250000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (99/128:ℝ) (199/256:ℝ)
    (43064575909141158188793/55538261523062839068160:ℝ) (108641251/100000000000000:ℝ) (100427867549897/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_198
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1193).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^8*thetaFirstMode x) ≤ (554871453750081/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (99/128:ℝ) (199/256:ℝ)
    (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ) (100427867549897/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_198 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_199 :
    (257615717359307/500000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (199/256:ℝ) (25/32:ℝ)
    (45056903762744623817991/57816411855179361794560:ℝ) (96913873/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_199
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1199).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^8*thetaFirstMode x) ≤ (103056814335751/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (199/256:ℝ) (25/32:ℝ)
    (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_199 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_200 :
    (238969637163141/500000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (25/32:ℝ) (201/256:ℝ)
    (47130745688792656218009/60175914297020011010560:ℝ) (21593419/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_200
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1205).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^8*thetaFirstMode x) ≤ (47798921073149/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (25/32:ℝ) (201/256:ℝ)
    (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_200 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_201 :
    (442851245980161/1000000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (201/256:ℝ) (101/128:ℝ)
    (49289005090173420207207/62619246315825509148160:ℝ) (1538183/2000000000000:ℝ) (298393710712757/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_201
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1211).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^8*thetaFirstMode x) ≤ (442898568632019/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (201/256:ℝ) (101/128:ℝ)
    (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_201 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_202 :
    (409878873540707/1000000000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (101/128:ℝ) (203/256:ℝ)
    (10306934712842449320045/13029789587177640023552:ℝ) (34209179/50000000000000:ℝ) (539471835378099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_202
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1217).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^8*thetaFirstMode x) ≤ (409923668500649/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (101/128:ℝ) (203/256:ℝ)
    (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_202 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_203 :
    (378933846030827/1000000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (203/256:ℝ) (51/64:ℝ)
    (53870833123989848203743/67767622995901638300160:ℝ) (60808201/100000000000000:ℝ) (12180020474541/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_203
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1223).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^8*thetaFirstMode x) ≤ (378976203578909/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (203/256:ℝ) (51/64:ℝ)
    (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ) (12180020474541/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_203 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_204 :
    (5467630370347/15625000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (51/64:ℝ) (205/256:ℝ)
    (56300658464195197911441/70477940425169641423360:ℝ) (26996867/50000000000000:ℝ) (54947028858241/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_204
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1229).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^8*thetaFirstMode x) ≤ (349968348649961/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (51/64:ℝ) (205/256:ℝ)
    (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ) (54947028858241/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_204 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_205 :
    (161387658783253/500000000000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (205/256:ℝ) (103/128:ℝ)
    (58827419272179392782959/73282635538862459829760:ℝ) (11974381/25000000000000:ℝ) (396227085824353/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_205
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1235).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^8*thetaFirstMode x) ≤ (80703265317367/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (205/256:ℝ) (103/128:ℝ)
    (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ) (396227085824353/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_205 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_206 :
    (148694383797777/500000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (103/128:ℝ) (207/256:ℝ)
    (61454482584883441479657/76184511352508643612160:ℝ) (8489811/20000000000000:ℝ) (22300504829651/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_206
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1241).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^8*thetaFirstMode x) ≤ (297424341384379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (103/128:ℝ) (207/256:ℝ)
    (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_206 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_207 :
    (136841999882023/500000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (207/256:ℝ) (13/16:ℝ)
    (12837063038463911715435/15837287983182423613952:ℝ) (18792087/50000000000000:ℝ) (80249536094603/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_207
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1247).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^8*thetaFirstMode x) ≤ (273717483367141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (207/256:ℝ) (13/16:ℝ)
    (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_207 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_208 :
    (251577826671971/1000000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (13/16:ℝ) (209/256:ℝ)
    (67023486088292228081193/82291363666684906908160:ℝ) (33244571/100000000000000:ℝ) (28849907635213/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_208
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1253).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^8*thetaFirstMode x) ≤ (251609304098559/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/16:ℝ) (209/256:ℝ)
    (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_208 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_209 :
    (115494387433763/500000000000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (209/256:ℝ) (105/128:ℝ)
    (69972668969052009938391/85502296803586871580160:ℝ) (293773/1000000000000:ℝ) (25903420067651/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_209
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1259).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^8*thetaFirstMode x) ≤ (231018337458987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (209/256:ℝ) (105/128:ℝ)
    (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ) (25903420067651/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_209 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_210 :
    (105918642274671/500000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (105/128:ℝ) (211/256:ℝ)
    (73036644780581807459409/88822326679864764136960:ℝ) (50653/195312500000:ℝ) (232347092922457/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_210
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1265).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^8*thetaFirstMode x) ≤ (847460053327/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (105/128:ℝ) (211/256:ℝ)
    (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_210 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_211 :
    (19404582984579/100000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (211/256:ℝ) (53/64:ℝ)
    (76219304315222090354607/92254615216783819932160:ℝ) (22872157/100000000000000:ℝ) (26025045292513/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_211
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1271).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^8*thetaFirstMode x) ≤ (97035907937641/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (211/256:ℝ) (53/64:ℝ)
    (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ) (26025045292513/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_211 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_212 :
    (35507818641889/200000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (53/64:ℝ) (213/256:ℝ)
    (15904930171669675505325/19160480067509209098752:ℝ) (10075683/50000000000000:ℝ) (46593623740507/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_212
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1277).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^8*thetaFirstMode x) ≤ (88781706115217/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (53/64:ℝ) (213/256:ℝ)
    (10740033/50000000000000:ℝ) (151323/800000000000:ℝ) (46593623740507/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_212 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_213 :
    (162244041112099/1000000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (213/256:ℝ) (107/128:ℝ)
    (82956802885821125866143/99468997421790285852160:ℝ) (4434083/25000000000000:ℝ) (41666673119801/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_213
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1283).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^8*thetaFirstMode x) ≤ (162266772389829/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (213/256:ℝ) (107/128:ℝ)
    (151323/800000000000:ℝ) (16640047/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_213 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_214 :
    (37022512094983/250000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (107/128:ℝ) (215/256:ℝ)
    (86519996812935046058841/103257800780870084584960:ℝ) (7797433/50000000000000:ℝ) (74444924862353/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_214
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1289).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^8*thetaFirstMode x) ≤ (148111271690619/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (107/128:ℝ) (215/256:ℝ)
    (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_214 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_215 :
    (27001792081299/200000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (215/256:ℝ) (27/32:ℝ)
    (90218589795601773832359/107172285154106278812160:ℝ) (13697917/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_215
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1295).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^8*thetaFirstMode x) ≤ (135028755615297/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (215/256:ℝ) (27/32:ℝ)
    (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_215 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_216 :
    (122935169860301/1000000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (27/32:ℝ) (217/256:ℝ)
    (94057062584506765152057/111216007226212200348160:ℝ) (2403859/20000000000000:ℝ) (118452877704869/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_216
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1301).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^8*thetaFirstMode x) ≤ (122953604003417/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (27/32:ℝ) (217/256:ℝ)
    (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_216 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_217 :
    (5590281932743/50000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (217/256:ℝ) (109/128:ℝ)
    (19608004486597651322715/23078521433218056637952:ℝ) (2633853/25000000000000:ℝ) (1054879510589/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_217
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1307).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^8*thetaFirstMode x) ≤ (55911390037221/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (217/256:ℝ) (109/128:ℝ)
    (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ) (1054879510589/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_217 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_218 :
    (50779963444959/500000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (109/128:ℝ) (219/256:ℝ)
    (102172206059393137678593/119705810187199806492160:ℝ) (4612523/50000000000000:ℝ) (93842617334969/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_218
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1313).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^8*thetaFirstMode x) ≤ (25393963463151/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (109/128:ℝ) (219/256:ℝ)
    (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_218 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_219 :
    (18428043574119/200000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (219/256:ℝ) (55/64:ℝ)
    (106458482664671619457791/124159428129696431157760:ℝ) (64553/800000000000:ℝ) (16678757434983/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_219
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1319).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^8*thetaFirstMode x) ≤ (92155008925367/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (219/256:ℝ) (55/64:ℝ)
    (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_219 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_220 :
    (83491346952961/1000000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (55/64:ℝ) (221/256:ℝ)
    (110903857005979655461809/128757361064545117135360:ℝ) (705053/10000000000000:ℝ) (37014350035403/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_220
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1325).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^8*thetaFirstMode x) ≤ (16701010822611/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (55/64:ℝ) (221/256:ℝ)
    (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ) (37014350035403/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_220 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_221 :
    (37780347429411/500000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (221/256:ℝ) (111/128:ℝ)
    (115513472527065173117007/133503598919808937500160:ℝ) (384619/6250000000000:ℝ) (410275687759/6250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_221
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1331).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^8*thetaFirstMode x) ≤ (75573394108203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (221/256:ℝ) (111/128:ℝ)
    (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ) (410275687759/6250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_221 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_222 :
    (68298285362549/1000000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (111/128:ℝ) (223/256:ℝ)
    (24058522909244262175605/27680444625863446871552:ℝ) (1073099/20000000000000:ℝ) (11629122491573/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_222
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1337).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^8*thetaFirstMode x) ≤ (68310018919359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (111/128:ℝ) (223/256:ℝ)
    (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_222 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_223 :
    (30828316890913/500000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (223/256:ℝ) (7/8:ℝ)
    (125246713502597024463543/143457408303917490588160:ℝ) (4672993/100000000000000:ℝ) (6430874207139/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_223
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1343).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^8*thetaFirstMode x) ≤ (481777149743/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (223/256:ℝ) (7/8:ℝ)
    (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ) (6430874207139/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_223 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
