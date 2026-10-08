import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature6

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_192 :
    (1495041484950647/1000000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/4:ℝ) (193/256:ℝ)
    (548559415042533895/729502937539807232:ℝ) (52904013/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_192
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1156).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^6*thetaFirstMode x) ≤ (93448253680551/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/4:ℝ) (193/256:ℝ)
    (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ) (14208294001147/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_192 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_193 :
    (1383118628420623/1000000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (193/256:ℝ) (97/128:ℝ)
    (568820330690682105/752537778572097536:ℝ) (37956007/20000000000000:ℝ) (323729221238183/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_193
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1162).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^6*thetaFirstMode x) ≤ (5532968648983/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (193/256:ℝ) (97/128:ℝ)
    (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ) (323729221238183/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_193 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_194 :
    (1278257801738461/1000000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (97/128:ℝ) (195/256:ℝ)
    (589719320504220263/776175582409545728:ℝ) (21256161/12500000000000:ℝ) (589561754626943/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_194
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1168).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^6*thetaFirstMode x) ≤ (639187280442193/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (97/128:ℝ) (195/256:ℝ)
    (179715241/100000000000000:ℝ) (257537/160000000000:ℝ) (589561754626943/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_194 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_195 :
    (118012514073879/100000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (195/256:ℝ) (49/64:ℝ)
    (611273043037863577/800428910102816768:ℝ) (15223641/10000000000000:ℝ) (536365970577363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_195
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1174).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^6*thetaFirstMode x) ≤ (118023538507861/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (195/256:ℝ) (49/64:ℝ)
    (257537/160000000000:ℝ) (72018211/50000000000000:ℝ) (536365970577363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_195 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_196 :
    (136049200050487/125000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (49/64:ℝ) (197/256:ℝ)
    (633498502977313575/825310517945133056:ℝ) (136169137/100000000000000:ℝ) (975067464150909/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_196
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1180).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^6*thetaFirstMode x) ≤ (544248792264791/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (49/64:ℝ) (197/256:ℝ)
    (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ) (975067464150909/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_196 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_197 :
    (501371789363287/500000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (197/256:ℝ) (99/128:ℝ)
    (656413056505416665/850833359485048832:ℝ) (7605579/6250000000000:ℝ) (885496145229559/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_197
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1186).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^6*thetaFirstMode x) ≤ (250710388365547/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (197/256:ℝ) (99/128:ℝ)
    (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ) (885496145229559/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_197 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_198 :
    (922863447349101/1000000000000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (99/128:ℝ) (199/256:ℝ)
    (680034416723500615/877010587549546496:ℝ) (108651629/100000000000000:ℝ) (100427867549897/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_198
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1192).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^6*thetaFirstMode x) ≤ (92295566260739/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (99/128:ℝ) (199/256:ℝ)
    (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ) (100427867549897/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_198 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_199 :
    (42422500165979/50000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (199/256:ℝ) (25/32:ℝ)
    (704380659128171193/903855556277454848:ℝ) (48461579/50000000000000:ℝ) (36414495119801/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_199
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1198).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^6*thetaFirstMode x) ≤ (212134178089993/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (199/256:ℝ) (25/32:ℝ)
    (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ) (36414495119801/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_199 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_200 :
    (779208904542553/1000000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (25/32:ℝ) (201/256:ℝ)
    (729470227143851207/931381823163189248:ℝ) (3455279/4000000000000:ℝ) (659574402541617/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_200
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1204).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^6*thetaFirstMode x) ≤ (389645175851111/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (25/32:ℝ) (201/256:ℝ)
    (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ) (659574402541617/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_200 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_201 :
    (357427494750499/500000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (201/256:ℝ) (101/128:ℝ)
    (755321937711344185/959603151110813696:ℝ) (38458281/50000000000000:ℝ) (298393710712757/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_201
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1210).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^6*thetaFirstMode x) ≤ (357465702766453/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (201/256:ℝ) (101/128:ℝ)
    (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ) (298393710712757/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_201 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_202 :
    (20472266179687/31250000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (101/128:ℝ) (203/256:ℝ)
    (781954986932704935/988533510498424832:ℝ) (68424971/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_202
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1216).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^6*thetaFirstMode x) ≤ (655184143947231/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (101/128:ℝ) (203/256:ℝ)
    (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ) (539471835378099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_202 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_203 :
    (23988617835943/40000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (203/256:ℝ) (51/64:ℝ)
    (809388955772699225/1018187081252857856:ℝ) (60814097/100000000000000:ℝ) (12180020474541/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_203
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1222).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^6*thetaFirstMode x) ≤ (37486406413717/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (203/256:ℝ) (51/64:ℝ)
    (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ) (12180020474541/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_203 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_204 :
    (54840751471247/100000000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (51/64:ℝ) (205/256:ℝ)
    (837643815817134823/1048578254934714368:ℝ) (10799797/20000000000000:ℝ) (54947028858241/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_204
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1228).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^6*thetaFirstMode x) ≤ (274235115595057/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (51/64:ℝ) (205/256:ℝ)
    (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ) (54947028858241/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_204 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_205 :
    (500942409060771/1000000000000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (205/256:ℝ) (103/128:ℝ)
    (866739935088346137/1079721636833712128:ℝ) (11975549/25000000000000:ℝ) (396227085824353/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_205
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1234).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^6*thetaFirstMode x) ≤ (501001010397503/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (205/256:ℝ) (103/128:ℝ)
    (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ) (396227085824353/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_205 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_206 :
    (457083800105989/1000000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (103/128:ℝ) (207/256:ℝ)
    (896698083918114695/1111632048074356736:ℝ) (42453209/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_206
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1240).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^6*thetaFirstMode x) ≤ (91427698314179/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (103/128:ℝ) (207/256:ℝ)
    (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ) (22300504829651/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_206 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_207 :
    (104151332015613/250000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (207/256:ℝ) (13/16:ℝ)
    (927539440878307705/1144324527731935232:ℝ) (37587863/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_207
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1246).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^6*thetaFirstMode x) ≤ (416656315283807/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (207/256:ℝ) (13/16:ℝ)
    (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ) (80249536094603/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_207 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_208 :
    (189645304634283/500000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (13/16:ℝ) (209/256:ℝ)
    (959285598769516935/1177814334958831616:ℝ) (8311961/25000000000000:ℝ) (28849907635213/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_208
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1252).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^6*thetaFirstMode x) ≤ (379338086085153/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/16:ℝ) (209/256:ℝ)
    (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ) (28849907635213/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_208 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_209 :
    (344933134794767/1000000000000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (209/256:ℝ) (105/128:ℝ)
    (991958570667980153/1212116951121164288:ℝ) (14690101/50000000000000:ℝ) (25903420067651/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_209
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1258).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^6*thetaFirstMode x) ≤ (344977291570023/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (209/256:ℝ) (105/128:ℝ)
    (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ) (25903420067651/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_209 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_210 :
    (39167021367523/125000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (105/128:ℝ) (211/256:ℝ)
    (1025580796031067367/1247248081945745408:ℝ) (12968453/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_210
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1264).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^6*thetaFirstMode x) ≤ (2448259347451/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (105/128:ℝ) (211/256:ℝ)
    (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ) (232347092922457/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_210 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_211 :
    (5686252475271/20000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (211/256:ℝ) (53/64:ℝ)
    (1060175146861614105/1283223659677362176:ℝ) (22874431/100000000000000:ℝ) (26025045292513/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_211
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1270).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^6*thetaFirstMode x) ≤ (284350705695701/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (211/256:ℝ) (53/64:ℝ)
    (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ) (26025045292513/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_211 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_212 :
    (257684881986989/1000000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (53/64:ℝ) (213/256:ℝ)
    (1095764933931383975/1320059845246380032:ℝ) (629793/3125000000000:ℝ) (46593623740507/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_212
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1276).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^6*thetaFirstMode x) ≤ (12886009285993/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (53/64:ℝ) (213/256:ℝ)
    (10740033/50000000000000:ℝ) (151323/800000000000:ℝ) (46593623740507/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_212 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_213 :
    (116642287606747/500000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (213/256:ℝ) (107/128:ℝ)
    (1132373913063942745/1357773030446667776:ℝ) (8869053/50000000000000:ℝ) (41666673119801/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_213
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1282).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^6*thetaFirstMode x) ≤ (233317276864027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (213/256:ℝ) (107/128:ℝ)
    (151323/800000000000:ℝ) (16640047/100000000000000:ℝ) (41666673119801/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_213 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_214 :
    (210952438486291/1000000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (107/128:ℝ) (215/256:ℝ)
    (1170026291477226183/1396379840123844608:ℝ) (15596431/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_214
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1288).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^6*thetaFirstMode x) ≤ (26372835655127/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (107/128:ℝ) (215/256:ℝ)
    (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ) (74444924862353/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_214 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_215 :
    (190537988646547/1000000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (215/256:ℝ) (27/32:ℝ)
    (1208746734186083897/1435897134373849088:ℝ) (13699297/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_215
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1294).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^6*thetaFirstMode x) ≤ (190565926985457/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (215/256:ℝ) (27/32:ℝ)
    (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ) (33217875238267/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_215 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_216 :
    (21487411201269/125000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (27/32:ℝ) (217/256:ℝ)
    (1248560370465081415/1476342010751830016:ℝ) (12020509/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_216
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1300).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^6*thetaFirstMode x) ≤ (85962540013327/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (27/32:ℝ) (217/256:ℝ)
    (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ) (118452877704869/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_216 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_217 :
    (38725691547869/250000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (217/256:ℝ) (109/128:ℝ)
    (1289492800371842745/1517731806491359232:ℝ) (65853/625000000000:ℝ) (1054879510589/10000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_217
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1306).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^6*thetaFirstMode x) ≤ (19365815362437/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (217/256:ℝ) (109/128:ℝ)
    (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ) (1054879510589/10000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_217 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_218 :
    (34855692740861/250000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (109/128:ℝ) (219/256:ℝ)
    (1331570101331215655/1560084100733966336:ℝ) (36039/390625000000:ℝ) (93842617334969/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_218
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1312).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^6*thetaFirstMode x) ≤ (139444647365789/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (109/128:ℝ) (219/256:ℝ)
    (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ) (93842617334969/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_218 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_219 :
    (62670719712477/500000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (219/256:ℝ) (55/64:ℝ)
    (1374818834780541913/1603416716768995328:ℝ) (8069949/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_219
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1318).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^6*thetaFirstMode x) ≤ (62680779417537/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (219/256:ℝ) (55/64:ℝ)
    (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ) (16678757434983/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_219 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_220 :
    (56274155782399/500000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (55/64:ℝ) (221/256:ℝ)
    (1419266052876314727/1647747724283783168:ℝ) (1762813/25000000000000:ℝ) (37014350035403/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_220
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1324).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^6*thetaFirstMode x) ≤ (56283397359407/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (55/64:ℝ) (221/256:ℝ)
    (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ) (37014350035403/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_220 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_221 :
    (100940039802173/1000000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (221/256:ℝ) (111/128:ℝ)
    (1464939305262505625/1693095441624160256:ℝ) (6154537/100000000000000:ℝ) (410275687759/6250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_221
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1330).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^6*thetaFirstMode x) ≤ (50478499294183/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (221/256:ℝ) (111/128:ℝ)
    (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ) (410275687759/6250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_221 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_222 :
    (22605022458191/250000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (111/128:ℝ) (223/256:ℝ)
    (1511866645900843015/1739478438065272832:ℝ) (167689/3125000000000:ℝ) (11629122491573/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_222
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1336).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^6*thetaFirstMode x) ≤ (2826113500899/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (111/128:ℝ) (223/256:ℝ)
    (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ) (11629122491573/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_222 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_223 :
    (80898454361029/1000000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (223/256:ℝ) (7/8:ℝ)
    (1560076639963324665/1786915536092727296:ℝ) (4673477/100000000000000:ℝ) (6430874207139/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_223
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1342).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^6*thetaFirstMode x) ≤ (40456337078297/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (223/256:ℝ) (7/8:ℝ)
    (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ) (6430874207139/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_223 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
