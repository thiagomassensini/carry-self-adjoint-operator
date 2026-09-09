import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes00
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes01
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes02
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes03
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes04
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes05
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes06
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes07
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes08
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes09
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes10
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes11
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes12
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes13
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes14
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes15
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes16
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes17
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes18
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes19
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes20
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes21
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes22
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes23
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes24
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes25
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes26
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes27
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes28
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes29
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes30
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes31
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes32
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes33
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes34
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes35
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes36
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes37
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes38
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes39
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes40
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes41
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes42
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes43
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes44
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes45
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes46
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes47
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes48
import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaFirstMode_refined_cell_lower_2_192 :
    (5882391018719/1258291200000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/4:ℝ) (193/256:ℝ) (85600515/113837056:ℝ) (52913951/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1154).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x) ≤ (94246993014581/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/4:ℝ) (193/256:ℝ) (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_193 :
    (888393232057/209715200000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (193/256:ℝ) (97/128:ℝ) (86941485/115022848:ℝ) (23726973/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1160).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x) ≤ (5693623226739/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (193/256:ℝ) (97/128:ℝ) (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_194 :
    (1930270930231/503316480000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (97/128:ℝ) (195/256:ℝ) (88296387/116214784:ℝ) (17008141/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1166).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x) ≤ (19329998467697/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (97/128:ℝ) (195/256:ℝ) (179715241/100000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_195 :
    (5819628571863/1677721600000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (195/256:ℝ) (49/64:ℝ) (89665293/117412864:ℝ) (152265249/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1172).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x) ≤ (69935915448761/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (195/256:ℝ) (49/64:ℝ) (257537/160000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_196 :
    (7888210455011/2516582400000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (49/64:ℝ) (197/256:ℝ) (91048275/118617088:ℝ) (68097503/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1178).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x) ≤ (6319789209601/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (49/64:ℝ) (197/256:ℝ) (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_197 :
    (14242669069531/5033164800000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (197/256:ℝ) (99/128:ℝ) (92445405/119827456:ℝ) (121712449/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1184).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x) ≤ (2282212160623/805306368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (197/256:ℝ) (99/128:ℝ) (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_198 :
    (12845837086523/5033164800000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (99/128:ℝ) (199/256:ℝ) (93856755/121043968:ℝ) (108672389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1190).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x) ≤ (51460944975991/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (99/128:ℝ) (199/256:ℝ) (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_199 :
    (2893734935633/1258291200000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (199/256:ℝ) (25/32:ℝ) (95282397/122266624:ℝ) (24235433/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1196).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x) ≤ (15456946569211/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (199/256:ℝ) (25/32:ℝ) (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_200 :
    (1736625817563/838860800000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/32:ℝ) (201/256:ℝ) (96722403/123495424:ℝ) (43199289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1202).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x) ≤ (13914689624163/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/32:ℝ) (201/256:ℝ) (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_201 :
    (9370781699923/5033164800000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (201/256:ℝ) (101/128:ℝ) (98176845/124730368:ℝ) (76931389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1208).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x) ≤ (12514199457611/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (201/256:ℝ) (101/128:ℝ) (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_202 :
    (8419199048819/5033164800000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (101/128:ℝ) (203/256:ℝ) (99645795/125971456:ℝ) (68438201/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1214).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x) ≤ (4216389357049/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (101/128:ℝ) (203/256:ℝ) (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_203 :
    (755682609593/503316480000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (203/256:ℝ) (51/64:ℝ) (101129325/127218688:ℝ) (6082589/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1220).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x) ≤ (30276867823391/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (203/256:ℝ) (51/64:ℝ) (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_204 :
    (423505273373/314572800000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (51/64:ℝ) (205/256:ℝ) (102627507/128472064:ℝ) (3375593/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1226).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x) ≤ (27149516977991/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (51/64:ℝ) (205/256:ℝ) (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_205 :
    (1011660194587/838860800000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (205/256:ℝ) (103/128:ℝ) (104140413/129731584:ℝ) (23955771/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1232).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x) ≤ (4864197361031/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (205/256:ℝ) (103/128:ℝ) (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_206 :
    (2715987306593/2516582400000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (103/128:ℝ) (207/256:ℝ) (105668115/130997248:ℝ) (21230759/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1238).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x) ≤ (21765325853617/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (103/128:ℝ) (207/256:ℝ) (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_207 :
    (4856139943067/5033164800000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (207/256:ℝ) (13/16:ℝ) (107210685/132269056:ℝ) (37595243/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1244).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x) ≤ (4864643341573/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (207/256:ℝ) (13/16:ℝ) (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_208 :
    (542117255183/629145600000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/16:ℝ) (209/256:ℝ) (108768195/133547008:ℝ) (4156799/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1250).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^2*thetaFirstMode x) ≤ (17378631856657/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/16:ℝ) (209/256:ℝ) (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_209 :
    (1934642398013/2516582400000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (209/256:ℝ) (105/128:ℝ) (110340717/134831104:ℝ) (14693003/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1256).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x) ≤ (3876286218131/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (209/256:ℝ) (105/128:ℝ) (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_210 :
    (1724251058413/2516582400000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (105/128:ℝ) (211/256:ℝ) (111928323/136121344:ℝ) (12971023/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1262).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^2*thetaFirstMode x) ≤ (3454845294509/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (105/128:ℝ) (211/256:ℝ) (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_211 :
    (3070290344863/5033164800000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (211/256:ℝ) (53/64:ℝ) (113531085/137417728:ℝ) (22878979/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1268).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x) ≤ (1538015595733/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (211/256:ℝ) (53/64:ℝ) (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_212 :
    (546140428651/1006632960000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (53/64:ℝ) (213/256:ℝ) (115149075/138720256:ℝ) (4031479/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1274).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^2*thetaFirstMode x) ≤ (3647856666661/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (53/64:ℝ) (213/256:ℝ) (10740033/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_213 :
    (303264779129/629145600000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (213/256:ℝ) (107/128:ℝ) (116782365/140028928:ℝ) (2217707/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1280).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x) ≤ (810268584951/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (213/256:ℝ) (107/128:ℝ) (151323/800000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_214 :
    (358870523737/838860800000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (107/128:ℝ) (215/256:ℝ) (118431027/141343744:ℝ) (7799781/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1286).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^2*thetaFirstMode x) ≤ (719150718239/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (107/128:ℝ) (215/256:ℝ) (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_215 :
    (79541005999/209715200000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (215/256:ℝ) (27/32:ℝ) (120095133/142664704:ℝ) (1712757/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1292).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x) ≤ (3825590592919/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (215/256:ℝ) (27/32:ℝ) (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_216 :
    (1690629613363/5033164800000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/32:ℝ) (217/256:ℝ) (121774755/143991808:ℝ) (12022939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1298).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^2*thetaFirstMode x) ≤ (67762417637/201326592000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/32:ℝ) (217/256:ℝ) (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_217 :
    (62317910171/209715200000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (217/256:ℝ) (109/128:ℝ) (123469965/145325056:ℝ) (1317327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1304).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x) ≤ (2997430015837/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (217/256:ℝ) (109/128:ℝ) (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_218 :
    (1321678847447/5033164800000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (109/128:ℝ) (219/256:ℝ) (125180835/146664448:ℝ) (9227861/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1310).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^2*thetaFirstMode x) ≤ (662225054279/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (109/128:ℝ) (219/256:ℝ) (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_219 :
    (97223046453/419430400000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (219/256:ℝ) (55/64:ℝ) (126907437/148009984:ℝ) (2017899/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1316).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x) ≤ (2338326380603/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (219/256:ℝ) (55/64:ℝ) (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_220 :
    (128589161407/629145600000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (55/64:ℝ) (221/256:ℝ) (128649843/149361664:ℝ) (881587/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1322).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^2*thetaFirstMode x) ≤ (4123768051813/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (55/64:ℝ) (221/256:ℝ) (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_221 :
    (906053881787/5033164800000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (221/256:ℝ) (111/128:ℝ) (130408125/150719488:ℝ) (6155801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1328).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x) ≤ (605366199101/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (221/256:ℝ) (111/128:ℝ) (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_222 :
    (398562172463/2516582400000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (111/128:ℝ) (223/256:ℝ) (132182355/152083456:ℝ) (2683577/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1334).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^2*thetaFirstMode x) ≤ (42608467121/268435456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (111/128:ℝ) (223/256:ℝ) (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_223 :
    (58374846209/419430400000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (223/256:ℝ) (7/8:ℝ) (133972605/153453568:ℝ) (1168611/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1340).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x) ≤ (936122615991/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (223/256:ℝ) (7/8:ℝ) (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
