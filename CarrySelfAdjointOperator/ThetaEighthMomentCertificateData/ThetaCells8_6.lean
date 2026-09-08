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

theorem thetaFirstMode_refined_cell_lower_8_192 :
    (59851122313034501100349963/70835497243044678205440000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/4:ℝ) (193/256:ℝ) (6534077305948613955765/8689317914228980285952:ℝ) (10579809/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1157).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^8*thetaFirstMode x) ≤ (7191960062005007907847807897/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/4:ℝ) (193/256:ℝ) (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_193 :
    (839202871325762803185234851/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (193/256:ℝ) (97/128:ℝ) (34229931486855451316343/45285304621504058652160:ℝ) (47440541/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1163).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^8*thetaFirstMode x) ≤ (3734977985937443032681619133/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (193/256:ℝ) (97/128:ℝ) (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_194 :
    (313443989177064796050502033/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (97/128:ℝ) (195/256:ℝ) (35855303234927171773041/47191752594083278773760:ℝ) (17003323/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1169).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^8*thetaFirstMode x) ≤ (15694359489822392775685868347/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (97/128:ℝ) (195/256:ℝ) (179715241/100000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_195 :
    (2923617279354870698376386533/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (195/256:ℝ) (49/64:ℝ) (37548920246270157404559/49168060985435061199360:ℝ) (152221993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1175).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^8*thetaFirstMode x) ≤ (29278199941864379115804798623/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (195/256:ℝ) (49/64:ℝ) (257537/160000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_196 :
    (453999507610620338176002161/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (49/64:ℝ) (197/256:ℝ) (39313276758463040392257/51216412690723244700160:ℝ) (68078103/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1181).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^8*thetaFirstMode x) ≤ (13639889570304427912779790817/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (49/64:ℝ) (197/256:ℝ) (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_197 :
    (1267611560704667117171751127/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (197/256:ℝ) (99/128:ℝ) (8230188948417592711155/10667809430360898647552:ℝ) (60838837/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1187).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^8*thetaFirstMode x) ≤ (1015595888962753025292840463/1700051933833072276930560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (197/256:ℝ) (99/128:ℝ) (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_198 :
    (2356932113371371948428350261/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (99/128:ℝ) (199/256:ℝ) (43064575909141158188793/55538261523062839068160:ℝ) (108641251/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1193).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^8*thetaFirstMode x) ≤ (23604920022536082992824830799/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (99/128:ℝ) (199/256:ℝ) (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_199 :
    (2188754842128338695773062473/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (199/256:ℝ) (25/32:ℝ) (45056903762744623817991/57816411855179361794560:ℝ) (96913873/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1199).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^8*thetaFirstMode x) ≤ (7307052133364079357238128739/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (199/256:ℝ) (25/32:ℝ) (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_200 :
    (507579582470173261381107619/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (25/32:ℝ) (201/256:ℝ) (47130745688792656218009/60175914297020011010560:ℝ) (21593419/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1205).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^8*thetaFirstMode x) ≤ (1355658404979246454652145599/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (25/32:ℝ) (201/256:ℝ) (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_201 :
    (37624945373365402007048513/85002596691653613846528000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (201/256:ℝ) (101/128:ℝ) (49289005090173420207207/62619246315825509148160:ℝ) (1538183/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1211).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^8*thetaFirstMode x) ≤ (1256155056234283519633051463/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (201/256:ℝ) (101/128:ℝ) (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_202 :
    (870582820937687485084481609/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (101/128:ℝ) (203/256:ℝ) (10306934712842449320045/13029789587177640023552:ℝ) (34209179/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1217).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^8*thetaFirstMode x) ≤ (1743974495486750129244337337/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (101/128:ℝ) (203/256:ℝ) (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_203 :
    (1609698140791800389838057661/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (203/256:ℝ) (51/64:ℝ) (53870833123989848203743/67767622995901638300160:ℝ) (60808201/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1223).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^8*thetaFirstMode x) ≤ (16123379768544571320287332901/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (203/256:ℝ) (51/64:ℝ) (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_204 :
    (743235775036026664821929927/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (51/64:ℝ) (205/256:ℝ) (56300658464195197911441/70477940425169641423360:ℝ) (26996867/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1229).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^8*thetaFirstMode x) ≤ (14889496998911486221894776221/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (51/64:ℝ) (205/256:ℝ) (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_205 :
    (342778983838468515858883351/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (205/256:ℝ) (103/128:ℝ) (58827419272179392782959/73282635538862459829760:ℝ) (11974381/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1235).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^8*thetaFirstMode x) ≤ (13734396526114532307788941933/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (205/256:ℝ) (103/128:ℝ) (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_206 :
    (84217721681009473975728607/283341988972178712821760000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (103/128:ℝ) (207/256:ℝ) (61454482584883441479657/76184511352508643612160:ℝ) (8489811/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1241).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^8*thetaFirstMode x) ≤ (12654422438818400666761838143/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (103/128:ℝ) (207/256:ℝ) (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_207 :
    (193760217203137136343906509/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (207/256:ℝ) (13/16:ℝ) (12837063038463911715435/15837287983182423613952:ℝ) (18792087/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1247).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^8*thetaFirstMode x) ≤ (1164597375438455312799915007/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (207/256:ℝ) (13/16:ℝ) (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_208 :
    (1068648860196846375912779531/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (13/16:ℝ) (209/256:ℝ) (67023486088292228081193/82291363666684906908160:ℝ) (33244571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1253).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^8*thetaFirstMode x) ≤ (10705514120439557769457733293/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (13/16:ℝ) (209/256:ℝ) (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_209 :
    (9811822749562549228405603/42501298345826806923264000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (209/256:ℝ) (105/128:ℝ) (69972668969052009938391/85502296803586871580160:ℝ) (293773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1259).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^8*thetaFirstMode x) ≤ (614348755616706078444698297/2656331146614175432704000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (209/256:ℝ) (105/128:ℝ) (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_210 :
    (1757467700513746053839623/8301034833169298227200000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (105/128:ℝ) (211/256:ℝ) (73036644780581807459409/88822326679864764136960:ℝ) (50653/195312500000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1265).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^8*thetaFirstMode x) ≤ (1126848592027239713334950911/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (105/128:ℝ) (211/256:ℝ) (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_211 :
    (824242985630026783026598777/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (211/256:ℝ) (53/64:ℝ) (76219304315222090354607/92254615216783819932160:ℝ) (22872157/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1271).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^8*thetaFirstMode x) ≤ (2064461097193786010183702657/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (211/256:ℝ) (53/64:ℝ) (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_212 :
    (125686799015651946913893781/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (53/64:ℝ) (213/256:ℝ) (15904930171669675505325/19160480067509209098752:ℝ) (10075683/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1277).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^8*thetaFirstMode x) ≤ (503702940748439624600625287/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (53/64:ℝ) (213/256:ℝ) (10740033/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_213 :
    (172286636912110990649298113/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (213/256:ℝ) (107/128:ℝ) (82956802885821125866143/99468997421790285852160:ℝ) (4434083/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1283).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^8*thetaFirstMode x) ≤ (1150797133645937382066143731/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (213/256:ℝ) (107/128:ℝ) (151323/800000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_214 :
    (314510071607883658693577503/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (107/128:ℝ) (215/256:ℝ) (86519996812935046058841/103257800780870084584960:ℝ) (7797433/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1289).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^8*thetaFirstMode x) ≤ (210085251970099199520775307/1416709944860893564108800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (107/128:ℝ) (215/256:ℝ) (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_215 :
    (573451979195812506385869637/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (215/256:ℝ) (27/32:ℝ) (90218589795601773832359/107172285154106278812160:ℝ) (13697917/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1295).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^8*thetaFirstMode x) ≤ (143649261019071843350479439/1062532458645670173081600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (215/256:ℝ) (27/32:ℝ) (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_216 :
    (104432656216716888170596699/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (27/32:ℝ) (217/256:ℝ) (94057062584506765152057/111216007226212200348160:ℝ) (2403859/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1301).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^8*thetaFirstMode x) ≤ (2616115600631719739202612517/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (27/32:ℝ) (217/256:ℝ) (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_217 :
    (39573849552373488365911321/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (217/256:ℝ) (109/128:ℝ) (19608004486597651322715/23078521433218056637952:ℝ) (2633853/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1307).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^8*thetaFirstMode x) ≤ (237932968971250447033866877/2125064917291340346163200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (217/256:ℝ) (109/128:ℝ) (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_218 :
    (215681954188317739468998953/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (109/128:ℝ) (219/256:ℝ) (102172206059393137678593/119705810187199806492160:ℝ) (4612523/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1313).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^8*thetaFirstMode x) ≤ (86453706066031129277206847/850025966916536138465280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (109/128:ℝ) (219/256:ℝ) (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_219 :
    (3130806079709489734580813/34001038676661445538611200000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (219/256:ℝ) (55/64:ℝ) (106458482664671619457791/124159428129696431157760:ℝ) (64553/800000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1319).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^8*thetaFirstMode x) ≤ (49023129728247337624276259/531266229322835086540800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (219/256:ℝ) (55/64:ℝ) (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_220 :
    (35461235816656534559233193/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (55/64:ℝ) (221/256:ℝ) (110903857005979655461809/128757361064545117135360:ℝ) (705053/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1325).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^8*thetaFirstMode x) ≤ (3553807593867150664286428861/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (55/64:ℝ) (221/256:ℝ) (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_221 :
    (20057820590991403801708609/265633114661417543270400000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (221/256:ℝ) (111/128:ℝ) (115513472527065173117007/133503598919808937500160:ℝ) (384619/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1331).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^8*thetaFirstMode x) ≤ (178684459803287163746014599/2361183241434822606848000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (221/256:ℝ) (111/128:ℝ) (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_222 :
    (58015346577284060496905429/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (111/128:ℝ) (223/256:ℝ) (24058522909244262175605/27680444625863446871552:ℝ) (1073099/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1337).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^8*thetaFirstMode x) ≤ (12921162872482376050861857/188894659314785808547840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (111/128:ℝ) (223/256:ℝ) (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_223 :
    (261865415938417307068764673/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (223/256:ℝ) (7/8:ℝ) (125246713502597024463543/143457408303917490588160:ℝ) (4672993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1343).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^8*thetaFirstMode x) ≤ (58324746714854988307494347/944473296573929042739200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (223/256:ℝ) (7/8:ℝ) (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
