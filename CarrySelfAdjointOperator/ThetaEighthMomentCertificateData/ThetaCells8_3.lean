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

theorem thetaFirstMode_refined_cell_lower_8_096 :
    (91502109521120850380695321/18889465931478580854784000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/8:ℝ) (97/256:ℝ) (65332341813084493257/173304480845017500160:ℝ) (12164766849/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0581).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^8*thetaFirstMode x) ≤ (1608863896548606368909291033/332041393326771929088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/8:ℝ) (97/256:ℝ) (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_097 :
    (1771554789638789150226683753/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (97/256:ℝ) (49/128:ℝ) (14336762398671353355/37640552179499351552:ℝ) (72291929829/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0587).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^8*thetaFirstMode x) ≤ (21264420838940706313025868637/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (97/256:ℝ) (49/128:ℝ) (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_098 :
    (7307906267313371780724786577/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (49/128:ℝ) (99/256:ℝ) (78578341309131839793/204209882504936988160:ℝ) (274838413521/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0593).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^8*thetaFirstMode x) ≤ (219297688982284252475091918139/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (49/128:ℝ) (99/256:ℝ) (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_099 :
    (2509067029740051329622200211/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (99/256:ℝ) (25/64:ℝ) (86056132492075958991/221395846441879298560:ℝ) (261111060999/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0599).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^8*thetaFirstMode x) ≤ (56469865924557928028903229769/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (99/256:ℝ) (25/64:ℝ) (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_100 :
    (2581194466970309151878462499/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (25/64:ℝ) (101/256:ℝ) (94159912870084059009/239834298071963906560:ℝ) (247965870591/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0605).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^8*thetaFirstMode x) ≤ (58093480554719651242877204581/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (25/64:ℝ) (101/256:ℝ) (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_101 :
    (238695996699414096126730039/42501298345826806923264000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (101/256:ℝ) (51/128:ℝ) (102935065125197358207/259602677601152028160:ℝ) (2353834549/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0611).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^8*thetaFirstMode x) ≤ (238765461239983041545827755473/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (101/256:ℝ) (51/128:ℝ) (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_102 :
    (24496598569261922304945981359/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (51/128:ℝ) (103/256:ℝ) (22485952682885662245/56156474985950039552:ℝ) (223344831929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0617).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^8*thetaFirstMode x) ≤ (12251927276057380803596617909/2125064917291340346163200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (51/128:ℝ) (103/256:ℝ) (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_103 :
    (25110206765273304393156214651/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (103/256:ℝ) (13/32:ℝ) (122695115016799804743/303458889196134300160:ℝ) (211831426291/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0623).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^8*thetaFirstMode x) ≤ (25117776916860318335191067137/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (103/256:ℝ) (13/32:ℝ) (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_104 :
    (25708903205617032237557701081/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (13/32:ℝ) (105/256:ℝ) (133785307673187732441/327721993105999567360:ℝ) (200825070001/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0629).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^8*thetaFirstMode x) ≤ (17144527788339556837799846059/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (13/32:ℝ) (105/256:ℝ) (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_105 :
    (13145595998863598217033824117/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (105/256:ℝ) (53/128:ℝ) (145757762788870993959/353665902141891765760:ℝ) (95154001427/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0635).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^8*thetaFirstMode x) ≤ (5479042175963563367859306973/885443715538058477568000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (105/256:ℝ) (53/128:ℝ) (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_106 :
    (13427804205508904502692290967/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (53/128:ℝ) (107/256:ℝ) (158673294672040530657/381389448748703772160:ℝ) (90131436197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0641).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^8*thetaFirstMode x) ≤ (67160359834279761764094514709/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (53/128:ℝ) (107/256:ℝ) (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_107 :
    (27400724773932883146157060153/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (107/256:ℝ) (27/64:ℝ) (34519255196979847635/82199252318350141952:ℝ) (170672733493/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0647).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^8*thetaFirstMode x) ≤ (27409587913071543455607637543/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (107/256:ℝ) (27/64:ℝ) (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_108 :
    (9308385410958046419884118719/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (27/64:ℝ) (109/256:ℝ) (187594809587397482193/442594949984965788160:ℝ) (161521047537/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0653).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^8*thetaFirstMode x) ≤ (55868697879451916294125688867/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (27/64:ℝ) (109/256:ℝ) (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_109 :
    (28427566344204490118010528251/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (109/256:ℝ) (55/128:ℝ) (203740906957094489391/476299293587687964160:ℝ) (152791681241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0659).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^8*thetaFirstMode x) ≤ (3554636244631827340557860429/531266229322835086540800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (109/256:ℝ) (55/128:ℝ) (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_110 :
    (14453336233422428117430952913/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (55/128:ℝ) (111/256:ℝ) (221110673372114090409/512228437469441512960:ℝ) (72234452543/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0665).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^8*thetaFirstMode x) ≤ (289165276903265286389432870293/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (55/128:ℝ) (111/256:ℝ) (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_111 :
    (14680625465700282077056010827/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (111/256:ℝ) (7/16:ℝ) (239784500047674155607/550507092643036572160:ℝ) (68268695707/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0671).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^8*thetaFirstMode x) ≤ (293714378164608374672261687317/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (111/256:ℝ) (7/16:ℝ) (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_112 :
    (14895070976628605606712829201/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/16:ℝ) (113/256:ℝ) (51969452684042517525/118253148433449738752:ℝ) (64491106081/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0677).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x) ≤ (59601319760631401932370993311/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/16:ℝ) (113/256:ℝ) (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_113 :
    (5032042378204400137084446269/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (113/256:ℝ) (57/128:ℝ) (281388531776708917143/634640852921264412160:ℝ) (60894418137/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0683).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x) ≤ (151015509662547061194464139277/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (113/256:ℝ) (57/128:ℝ) (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_114 :
    (30566569469964792919135979053/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (57/128:ℝ) (115/256:ℝ) (304502779430409389841/680775093154008808960:ℝ) (114943126783/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0689).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x) ≤ (305777448638851656105314205827/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (57/128:ℝ) (115/256:ℝ) (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_115 :
    (15456073003025065869061262929/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (115/256:ℝ) (29/64:ℝ) (329289608647804933359/729817555912400028160:ℝ) (54215668789/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0695).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x) ≤ (103078821384336878676369979391/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (115/256:ℝ) (29/64:ℝ) (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_116 :
    (2602343570977274234947439977/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (29/64:ℝ) (117/256:ℝ) (355853979535385553057/781923988453504668160:ℝ) (25560027471/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0701).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x) ≤ (156199724212443522182960507311/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (29/64:ℝ) (117/256:ℝ) (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_117 :
    (31513722801849729977869217353/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (117/256:ℝ) (59/128:ℝ) (76861289619680304915/167451405549299389952:ℝ) (96356468443/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0707).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x) ≤ (31525862216049211093218589283/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (117/256:ℝ) (59/128:ℝ) (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_118 :
    (31768255390651419560479590997/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (59/128:ℝ) (119/256:ℝ) (414763412687601229593/895986442171253532160:ℝ) (90767817427/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0713).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x) ≤ (158903536710719994104755889959/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (59/128:ℝ) (119/256:ℝ) (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_119 :
    (10663706472070840860617386309/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (119/256:ℝ) (15/32:ℝ) (447347369053687618791/958289379521344821760:ℝ) (85461936087/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0719).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x) ≤ (80009695727359085841229874921/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (119/256:ℝ) (15/32:ℝ) (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_120 :
    (2145453670693062103710958237/283341988972178712821760000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (15/32:ℝ) (121/256:ℝ) (482187174233040082809/1024350621420112591360:ℝ) (16085394831/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0725).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x) ≤ (80487161294160254706869377949/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (15/32:ℝ) (121/256:ℝ) (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_121 :
    (6467979118494926126285812111/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (121/256:ℝ) (61/128:ℝ) (519418319492085968007/1094362844259452700160:ℝ) (15130289401/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0731).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x) ≤ (323532485708456260519620651379/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (121/256:ℝ) (61/128:ℝ) (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_122 :
    (16232534328007470892053170471/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (61/128:ℝ) (123/256:ℝ) (111836642512315217805/233705377354370135552:ℝ) (35562115301/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0737).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x) ≤ (7217490528833572663446988721/944473296573929042739200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (61/128:ℝ) (123/256:ℝ) (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_123 :
    (32557097125670963691071491769/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (123/256:ℝ) (31/64:ℝ) (601631469395921364543/1247052024347146908160:ℝ) (66834556229/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0743).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x) ≤ (108570043718491665319141058153/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (123/256:ℝ) (31/64:ℝ) (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_124 :
    (1019245298103802149590776657/132816557330708771635200000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (31/64:ℝ) (125/256:ℝ) (646920215696683136241/1330156250206437122560:ℝ) (1961625157/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0749).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x) ≤ (326300336263059431949012693229/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (31/64:ℝ) (125/256:ℝ) (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_125 :
    (510020157894427239768447349/66408278665354385817600000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (125/256:ℝ) (63/128:ℝ) (695214398443277823759/1418066563546442882560:ℝ) (920726599/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0755).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x) ≤ (4354097659336697007457697993/566683977944357425643520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (125/256:ℝ) (63/128:ℝ) (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_126 :
    (3625942031335458524231566937/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (63/128:ℝ) (127/256:ℝ) (746687107677957320457/1511019264768615708160:ℝ) (55288311903/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0761).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x) ≤ (2176544558355570303409450399/283341988972178712821760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (63/128:ℝ) (127/256:ℝ) (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_127 :
    (2716047328878783031073482597/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (127/256:ℝ) (1/2:ℝ) (160303981759231989195/321852051581633495552:ℝ) (12962007471/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0767).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x) ≤ (5434582443098642055039041869/708354972430446782054400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (127/256:ℝ) (1/2:ℝ) (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
