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

theorem thetaFirstMode_refined_cell_lower_6_096 :
    (4912851286942121630547/144115188075855872000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/8:ℝ) (97/256:ℝ) (4364764631770375/11578443094624256:ℝ) (6082910757/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0580).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x) ≤ (6879823657919729469396517/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/8:ℝ) (97/256:ℝ) (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_097 :
    (1739282855973823329965771/50440315826549555200000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (97/256:ℝ) (49/128:ℝ) (4691376420086265/12317222597752832:ℝ) (289192734869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0586).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x) ≤ (1739754393598784525699083/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (97/256:ℝ) (49/128:ℝ) (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_098 :
    (1757463428367393981963867/50440315826549555200000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (49/128:ℝ) (99/256:ℝ) (5038717029229415/13094874042423296:ℝ) (274862139921/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0592).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x) ≤ (14063587408911795534527507/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (49/128:ℝ) (99/256:ℝ) (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_099 :
    (887000869356614417339713/25220157913274777600000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (99/256:ℝ) (25/64:ℝ) (5407871390045593/13913016748648448:ℝ) (130566778813/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0598).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x) ≤ (3549000111529289203700757/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (99/256:ℝ) (25/64:ℝ) (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_100 :
    (1788864358528004959956689/50440315826549555200000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (25/64:ℝ) (101/256:ℝ) (5799969393965607/14773320111515648:ℝ) (247987194389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0604).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x) ≤ (3578751653116917261825833/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/64:ℝ) (101/256:ℝ) (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_101 :
    (16089486150289811714119/450359962737049600000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (101/256:ℝ) (51/128:ℝ) (6216187276192985/15677504623056896:ℝ) (14712728779/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0610).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x) ≤ (2060053567990401536022191/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (101/256:ℝ) (51/128:ℝ) (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_102 :
    (1813451830195850333991723/50440315826549555200000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (51/128:ℝ) (103/256:ℝ) (6657749026974535/16627342904440832:ℝ) (223363971597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0616).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x) ≤ (7255955940564476572876833/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (51/128:ℝ) (103/256:ℝ) (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_103 :
    (182313303345860997400231/5044031582654955520000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (103/256:ℝ) (13/32:ℝ) (7125927831236025/17624660748486656:ℝ) (21184955023/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0622).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x) ≤ (3647365339022653795867379/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (103/256:ℝ) (13/32:ℝ) (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_104 :
    (114440708201324797110863/3152519739159347200000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (13/32:ℝ) (105/256:ℝ) (7622047536865223/18671338172499968:ℝ) (12552639143/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0628).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x) ≤ (14652905364868852168890913/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/32:ℝ) (105/256:ℝ) (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_105 :
    (459299187547131901584779/12610078956637388800000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (105/256:ℝ) (53/128:ℝ) (8147484151924537/19769310481430528:ℝ) (47581059389/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0634).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x) ≤ (29404327813722527969237/807045053224792883200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (105/256:ℝ) (53/128:ℝ) (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_106 :
    (1841564064444604284321601/50440315826549555200000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (53/128:ℝ) (107/256:ℝ) (8703667371075495/20920569341351936:ℝ) (180278229643/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0640).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x) ≤ (115134335656927324485833/3152519739159347200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (53/128:ℝ) (107/256:ℝ) (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_107 :
    (1844152770080410650425931/50440315826549555200000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (107/256:ℝ) (27/64:ℝ) (9292082131497305/22127163863263232:ℝ) (170687255559/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0646).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x) ≤ (7378997149312578818605973/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (107/256:ℝ) (27/64:ℝ) (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_108 :
    (1844967041394684753099583/50440315826549555200000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (27/64:ℝ) (109/256:ℝ) (9914270198581735/23391201697212416:ℝ) (161534774899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0652).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x) ≤ (2109227871885141963934263/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/64:ℝ) (109/256:ℝ) (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_109 :
    (461003917296274279640953/12610078956637388800000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (109/256:ℝ) (55/128:ℝ) (10571831781686553/24714850136741888:ℝ) (38201163163/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0658).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x) ≤ (7378533754002869188901299/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (109/256:ℝ) (55/128:ℝ) (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_110 :
    (1841311981610882151554311/50440315826549555200000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (55/128:ℝ) (111/256:ℝ) (11266427180229767/26100337233655808:ℝ) (144481157641/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0664).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x) ≤ (14735517948503342300639557/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (55/128:ℝ) (111/256:ℝ) (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_111 :
    (183687374829346510846957/5044031582654955520000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (111/256:ℝ) (7/16:ℝ) (11999778460406905/27549952923109376:ℝ) (13654896061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0670).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x) ≤ (14700088398752450350804517/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (111/256:ℝ) (7/16:ℝ) (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_112 :
    (1830723068264476622332267/50440315826549555200000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/16:ℝ) (113/256:ℝ) (12773671162813575/29066050159020032:ℝ) (128993131963/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0676).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^6*thetaFirstMode x) ≤ (14650955475542549247570751/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/16:ℝ) (113/256:ℝ) (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_113 :
    (1822886242445885339966581/50440315826549555200000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (113/256:ℝ) (57/128:ℝ) (13589956041255545/30651046059800576:ℝ) (121799139163/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0682).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^6*thetaFirstMode x) ≤ (7294164709770730944350539/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (113/256:ℝ) (57/128:ℝ) (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_114 :
    (90669681585700006152661/2522015791327477760000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (57/128:ℝ) (115/256:ℝ) (14450550833028583/32307423064414208:ℝ) (5747642191/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0688).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^6*thetaFirstMode x) ≤ (14512452959512634611071017/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (57/128:ℝ) (115/256:ℝ) (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_115 :
    (901139750558467022018849/25220157913274777600000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (115/256:ℝ) (29/64:ℝ) (15357442060950297/34037730098751488:ℝ) (54220249229/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0694).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^6*thetaFirstMode x) ≤ (2884720013394387668561067/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (115/256:ℝ) (29/64:ℝ) (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_116 :
    (357916370263302431825249/10088063165309911040000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (29/64:ℝ) (117/256:ℝ) (16312686867426215/35844583752329216:ℝ) (20449748597/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0700).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^6*thetaFirstMode x) ≤ (7161037304311259122680139/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/64:ℝ) (117/256:ℝ) (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_117 :
    (126810159873202376455443/3602879701896396800000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (117/256:ℝ) (59/128:ℝ) (17318414880832345/37730669465311232:ℝ) (48182300439/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0706).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^6*thetaFirstMode x) ≤ (7104104451750104968450243/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (117/256:ℝ) (59/128:ℝ) (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_118 :
    (439901395446071286678211/12610078956637388800000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (59/128:ℝ) (119/256:ℝ) (18376830114496455/39698742725851136:ℝ) (22693868773/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0712).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^6*thetaFirstMode x) ≤ (7041181096832588635512419/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (59/128:ℝ) (119/256:ℝ) (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_119 :
    (435604991241807963272047/12610078956637388800000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (119/256:ℝ) (15/32:ℝ) (19490212898560313/41751630277756928:ℝ) (21367285927/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0718).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^6*thetaFirstMode x) ≤ (697245951856859646877383/20176126330619822080000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (119/256:ℝ) (15/32:ℝ) (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_120 :
    (61565586573218603199679/1801439850948198400000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (15/32:ℝ) (121/256:ℝ) (20660921845005127/43892231338477568:ℝ) (20108438833/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0724).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^6*thetaFirstMode x) ≤ (3449071907498119505689519/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/32:ℝ) (121/256:ℝ) (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_121 :
    (1703908731319931995891667/50440315826549555200000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (121/256:ℝ) (61/128:ℝ) (21891395846122425/46123518827411456:ℝ) (75657824261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0730).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^6*thetaFirstMode x) ≤ (13636898068060509458599643/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (121/256:ℝ) (61/128:ℝ) (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_122 :
    (1682693171104628610472721/50440315826549555200000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (61/128:ℝ) (123/256:ℝ) (23184156106712615/48448540604536832:ℝ) (71130225419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0736).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^6*thetaFirstMode x) ≤ (1923885793776862563820407/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (61/128:ℝ) (123/256:ℝ) (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_123 :
    (415062077645494487626421/12610078956637388800000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (123/256:ℝ) (31/64:ℝ) (24541808210293465/50870420719364096:ℝ) (16710047273/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0742).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^6*thetaFirstMode x) ≤ (13287663575304548393280983/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (123/256:ℝ) (31/64:ℝ) (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_124 :
    (1636634766188502033313961/50440315826549555200000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (31/64:ℝ) (125/256:ℝ) (25967044219600743/53392360670210048:ℝ) (62777295461/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0748).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^6*thetaFirstMode x) ≤ (13098772011811528669089749/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/64:ℝ) (125/256:ℝ) (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_125 :
    (230273566698381971291029/7205759403792793600000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (125/256:ℝ) (63/128:ℝ) (27462644811663257/56017640673794048:ℝ) (58931468953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0754).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^6*thetaFirstMode x) ≤ (12901025266381782331114107/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (125/256:ℝ) (63/128:ℝ) (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_126 :
    (793076457753532244725051/25220157913274777600000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (63/128:ℝ) (127/256:ℝ) (29031481447734535/58749620945156096:ℝ) (27646486213/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0760).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^6*thetaFirstMode x) ≤ (396716729467457335371177/12610078956637388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (63/128:ℝ) (127/256:ℝ) (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_127 :
    (1559413948895607472756901/50440315826549555200000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (127/256:ℝ) (1/2:ℝ) (30676518578363385/61591742987896832:ℝ) (51852401189/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0766).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x) ≤ (6240512465637223460217099/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (127/256:ℝ) (1/2:ℝ) (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
