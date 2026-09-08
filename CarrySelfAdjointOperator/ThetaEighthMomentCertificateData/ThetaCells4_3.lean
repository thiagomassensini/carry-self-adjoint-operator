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

theorem thetaFirstMode_refined_cell_lower_4_096 :
    (16486622494497967651/68719476736000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/8:ℝ) (97/256:ℝ) (251071076165/666029999616:ℝ) (38021488771/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0579).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^4*thetaFirstMode x) ≤ (65964053747454476567/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/8:ℝ) (97/256:ℝ) (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_097 :
    (130688165270857720539/549755813888000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (97/256:ℝ) (49/128:ℝ) (88117293225/231356268032:ℝ) (289217755749/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0585).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x) ≤ (130723595853626198797/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (97/256:ℝ) (49/128:ℝ) (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_098 :
    (16173340812527503803/68719476736000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (49/128:ℝ) (99/256:ℝ) (278188842685/722983727616:ℝ) (34360733913/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0591).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^4*thetaFirstMode x) ≤ (258844864580254048569/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (49/128:ℝ) (99/256:ℝ) (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_099 :
    (31998113539464550229/137438953472000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (99/256:ℝ) (25/64:ℝ) (292599252995/752792833536:ℝ) (65289014729/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0597).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x) ≤ (38408522048987417389/164926744166400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (99/256:ℝ) (25/64:ℝ) (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_100 :
    (31627317901001149137/137438953472000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/64:ℝ) (101/256:ℝ) (102533584335/261171456512:ℝ) (62002130637/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0603).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^4*thetaFirstMode x) ≤ (12654544240756388419/54975581388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/64:ℝ) (101/256:ℝ) (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_101 :
    (124941220842950675817/549755813888000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (101/256:ℝ) (51/128:ℝ) (323211343315/815166767616:ℝ) (235423870107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0609).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x) ≤ (749865483995367037697/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (101/256:ℝ) (51/128:ℝ) (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_102 :
    (123292448298281314591/549755813888000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (51/128:ℝ) (103/256:ℝ) (339449386325/847768644096:ℝ) (223383115081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0615).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^4*thetaFirstMode x) ≤ (23124181449441519899/103079215104000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (51/128:ℝ) (103/256:ℝ) (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_103 :
    (121567190609322776659/549755813888000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (103/256:ℝ) (13/32:ℝ) (118777869945/293779599872:ℝ) (211867677739/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0621).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x) ≤ (121603840008361305421/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (103/256:ℝ) (13/32:ℝ) (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_104 :
    (23953952101240524983/109951162777600000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/32:ℝ) (105/256:ℝ) (373883110645/915896219136:ℝ) (40171877183/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0627).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^4*thetaFirstMode x) ≤ (718839060384592531901/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/32:ℝ) (105/256:ℝ) (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_105 :
    (117904532811418422531/549755813888000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (105/256:ℝ) (53/128:ℝ) (392117358155/951460071936:ℝ) (190340475381/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0633).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x) ≤ (88456014464548837747/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (105/256:ℝ) (53/128:ℝ) (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_106 :
    (115975930611309860641/549755813888000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (53/128:ℝ) (107/256:ℝ) (137018732655/329349903872:ℝ) (180293589811/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0639).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^4*thetaFirstMode x) ≤ (58006395363042354217/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (53/128:ℝ) (107/256:ℝ) (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_107 :
    (22797682329743321731/109951162777600000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (107/256:ℝ) (27/64:ℝ) (430719855475/1025684676096:ℝ) (34140356071/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0645).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x) ≤ (342075846466778636999/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (107/256:ℝ) (27/64:ℝ) (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_108 :
    (111946454966203195391/549755813888000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/64:ℝ) (109/256:ℝ) (451128939485/1064384687616:ℝ) (161548504811/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0651).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^4*thetaFirstMode x) ≤ (671899836299008706291/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/64:ℝ) (109/256:ℝ) (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_109 :
    (109854547868439947597/549755813888000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (109/256:ℝ) (55/128:ℝ) (157434815265/368056550912:ℝ) (152817626447/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0657).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x) ≤ (54945674935532984333/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (109/256:ℝ) (55/128:ℝ) (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_110 :
    (13464646650390773703/68719476736000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (55/128:ℝ) (111/256:ℝ) (494267760805/1145059662336:ℝ) (18061676553/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0663).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^4*thetaFirstMode x) ≤ (646523380157052991861/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (55/128:ℝ) (111/256:ℝ) (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_111 :
    (105538797035944775809/549755813888000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (111/256:ℝ) (7/16:ℝ) (517040665115/1187074991616:ℝ) (136560531889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0669).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x) ≤ (211150825734769756519/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (111/256:ℝ) (7/16:ℝ) (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_112 :
    (25830964181364721347/137438953472000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/16:ℝ) (113/256:ℝ) (180215112375/410078700032:ℝ) (32251013427/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0675).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^4*thetaFirstMode x) ≤ (206720672201978810401/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/16:ℝ) (113/256:ℝ) (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_113 :
    (101076749440266157877/549755813888000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (113/256:ℝ) (57/128:ℝ) (565104356635/1274563631616:ℝ) (121809443867/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0681).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x) ≤ (303339191913853739209/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (113/256:ℝ) (57/128:ℝ) (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_114 :
    (98801821147765268203/549755813888000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (57/128:ℝ) (115/256:ℝ) (590440708445/1320078414336:ℝ) (114962562553/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0687).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^4*thetaFirstMode x) ≤ (593027657470602605807/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (57/128:ℝ) (115/256:ℝ) (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_115 :
    (48251678048344237161/274877906944000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (115/256:ℝ) (29/64:ℝ) (205559261985/455600486912:ℝ) (54224830461/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0693).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x) ≤ (193078515385444933659/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (115/256:ℝ) (29/64:ℝ) (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_116 :
    (23546391703560602371/137438953472000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/64:ℝ) (117/256:ℝ) (643839394765/1414753967616:ℝ) (25564344391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0699).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^4*thetaFirstMode x) ≤ (282663664264555537639/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/64:ℝ) (117/256:ℝ) (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_117 :
    (22963146162847036003/137438953472000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (117/256:ℝ) (59/128:ℝ) (671949756275/1463957316096:ℝ) (24093183673/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0705).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x) ≤ (275663898232458920599/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (117/256:ℝ) (59/128:ℝ) (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_118 :
    (89508450872179392333/549755813888000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (59/128:ℝ) (119/256:ℝ) (233677837095/504811023872:ℝ) (90783134043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0711).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^4*thetaFirstMode x) ≤ (89543533604559527093/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (59/128:ℝ) (119/256:ℝ) (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_119 :
    (5447319270235964233/34359738368000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (119/256:ℝ) (15/32:ℝ) (731115723595/1566202983936:ℝ) (5342272033/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0717).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x) ≤ (130787801368288688029/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (119/256:ℝ) (15/32:ℝ) (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_120 :
    (84802393686158011029/549755813888000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/32:ℝ) (121/256:ℝ) (762221883605/1619288987136:ℝ) (80440537629/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0723).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^4*thetaFirstMode x) ≤ (42418402726502472363/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/32:ℝ) (121/256:ℝ) (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_121 :
    (257650094732850623/1717986918400000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (121/256:ℝ) (61/128:ℝ) (264792637305/557904399872:ℝ) (236450633/312500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0729).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x) ≤ (164964142795523425601/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (121/256:ℝ) (61/128:ℝ) (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_122 :
    (80097621685546450099/549755813888000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (61/128:ℝ) (123/256:ℝ) (827610162925/1729497924096:ℝ) (71136221209/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0735).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^4*thetaFirstMode x) ≤ (160262539487458065399/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (61/128:ℝ) (123/256:ℝ) (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_123 :
    (38877322719453010611/274877906944000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (123/256:ℝ) (31/64:ℝ) (861945428435/1786665647616:ℝ) (33422911431/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0741).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x) ≤ (466727274147659225203/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (123/256:ℝ) (31/64:ℝ) (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_124 :
    (37711224018541295871/274877906944000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/64:ℝ) (125/256:ℝ) (299136980415/615079680512:ℝ) (31391293371/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0747).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^4*thetaFirstMode x) ≤ (150910493257657415423/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/64:ℝ) (125/256:ℝ) (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_125 :
    (73104240022341112607/549755813888000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (125/256:ℝ) (63/128:ℝ) (934034378755/1905240961536:ℝ) (58936436357/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0753).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x) ≤ (146273168109981020913/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (125/256:ℝ) (63/128:ℝ) (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_126 :
    (885038648476233051/6871947673600000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (63/128:ℝ) (127/256:ℝ) (971843866565/1966694447616:ℝ) (691220421/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0759).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^4*thetaFirstMode x) ≤ (70834962771926440249/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (63/128:ℝ) (127/256:ℝ) (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_127 :
    (34260965244870526107/274877906944000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (127/256:ℝ) (1/2:ℝ) (336955994025/676540908032:ℝ) (25928386587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0765).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x) ≤ (4284581917110093339/34359738368000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (127/256:ℝ) (1/2:ℝ) (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
