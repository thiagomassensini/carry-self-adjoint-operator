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

theorem thetaFirstMode_refined_cell_lower_4_064 :
    (27075371955572415219/137438953472000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/4:ℝ) (65/256:ℝ) (11165689815/44312986112:ℝ) (312833588019/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0387).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^4*thetaFirstMode x) ≤ (108317616366378028401/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/4:ℝ) (65/256:ℝ) (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_065 :
    (55394433296719802919/274877906944000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (65/256:ℝ) (33/128:ℝ) (36175296955/141376436736:ℝ) (601838973369/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0393).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x) ≤ (664834051525848587941/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (65/256:ℝ) (33/128:ℝ) (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_066 :
    (56595772283376551011/274877906944000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (33/128:ℝ) (67/256:ℝ) (39022160765/150209327616:ℝ) (578733076081/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0399).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^4*thetaFirstMode x) ≤ (339627118651687404719/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (33/128:ℝ) (67/256:ℝ) (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_067 :
    (23100906121395754651/109951162777600000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (67/256:ℝ) (17/64:ℝ) (14015167425/53149932032:ℝ) (222533942791/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0405).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x) ≤ (46209086818016680327/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (67/256:ℝ) (17/64:ℝ) (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_068 :
    (58861547884066793489/274877906944000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/64:ℝ) (69/256:ℝ) (45253402285/169110191616:ℝ) (534629738669/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0411).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^4*thetaFirstMode x) ≤ (28258074644170434811/131941395333120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/64:ℝ) (69/256:ℝ) (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_069 :
    (59921392656969317353/274877906944000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (69/256:ℝ) (35/128:ℝ) (48654184595/179203047936:ℝ) (513603201403/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0417).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x) ≤ (59931182797196794007/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (69/256:ℝ) (35/128:ℝ) (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_070 :
    (121859429536272135851/549755813888000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (35/128:ℝ) (71/256:ℝ) (17418806535/63247027712:ℝ) (986481581501/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0423).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^4*thetaFirstMode x) ≤ (243759419807787678733/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (35/128:ℝ) (71/256:ℝ) (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_071 :
    (123769153354302125721/549755813888000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (71/256:ℝ) (9/32:ℝ) (56068927915/200737199616:ℝ) (947056250241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0429).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x) ≤ (61895067172149498011/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (71/256:ℝ) (9/32:ℝ) (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_072 :
    (981003005372574921/4294967296000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/32:ℝ) (73/256:ℝ) (60100783925/212204484096:ℝ) (7100795361/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0435).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^4*thetaFirstMode x) ≤ (251180131258240769011/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/32:ℝ) (73/256:ℝ) (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_073 :
    (127253861607623946261/549755813888000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (73/256:ℝ) (37/128:ℝ) (21453773145/74718735872:ℝ) (871989821331/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0441).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x) ≤ (15909530075495081573/68719476736000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (73/256:ℝ) (37/128:ℝ) (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_074 :
    (32205659562974888809/137438953472000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (37/128:ℝ) (75/256:ℝ) (68860127245/236605825536:ℝ) (209073014059/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0447).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^4*thetaFirstMode x) ≤ (96634284127697480219/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (37/128:ℝ) (75/256:ℝ) (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_075 :
    (130272089530829059403/549755813888000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (75/256:ℝ) (19/64:ℝ) (73607064755/249566977536:ℝ) (801780473903/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0453).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x) ≤ (32573963497355911613/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (75/256:ℝ) (19/64:ℝ) (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_076 :
    (16449989326754683629/68719476736000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/64:ℝ) (77/256:ℝ) (26204085855/87684495872:ℝ) (96053406609/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0459).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^4*thetaFirstMode x) ≤ (263248727956395109973/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/64:ℝ) (77/256:ℝ) (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_077 :
    (132804139231596893843/549755813888000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (77/256:ℝ) (39/128:ℝ) (83886103075/277079364096:ℝ) (736204800113/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0465).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x) ≤ (398487799828994319197/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (77/256:ℝ) (39/128:ℝ) (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_078 :
    (66941558396915547537/274877906944000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (39/128:ℝ) (79/256:ℝ) (89439274085/291658799616:ℝ) (352542881727/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0471).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^4*thetaFirstMode x) ≤ (160690696845659252641/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (39/128:ℝ) (79/256:ℝ) (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_079 :
    (1078684226909260749/4398046511104000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (79/256:ℝ) (5/16:ℝ) (31760907465/102268723712:ℝ) (5400344349/800000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0477).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x) ≤ (269723972147831408021/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (79/256:ℝ) (5/16:ℝ) (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_080 :
    (135660381500308343063/549755813888000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/16:ℝ) (81/256:ℝ) (101427682405/322536039936:ℝ) (646049805863/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0483).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^4*thetaFirstMode x) ≤ (135687489033833119493/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/16:ℝ) (81/256:ℝ) (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_081 :
    (68178504006544110267/274877906944000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (81/256:ℝ) (41/128:ℝ) (107885674715/338863151616:ℝ) (309039745557/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0489).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x) ≤ (163661704192396850077/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (81/256:ℝ) (41/128:ℝ) (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_082 :
    (68462530324456178657/274877906944000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (41/128:ℝ) (83/256:ℝ) (38222836575/118600812032:ℝ) (295552913387/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0495).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^4*thetaFirstMode x) ≤ (273906861968082721563/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (41/128:ℝ) (83/256:ℝ) (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_083 :
    (137364508760761721153/549755813888000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (83/256:ℝ) (21/64:ℝ) (121788291235/373369007616:ℝ) (565102837013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0501).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x) ≤ (412180468980066356399/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (83/256:ℝ) (21/64:ℝ) (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_084 :
    (68837816495522211423/274877906944000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/64:ℝ) (85/256:ℝ) (129257420045/391578164736:ℝ) (270022426323/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0507).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^4*thetaFirstMode x) ≤ (413115626962273394473/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/64:ℝ) (85/256:ℝ) (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_085 :
    (2757180380260837961/10995116277760000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (85/256:ℝ) (43/128:ℝ) (45696199185/136815130112:ℝ) (10318130411/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0513).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x) ≤ (275778346979131819177/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (85/256:ℝ) (43/128:ℝ) (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_086 :
    (137915550375417188313/549755813888000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (43/128:ℝ) (87/256:ℝ) (145294829365/429986351616:ℝ) (492662812623/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0519).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^4*thetaFirstMode x) ≤ (165535518714171000607/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (43/128:ℝ) (87/256:ℝ) (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_087 :
    (27569280100773242421/109951162777600000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (87/256:ℝ) (11/32:ℝ) (153889428875/450216900096:ℝ) (94057806861/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0525).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x) ≤ (827265945835831085293/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (87/256:ℝ) (11/32:ℝ) (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_088 :
    (137653023894438181443/549755813888000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/32:ℝ) (89/256:ℝ) (54295340295/157051023872:ℝ) (448760832603/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0531).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^4*thetaFirstMode x) ≤ (137684803066366568507/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/32:ℝ) (89/256:ℝ) (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_089 :
    (68668573283599554391/274877906944000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (89/256:ℝ) (45/128:ℝ) (172298545195/492811086336:ℝ) (214027101841/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0537).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x) ≤ (164843312258923597813/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (89/256:ℝ) (45/128:ℝ) (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_090 :
    (68450377910870614039/274877906944000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (45/128:ℝ) (91/256:ℝ) (182141260205/515207348736:ℝ) (204072749989/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0543).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^4*thetaFirstMode x) ≤ (20540027312048811341/82463372083200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (45/128:ℝ) (91/256:ℝ) (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_091 :
    (136346089349242810697/549755813888000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (91/256:ℝ) (23/64:ℝ) (64142915505/179452815872:ℝ) (389011436837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0549).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x) ≤ (136379305424095524641/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (91/256:ℝ) (23/64:ℝ) (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_092 :
    (135675623764024306083/549755813888000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/64:ℝ) (93/256:ℝ) (203175910525/562281156096:ℝ) (370629098703/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0555).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^4*thetaFirstMode x) ≤ (203563908969413414387/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/64:ℝ) (93/256:ℝ) (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_093 :
    (67446031299811466241/274877906944000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (93/256:ℝ) (47/128:ℝ) (214397988035/586992431616:ℝ) (176487972411/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0561).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x) ≤ (202389179675241706451/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (93/256:ℝ) (47/128:ℝ) (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_094 :
    (66999161918229937297/274877906944000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (47/128:ℝ) (95/256:ℝ) (75370182615/204169805312:ℝ) (168014907247/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0567).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^4*thetaFirstMode x) ≤ (33508191009244135407/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (47/128:ℝ) (95/256:ℝ) (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_095 :
    (16624690876069082081/68719476736000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (95/256:ℝ) (3/8:ℝ) (238329495355/638849435136:ℝ) (39971116481/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0573).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x) ≤ (66516162108422029729/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (95/256:ℝ) (3/8:ℝ) (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
