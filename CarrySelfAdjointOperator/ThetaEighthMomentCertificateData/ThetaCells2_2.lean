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

theorem thetaFirstMode_refined_cell_lower_2_064 :
    (2603244093873647/838860800000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/4:ℝ) (65/256:ℝ) (3220227/12780544:ℝ) (625729691661/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0386).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^2*thetaFirstMode x) ≤ (5207263549553441/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/4:ℝ) (65/256:ℝ) (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_065 :
    (3098815154574589/1006632960000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (65/256:ℝ) (33/128:ℝ) (3372333/13179904:ℝ) (240759471259/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0392).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x) ≤ (4132380397837889/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (65/256:ℝ) (33/128:ℝ) (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_066 :
    (1919702035160071/629145600000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (33/128:ℝ) (67/256:ℝ) (3529155/13585408:ℝ) (144697522813/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0398).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^2*thetaFirstMode x) ≤ (10239993302323599/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (33/128:ℝ) (67/256:ℝ) (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_067 :
    (15210570636392309/5033164800000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (67/256:ℝ) (17/64:ℝ) (3690765/13997056:ℝ) (1112778596561/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0404).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x) ≤ (12170372444457233/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (67/256:ℝ) (17/64:ℝ) (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_068 :
    (1505342905042333/503316480000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/64:ℝ) (69/256:ℝ) (3857235/14414848:ℝ) (106936343329/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0410).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^2*thetaFirstMode x) ≤ (12044674790172959/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/64:ℝ) (69/256:ℝ) (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_069 :
    (4962228692580459/1677721600000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (69/256:ℝ) (35/128:ℝ) (4028637/14838784:ℝ) (1027305643347/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0416).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x) ≤ (14889118284883093/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (69/256:ℝ) (35/128:ℝ) (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_070 :
    (7355419668483991/2516582400000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (35/128:ℝ) (71/256:ℝ) (4205043/15268864:ℝ) (493288154281/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0422).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^2*thetaFirstMode x) ≤ (58853150197209773/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (35/128:ℝ) (71/256:ℝ) (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_071 :
    (4842129425732459/1677721600000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (71/256:ℝ) (9/32:ℝ) (4386525/15705088:ℝ) (947146656921/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0428).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x) ≤ (9685900477968101/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (71/256:ℝ) (9/32:ℝ) (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_072 :
    (3583458247483621/1258291200000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/32:ℝ) (73/256:ℝ) (4573155/16147456:ℝ) (227247019309/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0434).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^2*thetaFirstMode x) ≤ (19115077159237051/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/32:ℝ) (73/256:ℝ) (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_073 :
    (117780608894253/41943040000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (73/256:ℝ) (37/128:ℝ) (4765005/16595968:ℝ) (21801803337/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0440).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x) ≤ (7068079295975849/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (73/256:ℝ) (37/128:ℝ) (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_074 :
    (4642135502127759/1677721600000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (37/128:ℝ) (75/256:ℝ) (4962147/17050624:ℝ) (836370578727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0446).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^2*thetaFirstMode x) ≤ (580370869916431/209715200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (37/128:ℝ) (75/256:ℝ) (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_075 :
    (13712528661352871/5033164800000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (75/256:ℝ) (19/64:ℝ) (5164653/17511424:ℝ) (801855368771/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0452).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x) ≤ (1142919173422309/419430400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (75/256:ℝ) (19/64:ℝ) (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_076 :
    (899502082833697/335544320000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/64:ℝ) (77/256:ℝ) (5372595/17978368:ℝ) (153699735063/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0458).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^2*thetaFirstMode x) ≤ (53980151656387537/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/64:ℝ) (77/256:ℝ) (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_077 :
    (663345068191879/251658240000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (77/256:ℝ) (39/128:ℝ) (5586045/18451456:ℝ) (36813644941/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0464).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x) ≤ (552892145691049/209715200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (77/256:ℝ) (39/128:ℝ) (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_078 :
    (6518060318954611/2516582400000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (39/128:ℝ) (79/256:ℝ) (5805075/18930688:ℝ) (352575340453/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0470).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^2*thetaFirstMode x) ≤ (3476968653254663/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (39/128:ℝ) (79/256:ℝ) (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_079 :
    (6400332159759551/2516582400000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (79/256:ℝ) (5/16:ℝ) (6029757/19416064:ℝ) (337552458191/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0476).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x) ≤ (51212704159104331/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (79/256:ℝ) (5/16:ℝ) (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_080 :
    (4187000165770921/1677721600000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/16:ℝ) (81/256:ℝ) (6260163/19907584:ℝ) (646108764843/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0482).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^2*thetaFirstMode x) ≤ (12563510369867953/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/16:ℝ) (81/256:ℝ) (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_081 :
    (2463517866677209/1006632960000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (81/256:ℝ) (41/128:ℝ) (6496365/20405248:ℝ) (123627132367/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0488).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x) ≤ (9856076495484383/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (81/256:ℝ) (41/128:ℝ) (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_082 :
    (1005906862598673/419430400000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (41/128:ℝ) (83/256:ℝ) (6738435/20909056:ℝ) (147789832401/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0494).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^2*thetaFirstMode x) ≤ (16097844442307113/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (41/128:ℝ) (83/256:ℝ) (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_083 :
    (1970220295153383/838860800000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (83/256:ℝ) (21/64:ℝ) (6986445/21419008:ℝ) (282576893697/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0500).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x) ≤ (11823815749960811/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (83/256:ℝ) (21/64:ℝ) (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_084 :
    (11569339892557247/5033164800000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/64:ℝ) (85/256:ℝ) (7240467/21935104:ℝ) (540093361307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0506).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^2*thetaFirstMode x) ≤ (5785912599663037/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/64:ℝ) (85/256:ℝ) (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_085 :
    (5657679262833143/2516582400000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (85/256:ℝ) (43/128:ℝ) (7500573/22457344:ℝ) (257976346853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0512).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x) ≤ (45271334069633597/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (85/256:ℝ) (43/128:ℝ) (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_086 :
    (184329807769741/83886080000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (43/128:ℝ) (87/256:ℝ) (7766835/22985728:ℝ) (24635337609/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0518).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^2*thetaFirstMode x) ≤ (2949933741435619/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (43/128:ℝ) (87/256:ℝ) (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_087 :
    (432121160743849/201326592000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (87/256:ℝ) (11/32:ℝ) (8039325/23520256:ℝ) (18813233521/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0524).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x) ≤ (14407304767267641/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (87/256:ℝ) (11/32:ℝ) (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_088 :
    (5272733781969071/2516582400000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/32:ℝ) (89/256:ℝ) (8318115/24060928:ℝ) (224400297143/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0530).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^2*thetaFirstMode x) ≤ (21095804137329343/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/32:ℝ) (89/256:ℝ) (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_089 :
    (10287479172309199/5033164800000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (89/256:ℝ) (45/128:ℝ) (8603277/24607744:ℝ) (428092013329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0536).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x) ≤ (41159588468915821/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (89/256:ℝ) (45/128:ℝ) (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_090 :
    (501471312952487/251658240000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (45/128:ℝ) (91/256:ℝ) (8894883/25160704:ℝ) (20409072197/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0542).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^2*thetaFirstMode x) ≤ (20063652351408929/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (45/128:ℝ) (91/256:ℝ) (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_091 :
    (325721942807083/167772160000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (91/256:ℝ) (23/64:ℝ) (9193005/25719808:ℝ) (38904559797/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0548).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x) ≤ (9774038745270287/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (91/256:ℝ) (23/64:ℝ) (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_092 :
    (3171503831326061/1677721600000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/64:ℝ) (93/256:ℝ) (9497715/26285056:ℝ) (370661556507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0554).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^2*thetaFirstMode x) ≤ (19033742229922619/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/64:ℝ) (93/256:ℝ) (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_093 :
    (9258308702900617/5033164800000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (93/256:ℝ) (47/128:ℝ) (9809085/26856448:ℝ) (353006775571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0560).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x) ≤ (18521292288260561/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (93/256:ℝ) (47/128:ℝ) (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_094 :
    (1500559852797751/838860800000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (47/128:ℝ) (95/256:ℝ) (10127187/27433984:ℝ) (168029545683/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0566).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^2*thetaFirstMode x) ≤ (6003782056564909/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (47/128:ℝ) (95/256:ℝ) (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_095 :
    (8749958194065689/5033164800000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (95/256:ℝ) (3/8:ℝ) (10452093/28017664:ℝ) (319796725049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0572).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x) ≤ (17504494886578643/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (95/256:ℝ) (3/8:ℝ) (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
