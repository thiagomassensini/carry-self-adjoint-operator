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

theorem thetaFirstMode_refined_cell_lower_0_064 :
    (1251584440439/25600000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/4:ℝ) (65/256:ℝ) (129/512:ℝ) (1251584440439/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0385).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x) ≤ (1251770818809/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/4:ℝ) (65/256:ℝ) (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_065 :
    (37622399689/800000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (65/256:ℝ) (33/128:ℝ) (131/512:ℝ) (37622399689/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0391).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x) ≤ (2408198869709/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (65/256:ℝ) (33/128:ℝ) (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_066 :
    (115769423549/2560000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (33/128:ℝ) (67/256:ℝ) (133/512:ℝ) (115769423549/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0397).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x) ≤ (1157873158663/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (33/128:ℝ) (67/256:ℝ) (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_067 :
    (69555468773/1600000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (67/256:ℝ) (17/64:ℝ) (135/512:ℝ) (69555468773/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0403).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x) ≤ (17809003453/409600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (67/256:ℝ) (17/64:ℝ) (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_068 :
    (1069467409093/25600000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/64:ℝ) (69/256:ℝ) (137/512:ℝ) (1069467409093/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0409).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x) ≤ (2139277865323/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/64:ℝ) (69/256:ℝ) (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_069 :
    (102740490249/2560000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (69/256:ℝ) (35/128:ℝ) (139/512:ℝ) (102740490249/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0415).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x) ≤ (102757275193/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (69/256:ℝ) (35/128:ℝ) (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_070 :
    (246667763263/6400000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (35/128:ℝ) (71/256:ℝ) (141/512:ℝ) (246667763263/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0421).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x) ≤ (1973670495967/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (35/128:ℝ) (71/256:ℝ) (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_071 :
    (473618539969/12800000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (71/256:ℝ) (9/32:ℝ) (143/512:ℝ) (473618539969/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0427).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x) ≤ (236849410449/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (71/256:ℝ) (9/32:ℝ) (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_072 :
    (14204286931/400000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/32:ℝ) (73/256:ℝ) (145/512:ℝ) (14204286931/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0433).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x) ≤ (1818462631161/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/32:ℝ) (73/256:ℝ) (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_073 :
    (872154459999/25600000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (73/256:ℝ) (37/128:ℝ) (147/512:ℝ) (872154459999/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0439).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x) ≤ (21807695677/640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (73/256:ℝ) (37/128:ℝ) (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_074 :
    (418224557351/12800000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (37/128:ℝ) (75/256:ℝ) (149/512:ℝ) (418224557351/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0445).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x) ≤ (1673197847/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (37/128:ℝ) (75/256:ℝ) (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_075 :
    (801930276291/25600000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (75/256:ℝ) (19/64:ℝ) (151/512:ℝ) (801930276291/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0451).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x) ≤ (200519138769/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (75/256:ℝ) (19/64:ℝ) (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_076 :
    (768570109637/25600000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/64:ℝ) (77/256:ℝ) (153/512:ℝ) (768570109637/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0457).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x) ≤ (1537425776531/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/64:ℝ) (77/256:ℝ) (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_077 :
    (736341008679/25600000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (77/256:ℝ) (39/128:ℝ) (155/512:ℝ) (736341008679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0463).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x) ≤ (736480318549/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (77/256:ℝ) (39/128:ℝ) (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_078 :
    (176303902207/6400000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (39/128:ℝ) (79/256:ℝ) (157/512:ℝ) (176303902207/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0469).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x) ≤ (1410702965653/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (39/128:ℝ) (79/256:ℝ) (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_079 :
    (27006671959/1024000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (79/256:ℝ) (5/16:ℝ) (159/512:ℝ) (27006671959/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0475).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x) ≤ (1350598542839/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (79/256:ℝ) (5/16:ℝ) (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_080 :
    (32308386653/1280000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/16:ℝ) (81/256:ℝ) (161/512:ℝ) (32308386653/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0481).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x) ≤ (646296839653/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/16:ℝ) (81/256:ℝ) (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_081 :
    (309095920617/12800000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (81/256:ℝ) (41/128:ℝ) (163/512:ℝ) (309095920617/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0487).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x) ≤ (1236635238009/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (81/256:ℝ) (41/128:ℝ) (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_082 :
    (591212840587/25600000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (41/128:ℝ) (83/256:ℝ) (165/512:ℝ) (591212840587/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0493).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x) ≤ (1182670655673/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (41/128:ℝ) (83/256:ℝ) (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_083 :
    (565204745437/25600000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (83/256:ℝ) (21/64:ℝ) (167/512:ℝ) (565204745437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0499).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x) ≤ (565323981681/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (83/256:ℝ) (21/64:ℝ) (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_084 :
    (540141877167/25600000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/64:ℝ) (85/256:ℝ) (169/512:ℝ) (540141877167/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0505).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x) ≤ (540257903083/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/64:ℝ) (85/256:ℝ) (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_085 :
    (515998873633/25600000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (85/256:ℝ) (43/128:ℝ) (171/512:ℝ) (515998873633/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0511).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x) ≤ (1032223462003/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (85/256:ℝ) (43/128:ℝ) (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_086 :
    (4927506981/256000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (43/128:ℝ) (87/256:ℝ) (173/512:ℝ) (4927506981/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0517).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x) ≤ (985720859491/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (43/128:ℝ) (87/256:ℝ) (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_087 :
    (18814905909/1024000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (87/256:ℝ) (11/32:ℝ) (175/512:ℝ) (18814905909/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0523).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x) ≤ (940958594921/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (87/256:ℝ) (11/32:ℝ) (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_088 :
    (448840361591/25600000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/32:ℝ) (89/256:ℝ) (177/512:ℝ) (448840361591/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0529).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x) ≤ (448943974157/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/32:ℝ) (89/256:ℝ) (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_089 :
    (214064914129/12800000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (89/256:ℝ) (45/128:ℝ) (179/512:ℝ) (214064914129/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0535).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x) ≤ (856460898537/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (89/256:ℝ) (45/128:ℝ) (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_090 :
    (408217392869/25600000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (45/128:ℝ) (91/256:ℝ) (181/512:ℝ) (408217392869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0541).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x) ≤ (102078767187/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (45/128:ℝ) (91/256:ℝ) (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_091 :
    (15563190551/1024000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (91/256:ℝ) (23/64:ℝ) (183/512:ℝ) (15563190551/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0547).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x) ≤ (389174541701/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (91/256:ℝ) (23/64:ℝ) (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_092 :
    (370694018701/25600000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/64:ℝ) (93/256:ℝ) (185/512:ℝ) (370694018701/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0553).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x) ≤ (92696486637/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/64:ℝ) (93/256:ℝ) (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_093 :
    (22064850653/1600000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (93/256:ℝ) (47/128:ℝ) (187/512:ℝ) (22064850653/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0559).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x) ≤ (176563368363/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (93/256:ℝ) (47/128:ℝ) (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_094 :
    (336088372119/25600000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (47/128:ℝ) (95/256:ℝ) (189/512:ℝ) (336088372119/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0565).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x) ≤ (1050546081/80000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (47/128:ℝ) (95/256:ℝ) (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_095 :
    (319824521899/25600000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (95/256:ℝ) (3/8:ℝ) (191/512:ℝ) (319824521899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0571).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x) ≤ (4998565513/400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (95/256:ℝ) (3/8:ℝ) (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
