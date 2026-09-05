import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes00
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes01
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes02
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes03
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes04
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes05
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes06
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes07
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes08
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes09
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes10
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes11
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes12
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes13
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes14
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes15
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes16
import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaFirstMode_cell_upper_6_096 :
    (∫ x in (3/4:ℝ)..(97/128:ℝ), x^6*thetaFirstMode x) ≤ (3642800024489964743/1261007895663738880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/4:ℝ) (97/128:ℝ) (279313/125000000000:ℝ) (1797153/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_384).2 (thetaFirstMode_node_388).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_097 :
    (∫ x in (97/128:ℝ)..(49/64:ℝ), x^6*thetaFirstMode x) ≤ (19449296984227457297/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (97/128:ℝ) (49/64:ℝ) (1797153/1000000000000:ℝ) (288073/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_388).2 (thetaFirstMode_node_392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_098 :
    (∫ x in (49/64:ℝ)..(99/128:ℝ), x^6*thetaFirstMode x) ≤ (33091969730182955233/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (49/64:ℝ) (99/128:ℝ) (288073/200000000000:ℝ) (1150323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_392).2 (thetaFirstMode_node_396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_099 :
    (∫ x in (99/128:ℝ)..(25/32:ℝ), x^6*thetaFirstMode x) ≤ (56069021703770271643/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (99/128:ℝ) (25/32:ℝ) (1150323/1000000000000:ℝ) (457691/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_396).2 (thetaFirstMode_node_400).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_100 :
    (∫ x in (25/32:ℝ)..(101/128:ℝ), x^6*thetaFirstMode x) ≤ (47299450568351933337/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/32:ℝ) (101/128:ℝ) (457691/500000000000:ℝ) (145153/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_400).2 (thetaFirstMode_node_404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_101 :
    (∫ x in (101/128:ℝ)..(51/64:ℝ), x^6*thetaFirstMode x) ≤ (19865632133169506767/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (101/128:ℝ) (51/64:ℝ) (145153/200000000000:ℝ) (573291/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_404).2 (thetaFirstMode_node_408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_102 :
    (∫ x in (51/64:ℝ)..(103/128:ℝ), x^6*thetaFirstMode x) ≤ (7595454912097237/7205759403792793600000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (51/64:ℝ) (103/128:ℝ) (573291/1000000000000:ℝ) (56393/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_408).2 (thetaFirstMode_node_412).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_103 :
    (∫ x in (103/128:ℝ)..(13/16:ℝ), x^6*thetaFirstMode x) ≤ (27671585545420572087/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (103/128:ℝ) (13/16:ℝ) (56393/125000000000:ℝ) (353663/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_412).2 (thetaFirstMode_node_416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_104 :
    (∫ x in (13/16:ℝ)..(105/128:ℝ), x^6*thetaFirstMode x) ≤ (1433828542735000963/1970324836974592000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/16:ℝ) (105/128:ℝ) (353663/1000000000000:ℝ) (276167/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_416).2 (thetaFirstMode_node_420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_105 :
    (∫ x in (105/128:ℝ)..(53/64:ℝ), x^6*thetaFirstMode x) ≤ (9467383225657891497/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (105/128:ℝ) (53/64:ℝ) (276167/1000000000000:ℝ) (214801/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_420).2 (thetaFirstMode_node_424).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_106 :
    (∫ x in (53/64:ℝ)..(107/128:ℝ), x^6*thetaFirstMode x) ≤ (1944691391303660357/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (53/64:ℝ) (107/128:ℝ) (214801/1000000000000:ℝ) (166401/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_424).2 (thetaFirstMode_node_428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_107 :
    (∫ x in (107/128:ℝ)..(27/32:ℝ), x^6*thetaFirstMode x) ≤ (3181086090808105913/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (107/128:ℝ) (27/32:ℝ) (166401/1000000000000:ℝ) (128381/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_428).2 (thetaFirstMode_node_432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_108 :
    (∫ x in (27/32:ℝ)..(109/128:ℝ), x^6*thetaFirstMode x) ≤ (5179549829951425571/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/32:ℝ) (109/128:ℝ) (128381/1000000000000:ℝ) (98639/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_432).2 (thetaFirstMode_node_436).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_109 :
    (∫ x in (109/128:ℝ)..(55/64:ℝ), x^6*thetaFirstMode x) ≤ (8394138470715600581/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (109/128:ℝ) (55/64:ℝ) (98639/1000000000000:ℝ) (18867/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_436).2 (thetaFirstMode_node_440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_110 :
    (∫ x in (55/64:ℝ)..(111/128:ℝ), x^6*thetaFirstMode x) ≤ (3384870901001218243/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (55/64:ℝ) (111/128:ℝ) (18867/250000000000:ℝ) (28747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_440).2 (thetaFirstMode_node_444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_111 :
    (∫ x in (111/128:ℝ)..(7/8:ℝ), x^6*thetaFirstMode x) ≤ (5433609217220935157/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (111/128:ℝ) (7/8:ℝ) (28747/500000000000:ℝ) (43611/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_444).2 (thetaFirstMode_node_448).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_112 :
    (∫ x in (7/8:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x) ≤ (1085025261398989339/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/8:ℝ) (113/128:ℝ) (43611/1000000000000:ℝ) (6587/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_448).2 (thetaFirstMode_node_452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_113 :
    (∫ x in (113/128:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x) ≤ (1724839322800797741/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (113/128:ℝ) (57/64:ℝ) (6587/200000000000:ℝ) (24761/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_452).2 (thetaFirstMode_node_456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_114 :
    (∫ x in (57/64:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x) ≤ (1364155466260922959/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (57/64:ℝ) (115/128:ℝ) (24761/1000000000000:ℝ) (18531/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_456).2 (thetaFirstMode_node_460).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_115 :
    (∫ x in (115/128:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x) ≤ (2146908279418283809/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (115/128:ℝ) (29/32:ℝ) (18531/1000000000000:ℝ) (3451/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_460).2 (thetaFirstMode_node_464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_116 :
    (∫ x in (29/32:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x) ≤ (1680800593266999753/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/32:ℝ) (117/128:ℝ) (3451/250000000000:ℝ) (2047/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_464).2 (thetaFirstMode_node_468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_117 :
    (∫ x in (117/128:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x) ≤ (654582004521272999/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (117/128:ℝ) (59/64:ℝ) (2047/200000000000:ℝ) (7553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_468).2 (thetaFirstMode_node_472).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_118 :
    (∫ x in (59/64:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x) ≤ (507208529845845343/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (59/64:ℝ) (119/128:ℝ) (7553/1000000000000:ℝ) (5547/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_472).2 (thetaFirstMode_node_476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_119 :
    (∫ x in (119/128:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x) ≤ (390911811869217441/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (119/128:ℝ) (15/16:ℝ) (5547/1000000000000:ℝ) (4053/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_476).2 (thetaFirstMode_node_480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_120 :
    (∫ x in (15/16:ℝ)..(121/128:ℝ), x^6*thetaFirstMode x) ≤ (42807307296378563/2251799813685248000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/16:ℝ) (121/128:ℝ) (4053/1000000000000:ℝ) (2947/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_480).2 (thetaFirstMode_node_484).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_121 :
    (∫ x in (121/128:ℝ)..(61/64:ℝ), x^6*thetaFirstMode x) ≤ (456937460213201337/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (121/128:ℝ) (61/64:ℝ) (2947/1000000000000:ℝ) (533/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_484).2 (thetaFirstMode_node_488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_122 :
    (∫ x in (61/64:ℝ)..(123/128:ℝ), x^6*thetaFirstMode x) ≤ (346532612728928797/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (61/64:ℝ) (123/128:ℝ) (533/250000000000:ℝ) (307/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_488).2 (thetaFirstMode_node_492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_123 :
    (∫ x in (123/128:ℝ)..(31/32:ℝ), x^6*thetaFirstMode x) ≤ (65338430607584217/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (123/128:ℝ) (31/32:ℝ) (307/200000000000:ℝ) (1099/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_492).2 (thetaFirstMode_node_496).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_124 :
    (∫ x in (31/32:ℝ)..(125/128:ℝ), x^6*thetaFirstMode x) ≤ (48998491884032869/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/32:ℝ) (125/128:ℝ) (1099/1000000000000:ℝ) (783/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_496).2 (thetaFirstMode_node_500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_125 :
    (∫ x in (125/128:ℝ)..(63/64:ℝ), x^6*thetaFirstMode x) ≤ (146080810531205411/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (125/128:ℝ) (63/64:ℝ) (783/1000000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_500).2 (thetaFirstMode_node_504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_126 :
    (∫ x in (63/64:ℝ)..(127/128:ℝ), x^6*thetaFirstMode x) ≤ (108286512203772267/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (63/64:ℝ) (127/128:ℝ) (277/500000000000:ℝ) (391/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_504).2 (thetaFirstMode_node_508).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_127 :
    (∫ x in (127/128:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x) ≤ (15977340708036391/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (127/128:ℝ) (1/1:ℝ) (391/1000000000000:ℝ) (137/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_508).2 (thetaFirstMode_node_512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
