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

theorem thetaFirstMode_cell_lower_0_096 :
    (2004791/128000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/4:ℝ) (97/128:ℝ) (193/256:ℝ) (2004791/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_385).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_096 :
    (∫ x in (3/4:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x) ≤ (4031657/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/4:ℝ) (97/128:ℝ) (279313/125000000000:ℝ) (1797153/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_384).2 (thetaFirstMode_node_388).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_097 :
    (804799/64000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (97/128:ℝ) (49/64:ℝ) (195/256:ℝ) (804799/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_389).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_097 :
    (∫ x in (97/128:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x) ≤ (1618759/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (97/128:ℝ) (49/64:ℝ) (1797153/1000000000000:ℝ) (288073/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_388).2 (thetaFirstMode_node_392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_098 :
    (160971/16000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (49/64:ℝ) (99/128:ℝ) (197/256:ℝ) (160971/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_393).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_098 :
    (∫ x in (49/64:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x) ≤ (80959/8000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (49/64:ℝ) (99/128:ℝ) (288073/200000000000:ℝ) (1150323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_392).2 (thetaFirstMode_node_396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_099 :
    (102661/12800000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (99/128:ℝ) (25/32:ℝ) (199/256:ℝ) (102661/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_397).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_099 :
    (∫ x in (99/128:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x) ≤ (413141/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (99/128:ℝ) (25/32:ℝ) (1150323/1000000000000:ℝ) (457691/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_396).2 (thetaFirstMode_node_400).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_100 :
    (815449/128000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/32:ℝ) (101/128:ℝ) (201/256:ℝ) (815449/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_401).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_100 :
    (∫ x in (25/32:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x) ≤ (1641147/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/32:ℝ) (101/128:ℝ) (457691/500000000000:ℝ) (145153/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_400).2 (thetaFirstMode_node_404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_101 :
    (80667/16000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (101/128:ℝ) (51/64:ℝ) (203/256:ℝ) (80667/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_405).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_101 :
    (∫ x in (101/128:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x) ≤ (81191/16000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (101/128:ℝ) (51/64:ℝ) (145153/200000000000:ℝ) (573291/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_404).2 (thetaFirstMode_node_408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_102 :
    (254401/64000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (51/64:ℝ) (103/128:ℝ) (205/256:ℝ) (254401/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_409).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_102 :
    (∫ x in (51/64:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x) ≤ (204887/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (51/64:ℝ) (103/128:ℝ) (573291/1000000000000:ℝ) (56393/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_408).2 (thetaFirstMode_node_412).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_103 :
    (399631/128000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (103/128:ℝ) (13/16:ℝ) (207/256:ℝ) (399631/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_413).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_103 :
    (∫ x in (103/128:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x) ≤ (804807/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (103/128:ℝ) (13/16:ℝ) (56393/125000000000:ℝ) (353663/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_412).2 (thetaFirstMode_node_416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_104 :
    (312673/128000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(105/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/16:ℝ) (105/128:ℝ) (209/256:ℝ) (312673/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_417).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_104 :
    (∫ x in (13/16:ℝ)..(105/128:ℝ), x^0*thetaFirstMode x) ≤ (62983/25600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/16:ℝ) (105/128:ℝ) (353663/1000000000000:ℝ) (276167/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_416).2 (thetaFirstMode_node_420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_105 :
    (121839/64000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(53/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (105/128:ℝ) (53/64:ℝ) (211/256:ℝ) (121839/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_421).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_105 :
    (∫ x in (105/128:ℝ)..(53/64:ℝ), x^0*thetaFirstMode x) ≤ (61371/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (105/128:ℝ) (53/64:ℝ) (276167/1000000000000:ℝ) (214801/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_420).2 (thetaFirstMode_node_424).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_106 :
    (5911/4000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(107/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (53/64:ℝ) (107/128:ℝ) (213/256:ℝ) (5911/31250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_425).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_106 :
    (∫ x in (53/64:ℝ)..(107/128:ℝ), x^0*thetaFirstMode x) ≤ (190601/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (53/64:ℝ) (107/128:ℝ) (214801/1000000000000:ℝ) (166401/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_424).2 (thetaFirstMode_node_428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_107 :
    (73117/64000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(27/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (107/128:ℝ) (27/32:ℝ) (215/256:ℝ) (73117/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_429).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_107 :
    (∫ x in (107/128:ℝ)..(27/32:ℝ), x^0*thetaFirstMode x) ≤ (147391/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (107/128:ℝ) (27/32:ℝ) (166401/1000000000000:ℝ) (128381/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_428).2 (thetaFirstMode_node_432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_108 :
    (112589/128000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(109/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/32:ℝ) (109/128:ℝ) (217/256:ℝ) (112589/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_433).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_108 :
    (∫ x in (27/32:ℝ)..(109/128:ℝ), x^0*thetaFirstMode x) ≤ (11351/12800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/32:ℝ) (109/128:ℝ) (128381/1000000000000:ℝ) (98639/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_432).2 (thetaFirstMode_node_436).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_109 :
    (21581/32000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(55/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (109/128:ℝ) (55/64:ℝ) (219/256:ℝ) (21581/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_437).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_109 :
    (∫ x in (109/128:ℝ)..(55/64:ℝ), x^0*thetaFirstMode x) ≤ (174107/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (109/128:ℝ) (55/64:ℝ) (98639/1000000000000:ℝ) (18867/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_436).2 (thetaFirstMode_node_440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_110 :
    (13181/25600000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(111/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (55/64:ℝ) (111/128:ℝ) (221/256:ℝ) (13181/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_441).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_110 :
    (∫ x in (55/64:ℝ)..(111/128:ℝ), x^0*thetaFirstMode x) ≤ (66481/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (55/64:ℝ) (111/128:ℝ) (18867/250000000000:ℝ) (28747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_440).2 (thetaFirstMode_node_444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_111 :
    (501/1280000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(7/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (111/128:ℝ) (7/8:ℝ) (223/256:ℝ) (501/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_445).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_111 :
    (∫ x in (111/128:ℝ)..(7/8:ℝ), x^0*thetaFirstMode x) ≤ (20221/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (111/128:ℝ) (7/8:ℝ) (28747/500000000000:ℝ) (43611/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_444).2 (thetaFirstMode_node_448).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_112 :
    (37919/128000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/8:ℝ) (113/128:ℝ) (225/256:ℝ) (37919/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_449).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_112 :
    (∫ x in (7/8:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x) ≤ (38273/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/8:ℝ) (113/128:ℝ) (43611/1000000000000:ℝ) (6587/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_448).2 (thetaFirstMode_node_452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_113 :
    (7143/32000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (113/128:ℝ) (57/64:ℝ) (227/256:ℝ) (7143/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_453).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_113 :
    (∫ x in (113/128:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x) ≤ (1803/8000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (113/128:ℝ) (57/64:ℝ) (6587/200000000000:ℝ) (24761/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_452).2 (thetaFirstMode_node_456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_114 :
    (2679/16000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (57/64:ℝ) (115/128:ℝ) (229/256:ℝ) (2679/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_457).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_114 :
    (∫ x in (57/64:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x) ≤ (10823/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (57/64:ℝ) (115/128:ℝ) (24761/1000000000000:ℝ) (18531/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_456).2 (thetaFirstMode_node_460).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_115 :
    (8001/64000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (115/128:ℝ) (29/32:ℝ) (231/256:ℝ) (8001/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_461).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_115 :
    (∫ x in (115/128:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x) ≤ (6467/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (115/128:ℝ) (29/32:ℝ) (18531/1000000000000:ℝ) (3451/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_460).2 (thetaFirstMode_node_464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_116 :
    (11893/128000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/32:ℝ) (117/128:ℝ) (233/256:ℝ) (11893/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_465).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_116 :
    (∫ x in (29/32:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x) ≤ (24039/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/32:ℝ) (117/128:ℝ) (3451/250000000000:ℝ) (2047/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_464).2 (thetaFirstMode_node_468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_117 :
    (8797/128000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (117/128:ℝ) (59/64:ℝ) (235/256:ℝ) (8797/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_469).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_117 :
    (∫ x in (117/128:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x) ≤ (4447/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (117/128:ℝ) (59/64:ℝ) (2047/200000000000:ℝ) (7553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_468).2 (thetaFirstMode_node_472).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_118 :
    (259/5120000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (59/64:ℝ) (119/128:ℝ) (237/256:ℝ) (259/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_473).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_118 :
    (∫ x in (59/64:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x) ≤ (131/2560000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (59/64:ℝ) (119/128:ℝ) (7553/1000000000000:ℝ) (5547/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_472).2 (thetaFirstMode_node_476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_119 :
    (4743/128000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (119/128:ℝ) (15/16:ℝ) (239/256:ℝ) (4743/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_477).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_119 :
    (∫ x in (119/128:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x) ≤ (3/80000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (119/128:ℝ) (15/16:ℝ) (5547/1000000000000:ℝ) (4053/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_476).2 (thetaFirstMode_node_480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_120 :
    (3457/128000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/16:ℝ) (121/128:ℝ) (241/256:ℝ) (3457/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_481).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_120 :
    (∫ x in (15/16:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x) ≤ (7/256000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/16:ℝ) (121/128:ℝ) (4053/1000000000000:ℝ) (2947/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_480).2 (thetaFirstMode_node_484).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_121 :
    (2507/128000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (121/128:ℝ) (61/64:ℝ) (243/256:ℝ) (2507/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_485).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_121 :
    (∫ x in (121/128:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x) ≤ (5079/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (121/128:ℝ) (61/64:ℝ) (2947/1000000000000:ℝ) (533/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_484).2 (thetaFirstMode_node_488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_122 :
    (1809/128000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (61/64:ℝ) (123/128:ℝ) (245/256:ℝ) (1809/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_489).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_122 :
    (∫ x in (61/64:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x) ≤ (3667/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (61/64:ℝ) (123/128:ℝ) (533/250000000000:ℝ) (307/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_488).2 (thetaFirstMode_node_492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_123 :
    (649/64000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (123/128:ℝ) (31/32:ℝ) (247/256:ℝ) (649/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_493).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_123 :
    (∫ x in (123/128:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x) ≤ (1317/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (123/128:ℝ) (31/32:ℝ) (307/200000000000:ℝ) (1099/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_492).2 (thetaFirstMode_node_496).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_124 :
    (927/128000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/32:ℝ) (125/128:ℝ) (249/256:ℝ) (927/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_497).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_124 :
    (∫ x in (31/32:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x) ≤ (941/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/32:ℝ) (125/128:ℝ) (1099/1000000000000:ℝ) (783/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_496).2 (thetaFirstMode_node_500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_125 :
    (329/64000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (125/128:ℝ) (63/64:ℝ) (251/256:ℝ) (329/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_501).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_125 :
    (∫ x in (125/128:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x) ≤ (1337/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (125/128:ℝ) (63/64:ℝ) (783/1000000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_500).2 (thetaFirstMode_node_504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_126 :
    (93/25600000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (63/64:ℝ) (127/128:ℝ) (253/256:ℝ) (93/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_505).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_126 :
    (∫ x in (63/64:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x) ≤ (189/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (63/64:ℝ) (127/128:ℝ) (277/500000000000:ℝ) (391/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_504).2 (thetaFirstMode_node_508).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_127 :
    (163/64000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (127/128:ℝ) (1/1:ℝ) (255/256:ℝ) (163/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_509).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_127 :
    (∫ x in (127/128:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x) ≤ (133/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (127/128:ℝ) (1/1:ℝ) (391/1000000000000:ℝ) (137/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_508).2 (thetaFirstMode_node_512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
