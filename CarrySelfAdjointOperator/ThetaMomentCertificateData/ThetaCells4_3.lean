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

theorem thetaFirstMode_cell_lower_4_096 :
    (868650114401523/171798691840000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/4:ℝ) (97/128:ℝ) (251071076165/333014999808:ℝ) (2003283/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_387).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_096 :
    (∫ x in (3/4:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x) ≤ (1048121963803657/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/4:ℝ) (97/128:ℝ) (279313/125000000000:ℝ) (1797153/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_384).2 (thetaFirstMode_node_388).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_097 :
    (726775440885891/171798691840000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (97/128:ℝ) (49/64:ℝ) (88117293225/115678134016:ℝ) (1608381/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_391).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_097 :
    (∫ x in (97/128:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x) ≤ (730913761456129/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (97/128:ℝ) (49/64:ℝ) (1797153/1000000000000:ℝ) (288073/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_388).2 (thetaFirstMode_node_392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_098 :
    (605681971272959/171798691840000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (49/64:ℝ) (99/128:ℝ) (278188842685/361491863808:ℝ) (1286789/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_395).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_098 :
    (∫ x in (49/64:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x) ≤ (114233768228303/32212254720000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (49/64:ℝ) (99/128:ℝ) (288073/200000000000:ℝ) (1150323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_392).2 (thetaFirstMode_node_396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_099 :
    (20110252824533/6871947673600000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (99/128:ℝ) (25/32:ℝ) (292599252995/376396416768:ℝ) (41033/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_399).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_099 :
    (∫ x in (99/128:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x) ≤ (3034888589312597/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (99/128:ℝ) (25/32:ℝ) (1150323/1000000000000:ℝ) (457691/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_396).2 (thetaFirstMode_node_400).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_100 :
    (415640600325321/171798691840000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/32:ℝ) (101/128:ℝ) (102533584335/130585728256:ℝ) (814821/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_403).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_100 :
    (∫ x in (25/32:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x) ≤ (836508312386469/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/32:ℝ) (101/128:ℝ) (457691/500000000000:ℝ) (145153/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_400).2 (thetaFirstMode_node_404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_101 :
    (342219852167447/171798691840000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (101/128:ℝ) (51/64:ℝ) (323211343315/407583383808:ℝ) (644837/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_407).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_101 :
    (∫ x in (101/128:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x) ≤ (64583187384767/32212254720000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (101/128:ℝ) (51/64:ℝ) (145153/200000000000:ℝ) (573291/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_404).2 (thetaFirstMode_node_408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_102 :
    (56121069987191/34359738368000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (51/64:ℝ) (103/128:ℝ) (339449386325/423884322048:ℝ) (101681/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_411).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_102 :
    (∫ x in (51/64:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x) ≤ (338988430401607/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (51/64:ℝ) (103/128:ℝ) (573291/1000000000000:ℝ) (56393/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_408).2 (thetaFirstMode_node_412).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_103 :
    (229123415004077/171798691840000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (103/128:ℝ) (13/16:ℝ) (118777869945/146889799936:ℝ) (399317/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_415).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_103 :
    (∫ x in (103/128:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x) ≤ (461428556931549/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (103/128:ℝ) (13/16:ℝ) (56393/125000000000:ℝ) (353663/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_412).2 (thetaFirstMode_node_416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_104 :
    (93147718802013/85899345920000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/16:ℝ) (105/128:ℝ) (373883110645/457948109568:ℝ) (156213/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_419).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_104 :
    (∫ x in (13/16:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x) ≤ (187632199912627/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/16:ℝ) (105/128:ℝ) (353663/1000000000000:ℝ) (276167/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_416).2 (thetaFirstMode_node_420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_105 :
    (30164877033247/34359738368000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (105/128:ℝ) (53/64:ℝ) (392117358155/475730035968:ℝ) (48697/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_423).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_105 :
    (∫ x in (105/128:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x) ≤ (56978455093447/64424509440000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (105/128:ℝ) (53/64:ℝ) (276167/1000000000000:ℝ) (214801/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_420).2 (thetaFirstMode_node_424).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_106 :
    (121577072620531/171798691840000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (53/64:ℝ) (107/128:ℝ) (137018732655/164674951936:ℝ) (189001/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_427).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_106 :
    (∫ x in (53/64:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x) ≤ (122508848511731/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (53/64:ℝ) (107/128:ℝ) (214801/1000000000000:ℝ) (166401/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_424).2 (thetaFirstMode_node_428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_107 :
    (24392731466869/42949672960000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (107/128:ℝ) (27/32:ℝ) (430719855475/512842338048:ℝ) (36529/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_431).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_107 :
    (∫ x in (107/128:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x) ≤ (295030809139453/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (107/128:ℝ) (27/32:ℝ) (166401/1000000000000:ℝ) (128381/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_428).2 (thetaFirstMode_node_432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_108 :
    (38978238472469/85899345920000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/32:ℝ) (109/128:ℝ) (451128939485/532192343808:ℝ) (56249/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_435).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_108 :
    (∫ x in (27/32:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x) ≤ (9824304400329/21474836480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/32:ℝ) (109/128:ℝ) (128381/1000000000000:ℝ) (98639/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_432).2 (thetaFirstMode_node_436).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_109 :
    (62003870480103/171798691840000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (109/128:ℝ) (55/64:ℝ) (157434815265/184028275456:ℝ) (86253/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_439).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_109 :
    (∫ x in (109/128:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x) ≤ (125057228753441/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (109/128:ℝ) (55/64:ℝ) (98639/1000000000000:ℝ) (18867/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_436).2 (thetaFirstMode_node_440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_110 :
    (49090705614901/171798691840000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (55/64:ℝ) (111/128:ℝ) (494267760805/572529831168:ℝ) (65851/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_443).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_110 :
    (∫ x in (55/64:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x) ≤ (148559819950489/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (55/64:ℝ) (111/128:ℝ) (18867/250000000000:ℝ) (28747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_440).2 (thetaFirstMode_node_444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_111 :
    (38687361331579/171798691840000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (111/128:ℝ) (7/8:ℝ) (517040665115/593537495808:ℝ) (50059/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_447).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_111 :
    (∫ x in (111/128:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x) ≤ (234220085361257/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (111/128:ℝ) (7/8:ℝ) (28747/500000000000:ℝ) (43611/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_444).2 (thetaFirstMode_node_448).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_112 :
    (30345022867407/171798691840000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(113/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/8:ℝ) (113/128:ℝ) (180215112375/205039350016:ℝ) (37887/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_451).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_112 :
    (∫ x in (7/8:ℝ)..(113/128:ℝ), x^4*thetaFirstMode x) ≤ (30628848813653/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/8:ℝ) (113/128:ℝ) (43611/1000000000000:ℝ) (6587/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_448).2 (thetaFirstMode_node_452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_113 :
    (5922239999247/42949672960000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(57/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (113/128:ℝ) (57/64:ℝ) (565104356635/637281815808:ℝ) (7137/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_455).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_113 :
    (∫ x in (113/128:ℝ)..(57/64:ℝ), x^4*thetaFirstMode x) ≤ (17938484112569/128849018880000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (113/128:ℝ) (57/64:ℝ) (6587/200000000000:ℝ) (24761/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_452).2 (thetaFirstMode_node_456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_114 :
    (9201874728057/85899345920000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(115/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (57/64:ℝ) (115/128:ℝ) (590440708445/660039207168:ℝ) (10707/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_459).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_114 :
    (∫ x in (57/64:ℝ)..(115/128:ℝ), x^4*thetaFirstMode x) ≤ (27881324181959/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (57/64:ℝ) (115/128:ℝ) (24761/1000000000000:ℝ) (18531/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_456).2 (thetaFirstMode_node_460).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_115 :
    (14227726924289/171798691840000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(29/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (115/128:ℝ) (29/32:ℝ) (205559261985/227800243456:ℝ) (15989/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_463).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_115 :
    (∫ x in (115/128:ℝ)..(29/32:ℝ), x^4*thetaFirstMode x) ≤ (28748850279577/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (115/128:ℝ) (29/32:ℝ) (18531/1000000000000:ℝ) (3451/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_460).2 (thetaFirstMode_node_464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_116 :
    (5472039922921/85899345920000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(117/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/32:ℝ) (117/128:ℝ) (643839394765/707376983808:ℝ) (5941/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_467).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_116 :
    (∫ x in (29/32:ℝ)..(117/128:ℝ), x^4*thetaFirstMode x) ≤ (66367924216003/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/32:ℝ) (117/128:ℝ) (3451/250000000000:ℝ) (2047/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_464).2 (thetaFirstMode_node_468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_117 :
    (8376771387479/171798691840000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(59/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (117/128:ℝ) (59/64:ℝ) (671949756275/731978658048:ℝ) (8789/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_471).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_117 :
    (∫ x in (117/128:ℝ)..(59/64:ℝ), x^4*thetaFirstMode x) ≤ (4234797564097/85899345920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (117/128:ℝ) (59/64:ℝ) (2047/200000000000:ℝ) (7553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_468).2 (thetaFirstMode_node_472).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_118 :
    (637915493057/17179869184000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(119/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (59/64:ℝ) (119/128:ℝ) (233677837095/252405511936:ℝ) (647/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_475).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_118 :
    (∫ x in (59/64:ℝ)..(119/128:ℝ), x^4*thetaFirstMode x) ≤ (3226234132403/85899345920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (59/64:ℝ) (119/128:ℝ) (7553/1000000000000:ℝ) (5547/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_472).2 (thetaFirstMode_node_476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_119 :
    (4832184857339/171798691840000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(15/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (119/128:ℝ) (15/16:ℝ) (731115723595/783101491968:ℝ) (4739/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_479).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_119 :
    (∫ x in (119/128:ℝ)..(15/16:ℝ), x^4*thetaFirstMode x) ≤ (2445067560189/85899345920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (119/128:ℝ) (15/16:ℝ) (5547/1000000000000:ℝ) (4053/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_476).2 (thetaFirstMode_node_480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_120 :
    (1820645885927/85899345920000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(121/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/16:ℝ) (121/128:ℝ) (762221883605/809644493568:ℝ) (1727/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_483).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_120 :
    (∫ x in (15/16:ℝ)..(121/128:ℝ), x^4*thetaFirstMode x) ≤ (5529841212077/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/16:ℝ) (121/128:ℝ) (4053/1000000000000:ℝ) (2947/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_480).2 (thetaFirstMode_node_484).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_121 :
    (545918172531/34359738368000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(61/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (121/128:ℝ) (61/64:ℝ) (264792637305/278952199936:ℝ) (501/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_487).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_121 :
    (∫ x in (121/128:ℝ)..(61/64:ℝ), x^4*thetaFirstMode x) ≤ (5529495361269/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (121/128:ℝ) (61/64:ℝ) (2947/1000000000000:ℝ) (533/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_484).2 (thetaFirstMode_node_488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_122 :
    (2034637206277/171798691840000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(123/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (61/64:ℝ) (123/128:ℝ) (827610162925/864748962048:ℝ) (1807/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_491).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_122 :
    (∫ x in (61/64:ℝ)..(123/128:ℝ), x^4*thetaFirstMode x) ≤ (4125292913577/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (61/64:ℝ) (123/128:ℝ) (533/250000000000:ℝ) (307/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_488).2 (thetaFirstMode_node_492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_123 :
    (1508662333957/171798691840000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(31/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (123/128:ℝ) (31/32:ℝ) (861945428435/893332823808:ℝ) (1297/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_495).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_123 :
    (∫ x in (123/128:ℝ)..(31/32:ℝ), x^4*thetaFirstMode x) ≤ (4591672225079/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (123/128:ℝ) (31/32:ℝ) (307/200000000000:ℝ) (1099/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_492).2 (thetaFirstMode_node_496).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_124 :
    (556214632963/85899345920000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(125/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/32:ℝ) (125/128:ℝ) (299136980415/307539840256:ℝ) (463/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_499).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_124 :
    (∫ x in (31/32:ℝ)..(125/128:ℝ), x^4*thetaFirstMode x) ≤ (1129432817213/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/32:ℝ) (125/128:ℝ) (1099/1000000000000:ℝ) (783/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_496).2 (thetaFirstMode_node_500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_125 :
    (408088721579/85899345920000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(63/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (125/128:ℝ) (63/64:ℝ) (934034378755/952620480768:ℝ) (329/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_503).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_125 :
    (∫ x in (125/128:ℝ)..(63/64:ℝ), x^4*thetaFirstMode x) ≤ (4970682721553/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (125/128:ℝ) (63/64:ℝ) (783/1000000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_500).2 (thetaFirstMode_node_504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_126 :
    (37131600899/10737418240000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(127/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (63/64:ℝ) (127/128:ℝ) (971843866565/983347223808:ℝ) (29/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_507).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_126 :
    (∫ x in (63/64:ℝ)..(127/128:ℝ), x^4*thetaFirstMode x) ≤ (3626634473017/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (63/64:ℝ) (127/128:ℝ) (277/500000000000:ℝ) (391/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_504).2 (thetaFirstMode_node_508).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_127 :
    (215383140643/85899345920000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (127/128:ℝ) (1/1:ℝ) (336955994025/338270454016:ℝ) (163/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_511).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_127 :
    (∫ x in (127/128:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x) ≤ (35116080383/13743895347200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (127/128:ℝ) (1/1:ℝ) (391/1000000000000:ℝ) (137/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_508).2 (thetaFirstMode_node_512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
