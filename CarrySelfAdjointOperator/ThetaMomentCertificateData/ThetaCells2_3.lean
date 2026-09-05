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

theorem thetaFirstMode_cell_lower_2_096 :
    (55986781669/6291456000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/4:ℝ) (97/128:ℝ) (10783875/14303744:ℝ) (2004037/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_386).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_096 :
    (∫ x in (3/4:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x) ≤ (9007215779/1006632960000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/4:ℝ) (97/128:ℝ) (279313/125000000000:ℝ) (1797153/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_384).2 (thetaFirstMode_node_388).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_097 :
    (1529559527/209715200000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (97/128:ℝ) (49/64:ℝ) (11122605/14601728:ℝ) (160899/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_390).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_097 :
    (∫ x in (97/128:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x) ≤ (23073997253/3145728000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (97/128:ℝ) (49/64:ℝ) (1797153/1000000000000:ℝ) (288073/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_388).2 (thetaFirstMode_node_392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_098 :
    (18734400373/3145728000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (49/64:ℝ) (99/128:ℝ) (11468355/14902784:ℝ) (643639/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_394).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_098 :
    (∫ x in (49/64:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x) ≤ (25126195493/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (49/64:ℝ) (99/128:ℝ) (288073/200000000000:ℝ) (1150323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_392).2 (thetaFirstMode_node_396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_099 :
    (30479671117/6291456000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (99/128:ℝ) (25/32:ℝ) (11821197/15206912:ℝ) (1026217/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_398).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_099 :
    (∫ x in (99/128:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x) ≤ (40886751717/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (99/128:ℝ) (25/32:ℝ) (1150323/1000000000000:ℝ) (457691/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_396).2 (thetaFirstMode_node_400).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_100 :
    (4939881127/1258291200000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/32:ℝ) (101/128:ℝ) (12181203/15514112:ℝ) (163027/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_402).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_100 :
    (∫ x in (25/32:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x) ≤ (33139559159/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/32:ℝ) (101/128:ℝ) (457691/500000000000:ℝ) (145153/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_400).2 (thetaFirstMode_node_404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_101 :
    (9968836501/3145728000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (101/128:ℝ) (51/64:ℝ) (12548445/15824384:ℝ) (322543/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_406).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_101 :
    (∫ x in (101/128:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x) ≤ (13378149227/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (101/128:ℝ) (51/64:ℝ) (145153/200000000000:ℝ) (573291/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_404).2 (thetaFirstMode_node_408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_102 :
    (4007672369/1572864000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (51/64:ℝ) (103/128:ℝ) (12922995/16137728:ℝ) (127151/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_410).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_102 :
    (∫ x in (51/64:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x) ≤ (4303552893/1677721600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (51/64:ℝ) (103/128:ℝ) (573291/1000000000000:ℝ) (56393/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_408).2 (thetaFirstMode_node_412).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_103 :
    (2139649323/1048576000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (103/128:ℝ) (13/16:ℝ) (13304925/16454144:ℝ) (199737/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_414).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_103 :
    (∫ x in (103/128:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x) ≤ (17235995517/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (103/128:ℝ) (13/16:ℝ) (56393/125000000000:ℝ) (353663/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_412).2 (thetaFirstMode_node_416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_104 :
    (204789011/125829120000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/16:ℝ) (105/128:ℝ) (13694307/16773632:ℝ) (6251/20000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_418).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_104 :
    (∫ x in (13/16:ℝ)..(105/128:ℝ), x^2*thetaFirstMode x) ≤ (10312881149/6291456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/16:ℝ) (105/128:ℝ) (353663/1000000000000:ℝ) (276167/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_416).2 (thetaFirstMode_node_420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_105 :
    (1355574427/1048576000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (105/128:ℝ) (53/64:ℝ) (14091213/17096192:ℝ) (121791/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_422).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_105 :
    (∫ x in (105/128:ℝ)..(53/64:ℝ), x^2*thetaFirstMode x) ≤ (131099507/100663296000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (105/128:ℝ) (53/64:ℝ) (276167/1000000000000:ℝ) (214801/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_420).2 (thetaFirstMode_node_424).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_106 :
    (6433723079/6291456000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (53/64:ℝ) (107/128:ℝ) (14495715/17421824:ℝ) (189077/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_426).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_106 :
    (∫ x in (53/64:ℝ)..(107/128:ℝ), x^2*thetaFirstMode x) ≤ (6483002927/6291456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (53/64:ℝ) (107/128:ℝ) (214801/1000000000000:ℝ) (166401/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_424).2 (thetaFirstMode_node_428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_107 :
    (67569881/83886080000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (107/128:ℝ) (27/32:ℝ) (14907885/17750528:ℝ) (5847/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_430).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_107 :
    (∫ x in (107/128:ℝ)..(27/32:ℝ), x^2*thetaFirstMode x) ≤ (1276963751/1572864000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (107/128:ℝ) (27/32:ℝ) (166401/1000000000000:ℝ) (128381/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_428).2 (thetaFirstMode_node_432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_108 :
    (3974681131/6291456000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/32:ℝ) (109/128:ℝ) (15327795/18082304:ℝ) (112543/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_434).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_108 :
    (∫ x in (27/32:ℝ)..(109/128:ℝ), x^2*thetaFirstMode x) ≤ (8014438333/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/32:ℝ) (109/128:ℝ) (128381/1000000000000:ℝ) (98639/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_432).2 (thetaFirstMode_node_436).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_109 :
    (193991603/393216000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (109/128:ℝ) (55/64:ℝ) (15755517/18417152:ℝ) (5393/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_438).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_109 :
    (∫ x in (109/128:ℝ)..(55/64:ℝ), x^2*thetaFirstMode x) ≤ (2504106269/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (109/128:ℝ) (55/64:ℝ) (98639/1000000000000:ℝ) (18867/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_436).2 (thetaFirstMode_node_440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_110 :
    (1206588509/3145728000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (55/64:ℝ) (111/128:ℝ) (16191123/18755072:ℝ) (32939/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_442).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_110 :
    (∫ x in (55/64:ℝ)..(111/128:ℝ), x^2*thetaFirstMode x) ≤ (973708979/2516582400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (55/64:ℝ) (111/128:ℝ) (18867/250000000000:ℝ) (28747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_440).2 (thetaFirstMode_node_444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_111 :
    (622598821/2097152000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (111/128:ℝ) (7/8:ℝ) (16634685/19096064:ℝ) (50079/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_446).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_111 :
    (∫ x in (111/128:ℝ)..(7/8:ℝ), x^2*thetaFirstMode x) ≤ (7538730461/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (111/128:ℝ) (7/8:ℝ) (28747/500000000000:ℝ) (43611/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_444).2 (thetaFirstMode_node_448).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_112 :
    (1439139007/6291456000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/8:ℝ) (113/128:ℝ) (17086275/19440128:ℝ) (37903/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_450).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_112 :
    (∫ x in (7/8:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x) ≤ (363146753/1572864000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/8:ℝ) (113/128:ℝ) (43611/1000000000000:ℝ) (6587/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_448).2 (thetaFirstMode_node_452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_113 :
    (4598993/26214400000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (113/128:ℝ) (57/64:ℝ) (17545965/19787264:ℝ) (357/12500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_454).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_113 :
    (∫ x in (113/128:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x) ≤ (2228849563/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (113/128:ℝ) (57/64:ℝ) (6587/200000000000:ℝ) (24761/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_452).2 (thetaFirstMode_node_456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_114 :
    (280862671/2097152000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (57/64:ℝ) (115/128:ℝ) (18013827/20137472:ℝ) (21423/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_458).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_114 :
    (∫ x in (57/64:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x) ≤ (1702004317/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (57/64:ℝ) (115/128:ℝ) (24761/1000000000000:ℝ) (18531/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_456).2 (thetaFirstMode_node_460).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_115 :
    (128027179/1258291200000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (115/128:ℝ) (29/32:ℝ) (18489933/20490752:ℝ) (3199/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_462).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_115 :
    (∫ x in (115/128:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x) ≤ (2587066133/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (115/128:ℝ) (29/32:ℝ) (18531/1000000000000:ℝ) (3451/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_460).2 (thetaFirstMode_node_464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_116 :
    (30252731/393216000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/32:ℝ) (117/128:ℝ) (18974355/20847104:ℝ) (743/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_466).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_116 :
    (∫ x in (29/32:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x) ≤ (1956760349/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/32:ℝ) (117/128:ℝ) (3451/250000000000:ℝ) (2047/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_464).2 (thetaFirstMode_node_468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_117 :
    (121399089/2097152000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (117/128:ℝ) (59/64:ℝ) (19467165/21206528:ℝ) (8793/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_470).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_117 :
    (∫ x in (117/128:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x) ≤ (736446037/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (117/128:ℝ) (59/64:ℝ) (2047/200000000000:ℝ) (7553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_468).2 (thetaFirstMode_node_472).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_118 :
    (272688071/6291456000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (59/64:ℝ) (119/128:ℝ) (19968435/21569024:ℝ) (6473/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_474).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_118 :
    (∫ x in (59/64:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x) ≤ (551625989/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (59/64:ℝ) (119/128:ℝ) (7553/1000000000000:ℝ) (5547/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_472).2 (thetaFirstMode_node_476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_119 :
    (203109181/6291456000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (119/128:ℝ) (15/16:ℝ) (20478237/21934592:ℝ) (4741/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_478).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_119 :
    (∫ x in (119/128:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x) ≤ (137031689/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (119/128:ℝ) (15/16:ℝ) (5547/1000000000000:ℝ) (4053/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_476).2 (thetaFirstMode_node_480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_120 :
    (392049/16384000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/16:ℝ) (121/128:ℝ) (20996643/22303232:ℝ) (27/7812500000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_482).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_120 :
    (∫ x in (15/16:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x) ≤ (101597909/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/16:ℝ) (121/128:ℝ) (4053/1000000000000:ℝ) (2947/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_480).2 (thetaFirstMode_node_484).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_121 :
    (55491611/3145728000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (121/128:ℝ) (61/64:ℝ) (21523725/22674944:ℝ) (1253/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_486).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_121 :
    (∫ x in (121/128:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x) ≤ (149889767/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (121/128:ℝ) (61/64:ℝ) (2947/1000000000000:ℝ) (533/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_484).2 (thetaFirstMode_node_488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_122 :
    (5087147/393216000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (61/64:ℝ) (123/128:ℝ) (22059555/23049728:ℝ) (113/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_490).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_122 :
    (∫ x in (61/64:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x) ≤ (330023081/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (61/64:ℝ) (123/128:ℝ) (533/250000000000:ℝ) (307/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_488).2 (thetaFirstMode_node_492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_123 :
    (29696293/3145728000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (123/128:ℝ) (31/32:ℝ) (22604205/23427584:ℝ) (649/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_494).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_123 :
    (∫ x in (123/128:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x) ≤ (30117523/3145728000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (123/128:ℝ) (31/32:ℝ) (307/200000000000:ℝ) (1099/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_492).2 (thetaFirstMode_node_496).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_124 :
    (14368809/2097152000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/32:ℝ) (125/128:ℝ) (23157747/23808512:ℝ) (927/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_498).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_124 :
    (∫ x in (31/32:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x) ≤ (4373777/629145600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/32:ℝ) (125/128:ℝ) (1099/1000000000000:ℝ) (783/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_496).2 (thetaFirstMode_node_500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_125 :
    (15545579/3145728000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (125/128:ℝ) (63/64:ℝ) (23720253/24192512:ℝ) (329/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_502).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_125 :
    (∫ x in (125/128:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x) ≤ (25258339/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (125/128:ℝ) (63/64:ℝ) (783/1000000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_500).2 (thetaFirstMode_node_504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_126 :
    (1488217/419430400000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (63/64:ℝ) (127/128:ℝ) (24291795/24579584:ℝ) (93/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_506).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_126 :
    (∫ x in (63/64:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x) ≤ (90691991/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (63/64:ℝ) (127/128:ℝ) (277/500000000000:ℝ) (391/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_504).2 (thetaFirstMode_node_508).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_127 :
    (7949347/3145728000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (127/128:ℝ) (1/1:ℝ) (24872445/24969728:ℝ) (163/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_510).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_127 :
    (∫ x in (127/128:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x) ≤ (12966587/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (127/128:ℝ) (1/1:ℝ) (391/1000000000000:ℝ) (137/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_508).2 (thetaFirstMode_node_512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
