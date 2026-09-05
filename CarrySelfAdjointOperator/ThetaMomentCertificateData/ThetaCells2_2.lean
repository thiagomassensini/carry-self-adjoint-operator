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

theorem thetaFirstMode_cell_lower_2_064 :
    (5870926943707/6291456000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(65/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/2:ℝ) (65/128:ℝ) (3220227/6390272:ℝ) (470389147/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_258).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_064 :
    (∫ x in (1/2:ℝ)..(65/128:ℝ), x^2*thetaFirstMode x) ≤ (11763834360811/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/2:ℝ) (65/128:ℝ) (7846301/15625000000:ℝ) (44069381/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_256).2 (thetaFirstMode_node_260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_065 :
    (442305312177/524288000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(33/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (65/128:ℝ) (33/64:ℝ) (3372333/6589952:ℝ) (103093461/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_262).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_065 :
    (∫ x in (65/128:ℝ)..(33/64:ℝ), x^2*thetaFirstMode x) ≤ (531794796011/629145600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (65/128:ℝ) (33/64:ℝ) (44069381/100000000000:ℝ) (38593061/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_260).2 (thetaFirstMode_node_264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_066 :
    (398831479373/524288000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(67/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (33/64:ℝ) (67/128:ℝ) (3529155/6792704:ℝ) (90185757/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_266).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_066 :
    (∫ x in (33/64:ℝ)..(67/128:ℝ), x^2*thetaFirstMode x) ≤ (19182302956733/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (33/64:ℝ) (67/128:ℝ) (38593061/100000000000:ℝ) (337246369/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_264).2 (thetaFirstMode_node_268).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_067 :
    (4304274344329/6291456000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(17/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (67/128:ℝ) (17/32:ℝ) (3690765/6998528:ℝ) (314893141/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_270).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_067 :
    (∫ x in (67/128:ℝ)..(17/32:ℝ), x^2*thetaFirstMode x) ≤ (8626415895059/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (67/128:ℝ) (17/32:ℝ) (337246369/1000000000000:ℝ) (294060307/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_268).2 (thetaFirstMode_node_272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_068 :
    (3860843171773/6291456000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(69/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/32:ℝ) (69/128:ℝ) (3857235/7207424:ℝ) (274266049/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_274).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_068 :
    (∫ x in (17/32:ℝ)..(69/128:ℝ), x^2*thetaFirstMode x) ≤ (3778453093/6144000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/32:ℝ) (69/128:ℝ) (294060307/1000000000000:ℝ) (255835999/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_272).2 (thetaFirstMode_node_276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_069 :
    (1151294777923/2097152000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(35/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (69/128:ℝ) (35/64:ℝ) (4028637/7419392:ℝ) (238346859/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_278).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_069 :
    (∫ x in (69/128:ℝ)..(35/64:ℝ), x^2*thetaFirstMode x) ≤ (13846245578179/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (69/128:ℝ) (35/64:ℝ) (255835999/1000000000000:ℝ) (111039591/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_276).2 (thetaFirstMode_node_280).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_070 :
    (513588832731/1048576000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(71/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (35/64:ℝ) (71/128:ℝ) (4205043/7634432:ℝ) (103330863/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_282).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_070 :
    (∫ x in (35/64:ℝ)..(71/128:ℝ), x^2*thetaFirstMode x) ≤ (4118160791827/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (35/64:ℝ) (71/128:ℝ) (111039591/500000000000:ℝ) (192335553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_280).2 (thetaFirstMode_node_284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_071 :
    (228490181227/524288000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(9/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (71/128:ℝ) (9/16:ℝ) (4386525/7852544:ℝ) (44693913/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_286).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_071 :
    (∫ x in (71/128:ℝ)..(9/16:ℝ), x^2*thetaFirstMode x) ≤ (10993630053601/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (71/128:ℝ) (9/16:ℝ) (192335553/1000000000000:ℝ) (83094287/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_284).2 (thetaFirstMode_node_288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_072 :
    (2433003630317/6291456000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(73/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/16:ℝ) (73/128:ℝ) (4573155/8073728:ℝ) (154290293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_290).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_072 :
    (∫ x in (9/16:ℝ)..(73/128:ℝ), x^2*thetaFirstMode x) ≤ (9755978400871/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/16:ℝ) (73/128:ℝ) (83094287/500000000000:ℝ) (143257283/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_288).2 (thetaFirstMode_node_292).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_073 :
    (717655635579/2097152000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(37/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (73/128:ℝ) (37/64:ℝ) (4765005/8297984:ℝ) (132841791/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_294).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_073 :
    (∫ x in (73/128:ℝ)..(37/64:ℝ), x^2*thetaFirstMode x) ≤ (1726761454669/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (73/128:ℝ) (37/64:ℝ) (143257283/1000000000000:ℝ) (3849817/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_292).2 (thetaFirstMode_node_296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_074 :
    (1899856338083/6291456000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(75/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (37/64:ℝ) (75/128:ℝ) (4962147/8525312:ℝ) (114098633/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_298).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_074 :
    (∫ x in (37/64:ℝ)..(75/128:ℝ), x^2*thetaFirstMode x) ≤ (317477283873/1048576000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (37/64:ℝ) (75/128:ℝ) (3849817/31250000000:ℝ) (2642073/25000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_296).2 (thetaFirstMode_node_300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_075 :
    (417946541789/1572864000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(19/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (75/128:ℝ) (19/32:ℝ) (5164653/8755712:ℝ) (24439889/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_302).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_075 :
    (∫ x in (75/128:ℝ)..(19/32:ℝ), x^2*thetaFirstMode x) ≤ (279390745981/1048576000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (75/128:ℝ) (19/32:ℝ) (2642073/25000000000:ℝ) (88317/976562500:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_300).2 (thetaFirstMode_node_304).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_076 :
    (1466913703057/6291456000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(77/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/32:ℝ) (77/128:ℝ) (5372595/8989184:ℝ) (83551501/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_306).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_076 :
    (∫ x in (19/32:ℝ)..(77/128:ℝ), x^2*thetaFirstMode x) ≤ (5884205023627/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/32:ℝ) (77/128:ℝ) (88317/976562500:ℝ) (77195417/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_304).2 (thetaFirstMode_node_308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_077 :
    (427816882317/2097152000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(39/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (77/128:ℝ) (39/64:ℝ) (5586045/9225728:ℝ) (71227629/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_310).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_077 :
    (∫ x in (77/128:ℝ)..(39/64:ℝ), x^2*thetaFirstMode x) ≤ (2574390616367/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (77/128:ℝ) (39/64:ℝ) (77195417/1000000000000:ℝ) (65724811/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_308).2 (thetaFirstMode_node_312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_078 :
    (1119672531313/6291456000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(79/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (39/64:ℝ) (79/128:ℝ) (5805075/9465344:ℝ) (60565399/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_314).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_078 :
    (∫ x in (39/64:ℝ)..(79/128:ℝ), x^2*thetaFirstMode x) ≤ (4492206410641/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (39/64:ℝ) (79/128:ℝ) (65724811/1000000000000:ℝ) (27906817/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_312).2 (thetaFirstMode_node_316).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_079 :
    (12174080699/78643200000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(5/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (79/128:ℝ) (5/8:ℝ) (6029757/9708032:ℝ) (642059/12500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_318).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_079 :
    (∫ x in (79/128:ℝ)..(5/8:ℝ), x^2*thetaFirstMode x) ≤ (130262208669/838860800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (79/128:ℝ) (5/8:ℝ) (27906817/500000000000:ℝ) (1477259/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_316).2 (thetaFirstMode_node_320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_080 :
    (281545747901/2097152000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/8:ℝ) (81/128:ℝ) (6260163/9953792:ℝ) (43446183/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_322).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_080 :
    (∫ x in (5/8:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x) ≤ (677891329607/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/8:ℝ) (81/128:ℝ) (1477259/31250000000:ℝ) (39931009/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_320).2 (thetaFirstMode_node_324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_081 :
    (182578008961/1572864000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (81/128:ℝ) (41/64:ℝ) (6496365/10202624:ℝ) (9162343/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_326).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_081 :
    (∫ x in (81/128:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x) ≤ (117240089917/1006632960000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (81/128:ℝ) (41/64:ℝ) (39931009/1000000000000:ℝ) (16819109/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_324).2 (thetaFirstMode_node_328).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_082 :
    (41969559723/419430400000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (41/64:ℝ) (83/128:ℝ) (6738435/10454528:ℝ) (6166251/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_330).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_082 :
    (∫ x in (41/64:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x) ≤ (1263434606791/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (41/64:ℝ) (83/128:ℝ) (16819109/500000000000:ℝ) (7064739/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_328).2 (thetaFirstMode_node_332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_083 :
    (36067413187/419430400000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (83/128:ℝ) (21/32:ℝ) (6986445/10709504:ℝ) (5172933/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_334).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_083 :
    (∫ x in (83/128:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x) ≤ (2171772771061/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (83/128:ℝ) (21/32:ℝ) (7064739/250000000000:ℝ) (23673409/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_332).2 (thetaFirstMode_node_336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_084 :
    (154494485511/2097152000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/32:ℝ) (85/128:ℝ) (7240467/10967552:ℝ) (21636873/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_338).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_084 :
    (∫ x in (21/32:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x) ≤ (232597517993/3145728000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/32:ℝ) (85/128:ℝ) (23673409/1000000000000:ℝ) (19775517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_336).2 (thetaFirstMode_node_340).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_085 :
    (79163168357/1258291200000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (85/128:ℝ) (43/64:ℝ) (7500573/11228672:ℝ) (3609647/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_342).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_085 :
    (∫ x in (85/128:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x) ≤ (794654689261/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (85/128:ℝ) (43/64:ℝ) (19775517/1000000000000:ℝ) (658867/40000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_340).2 (thetaFirstMode_node_344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_086 :
    (877475677/16384000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (43/64:ℝ) (87/128:ℝ) (7766835/11492864:ℝ) (117273/7812500000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_346).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_086 :
    (∫ x in (43/64:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x) ≤ (225520761719/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (43/64:ℝ) (87/128:ℝ) (658867/40000000000:ℝ) (13679517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_344).2 (thetaFirstMode_node_348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_087 :
    (35739327589/786432000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (87/128:ℝ) (11/16:ℝ) (8039325/11760128:ℝ) (1555981/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_350).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_087 :
    (∫ x in (87/128:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x) ≤ (382775939763/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (87/128:ℝ) (11/16:ℝ) (13679517/1000000000000:ℝ) (5663393/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_348).2 (thetaFirstMode_node_352).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_088 :
    (241816391381/6291456000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/16:ℝ) (89/128:ℝ) (8318115/12030464:ℝ) (10291373/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_354).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_088 :
    (∫ x in (11/16:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x) ≤ (194269762253/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/16:ℝ) (89/128:ℝ) (5663393/500000000000:ℝ) (9350293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_352).2 (thetaFirstMode_node_356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_089 :
    (203843269903/6291456000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (89/128:ℝ) (45/64:ℝ) (8603277/12303872:ℝ) (8482513/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_358).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_089 :
    (∫ x in (89/128:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x) ≤ (818931873223/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (89/128:ℝ) (45/64:ℝ) (9350293/1000000000000:ℝ) (240467/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_356).2 (thetaFirstMode_node_360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_090 :
    (42814402367/1572864000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (45/64:ℝ) (91/128:ℝ) (8894883/12580352:ℝ) (1742477/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_362).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_090 :
    (∫ x in (45/64:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x) ≤ (688121593579/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (45/64:ℝ) (91/128:ℝ) (240467/31250000000:ℝ) (1262573/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_360).2 (thetaFirstMode_node_364).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_091 :
    (23898800383/1048576000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (91/128:ℝ) (23/32:ℝ) (9193005/12859904:ℝ) (2854497/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_366).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_091 :
    (∫ x in (91/128:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x) ≤ (23049880079/1006632960000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (91/128:ℝ) (23/32:ℝ) (1262573/200000000000:ℝ) (258129/50000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_364).2 (thetaFirstMode_node_368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_092 :
    (11964911287/629145600000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/32:ℝ) (93/128:ℝ) (9497715/13142528:ℝ) (466123/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_370).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_092 :
    (∫ x in (23/32:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x) ≤ (480904716703/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/32:ℝ) (93/128:ℝ) (258129/50000000000:ℝ) (4208281/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_368).2 (thetaFirstMode_node_372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_093 :
    (6632624711/419430400000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (93/128:ℝ) (47/64:ℝ) (9809085/13428224:ℝ) (758679/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_374).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_093 :
    (∫ x in (93/128:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x) ≤ (12498176423/786432000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (93/128:ℝ) (47/64:ℝ) (4208281/1000000000000:ℝ) (3419149/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_372).2 (thetaFirstMode_node_376).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_094 :
    (41217230143/3145728000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (47/64:ℝ) (95/128:ℝ) (10127187/13716992:ℝ) (1538473/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_378).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_094 :
    (∫ x in (47/64:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x) ≤ (165718673831/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (47/64:ℝ) (95/128:ℝ) (3419149/1000000000000:ℝ) (553751/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_376).2 (thetaFirstMode_node_380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_095 :
    (13611796529/1258291200000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (95/128:ℝ) (3/4:ℝ) (10452093/14008832:ℝ) (497489/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_382).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_095 :
    (∫ x in (95/128:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x) ≤ (273686297057/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (95/128:ℝ) (3/4:ℝ) (553751/200000000000:ℝ) (279313/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_380).2 (thetaFirstMode_node_384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
