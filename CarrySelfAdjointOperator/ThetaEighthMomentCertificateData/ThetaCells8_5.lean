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

theorem thetaFirstMode_refined_cell_lower_8_160 :
    (1122538547628527211503622793/265633114661417543270400000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/8:ℝ) (161/256:ℝ) (6361630132651141262409/10146636573905784424960:ℝ) (283216873/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0965).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^8*thetaFirstMode x) ≤ (59916781812260298457020091297/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/8:ℝ) (161/256:ℝ) (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_161 :
    (240946165353322053271133487/59029581035870565171200000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (161/256:ℝ) (81/128:ℝ) (6727368238177514567607/10663543358416903452160:ℝ) (520596153/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0971).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^8*thetaFirstMode x) ≤ (43405715060030152270606939987/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (161/256:ℝ) (81/128:ℝ) (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_162 :
    (16740039998033787923245179961/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (81/128:ℝ) (163/256:ℝ) (1422335766498956948925/2240669318036578698752:ℝ) (3825151891/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0977).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^8*thetaFirstMode x) ≤ (16753937166185409230828439247/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (81/128:ℝ) (163/256:ℝ) (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_163 :
    (8068680266591914989309790747/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (163/256:ℝ) (41/64:ℝ) (7515381976057835704143/11766910146346930332160:ℝ) (1755415927/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0983).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^8*thetaFirstMode x) ≤ (80754920691187342026349271557/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (163/256:ℝ) (41/64:ℝ) (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_164 :
    (15541031007745133345333054479/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (41/64:ℝ) (165/256:ℝ) (7939328572536936611841/12355124896752488296960:ℝ) (3220124419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0989).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^8*thetaFirstMode x) ≤ (77771865592867980949128743959/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (41/64:ℝ) (165/256:ℝ) (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_165 :
    (7475972637792734203518916139/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (165/256:ℝ) (83/128:ℝ) (8384401329530932495359/12968909374505557020160:ℝ) (1475720849/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0995).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^8*thetaFirstMode x) ≤ (74824993302763490923822121353/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (165/256:ℝ) (83/128:ℝ) (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_166 :
    (7185472098984132875184073237/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (83/128:ℝ) (167/256:ℝ) (8851515743072711040057/13609210458953895708160:ℝ) (1351644067/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1001).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^8*thetaFirstMode x) ≤ (143837023316006239780989824623/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (83/128:ℝ) (167/256:ℝ) (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_167 :
    (13798814575168345129210063723/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (167/256:ℝ) (21/32:ℝ) (1868324221273231476315/2855400814247135293952:ℝ) (2474256163/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1007).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^8*thetaFirstMode x) ≤ (1381127164192918221293190473/425012983458268069232640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (167/256:ℝ) (21/32:ℝ) (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_168 :
    (3309072087343888749928350983/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (21/32:ℝ) (169/256:ℝ) (9855701543199181141593/14973295882550797212160:ℝ) (565755503/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1013).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^8*thetaFirstMode x) ≤ (26496878476423079239710872137/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (21/32:ℝ) (169/256:ℝ) (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_169 :
    (99094078648310335977332449/33204139332677192908800000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (169/256:ℝ) (85/128:ℝ) (10394777066482805050791/15699122035309073589760:ℝ) (16158919/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1019).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^8*thetaFirstMode x) ≤ (21159803956067218788821865437/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (169/256:ℝ) (85/128:ℝ) (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_170 :
    (12142696612442050421738758939/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (85/128:ℝ) (171/256:ℝ) (10959904662371742259809/16455549877310448463360:ℝ) (1889046769/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1025).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^8*thetaFirstMode x) ≤ (4861689059594216043755631353/1700051933833072276930560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (85/128:ℝ) (171/256:ℝ) (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_171 :
    (3870939071418593216512067251/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (171/256:ℝ) (43/64:ℝ) (11552179400427359855007/17243678709113286300160:ℝ) (1724041173/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1031).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^8*thetaFirstMode x) ≤ (11624025981545839934331094841/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (171/256:ℝ) (43/64:ℝ) (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_172 :
    (2218982731279969997776844927/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (43/64:ℝ) (173/256:ℝ) (2434547114057885834205/3612928108949549783552:ℝ) (314459387/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1037).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^8*thetaFirstMode x) ≤ (1388225355416535791371370771/531266229322835086540800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (43/64:ℝ) (173/256:ℝ) (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_173 :
    (2117888155220529382622873123/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (173/256:ℝ) (87/128:ℝ) (12822747845328599226543/18919600885932177948160:ℝ) (286570193/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1043).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^8*thetaFirstMode x) ≤ (17666681237666842656305425921/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (173/256:ℝ) (87/128:ℝ) (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_174 :
    (3365599698735985367003041513/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (87/128:ℝ) (175/256:ℝ) (13503432473757098003241/19809759509951338370560:ℝ) (1304801589/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1049).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^8*thetaFirstMode x) ≤ (4211268704084294617769815703/1770887431076116955136000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (87/128:ℝ) (175/256:ℝ) (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_175 :
    (200361162794577439231379927/88544371553805847756800000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (175/256:ℝ) (11/16:ℝ) (14216048497680767340759/20736351271356306434560:ℝ) (74206581/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1055).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^8*thetaFirstMode x) ≤ (3008518469176946704842458891/1328165573307087716352000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (175/256:ℝ) (11/16:ℝ) (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_176 :
    (9151345794181389422359988707/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (11/16:ℝ) (177/256:ℝ) (14961899000581170932457/21700646917646714268160:ℝ) (1079573587/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1061).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^8*thetaFirstMode x) ≤ (45804734488176108136901294737/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (11/16:ℝ) (177/256:ℝ) (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_177 :
    (1087384117955555318071183237/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (177/256:ℝ) (89/128:ℝ) (3148466476744436255595/4540790783819398487552:ℝ) (122608747/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1067).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^8*thetaFirstMode x) ≤ (348334111119340278541968413/170005193383307227693056000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (177/256:ℝ) (89/128:ℝ) (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_178 :
    (8260711585538053022051244623/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (89/128:ℝ) (179/256:ℝ) (16558743671981150478993/23747617312889180700160:ℝ) (890507093/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1073).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^8*thetaFirstMode x) ≤ (6891393062894212920302486731/3541774862152233910272000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (89/128:ℝ) (179/256:ℝ) (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_179 :
    (217678003204743717671449129/118059162071741130342400000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (179/256:ℝ) (45/64:ℝ) (17412575849610501454191/24833020561715806159360:ℝ) (201960981/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1079).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^8*thetaFirstMode x) ≤ (26150168470909089638946511819/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (179/256:ℝ) (45/64:ℝ) (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_180 :
    (185656567845598694732112659/106253245864567017308160000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (45/64:ℝ) (181/256:ℝ) (18305321226441340498209/25961586427017257013760:ℝ) (18307079/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1085).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^8*thetaFirstMode x) ≤ (1548872936628844457737896571/885443715538058477568000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (45/64:ℝ) (181/256:ℝ) (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_181 :
    (878791399275477595538577613/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (181/256:ℝ) (91/128:ℝ) (19238522835046489117407/27134777857019009052160:ℝ) (82908583/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1091).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^8*thetaFirstMode x) ≤ (70383466839274791932661159407/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (181/256:ℝ) (91/128:ℝ) (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_182 :
    (6648627015629072787192152647/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (91/128:ℝ) (183/256:ℝ) (4042755171877232548485/5670819777946998205952:ℝ) (600283057/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1097).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^8*thetaFirstMode x) ≤ (6656334253917927832082493389/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (91/128:ℝ) (183/256:ℝ) (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_183 :
    (196285103890418810189484359/132816557330708771635200000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (183/256:ℝ) (23/32:ℝ) (21232729095465386243943/29621095571104304028160:ℝ) (16963919/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1103).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^8*thetaFirstMode x) ≤ (491291125967770785481294141/332041393326771929088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (183/256:ℝ) (23/32:ℝ) (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_184 :
    (1975918360796798561442428171/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (23/32:ℝ) (185/256:ℝ) (22297086444538131163641/30937356888429438876160:ℝ) (490509033/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1109).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^8*thetaFirstMode x) ≤ (6594287294189459778646950513/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (23/32:ℝ) (185/256:ℝ) (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_185 :
    (1397105329878048344796034741/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (185/256:ℝ) (93/128:ℝ) (23408608439399087217159/32304515719285064680960:ℝ) (110714851/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1115).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^8*thetaFirstMode x) ≤ (11190460279038474168361822757/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (185/256:ℝ) (93/128:ℝ) (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_186 :
    (584776370524661220333324229/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (93/128:ℝ) (187/256:ℝ) (24569113804309940929857/33724249796067390492160:ℝ) (399512151/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1121).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^8*thetaFirstMode x) ≤ (26347534053433937285053215023/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (93/128:ℝ) (187/256:ℝ) (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_187 :
    (8595984354504047247891053/7378697629483820646400000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (187/256:ℝ) (47/64:ℝ) (5156096209822605445875/7039656537271006218752:ℝ) (5626737/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1127).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^8*thetaFirstMode x) ≤ (495752280594317351931765167/425012983458268069232640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (187/256:ℝ) (47/64:ℝ) (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_188 :
    (2326562533003535726061418349/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (47/64:ℝ) (189/256:ℝ) (27044650098091245441393/36728384789253236892160:ℝ) (162163409/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1133).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^8*thetaFirstMode x) ≤ (11647708025857004405175694223/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (47/64:ℝ) (189/256:ℝ) (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_189 :
    (2184139770540125294076366901/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (189/256:ℝ) (95/128:ℝ) (28363623954139189416591/38316374347894276840960:ℝ) (145927111/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1139).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^8*thetaFirstMode x) ≤ (5467457847676975358908227973/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (189/256:ℝ) (95/128:ℝ) (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_190 :
    (455167096831625346265913039/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (95/128:ℝ) (191/256:ℝ) (29739470398816532457609/39964118478267692316160:ℝ) (262411641/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1145).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^8*thetaFirstMode x) ≤ (1139423821097461017217048831/1180591620717411303424000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (95/128:ℝ) (191/256:ℝ) (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_191 :
    (3837529358146387667255117189/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (191/256:ℝ) (3/4:ℝ) (31174323728860831314807/41673534214555068828160:ℝ) (235738949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1151).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^8*thetaFirstMode x) ≤ (38426931577014180426043799819/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (191/256:ℝ) (3/4:ℝ) (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
