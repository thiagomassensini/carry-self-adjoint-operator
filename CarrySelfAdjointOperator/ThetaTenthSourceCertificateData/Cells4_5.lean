import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature5

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_160 :
    (27361104910885621/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (5/8:ℝ) (161/256:ℝ)
    (1065097174935/1698824602112:ℝ) (2266130489/50000000000000:ℝ) (4513506200394323/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_160
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0963).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^4*thetaFirstMode x) ≤ (1368113939339909/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (5/8:ℝ) (161/256:ℝ)
    (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_160 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_161 :
    (12889833052109783/500000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (161/256:ℝ) (81/128:ℝ)
    (3296080149115/5224679471616:ℝ) (52068719/1250000000000:ℝ) (16869263981906327/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_161
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0969).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x) ≤ (12890398369947641/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (161/256:ℝ) (81/128:ℝ)
    (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_161 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_162 :
    (12134734706575111/500000000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (81/128:ℝ) (163/256:ℝ)
    (3399396216125/5355288900096:ℝ) (59778469/1562500000000:ℝ) (15751367210440041/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_162
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0975).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^4*thetaFirstMode x) ≤ (24270557520391421/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (81/128:ℝ) (163/256:ℝ)
    (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_162 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_163 :
    (11414348490307127/500000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (163/256:ℝ) (41/64:ℝ)
    (1168428988545/1829443983872:ℝ) (3511448057/100000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_163
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0981).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x) ≤ (22829743300710483/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (163/256:ℝ) (41/64:ℝ)
    (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_163 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_164 :
    (10727741391576953/500000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (41/64:ℝ) (165/256:ℝ)
    (3613800222445/5623838670336:ℝ) (3220690669/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_164
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0987).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^4*thetaFirstMode x) ≤ (4291297618797211/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (41/64:ℝ) (165/256:ℝ)
    (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_164 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_165 :
    (2518490074789307/125000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (165/256:ℝ) (83/128:ℝ)
    (3724984399955/5761839284736:ℝ) (2951961703/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_165
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0993).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x) ≤ (10074442851835511/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (165/256:ℝ) (83/128:ℝ)
    (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_165 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_166 :
    (1181504475880149/62500000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (83/128:ℝ) (167/256:ℝ)
    (1279629501255/1967454735872:ℝ) (2703765353/100000000000000:ℝ) (5944719025535047/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_166
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0999).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^4*thetaFirstMode x) ≤ (18904997361480503/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (83/128:ℝ) (167/256:ℝ)
    (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (5944719025535047/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_166 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_167 :
    (17721971811757583/1000000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (167/256:ℝ) (21/32:ℝ)
    (3955562135275/6045444036096:ℝ) (38667091/1562500000000:ℝ) (5531197575076283/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_167
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1005).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x) ≤ (553839345764561/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (167/256:ℝ) (21/32:ℝ)
    (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_167 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_168 :
    (8299819463947103/500000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (21/32:ℝ) (169/256:ℝ)
    (4075055495285/6191109551616:ℝ) (2263423123/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_168
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1011).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^4*thetaFirstMode x) ≤ (4150122143024703/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (21/32:ℝ) (169/256:ℝ)
    (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_168 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_169 :
    (15535079136127693/1000000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (169/256:ℝ) (85/128:ℝ)
    (1399139795865/2113130573312:ℝ) (413741799/20000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_169
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1017).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x) ≤ (15535892076458433/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (169/256:ℝ) (85/128:ℝ)
    (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_169 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_170 :
    (14526293363136017/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (85/128:ℝ) (171/256:ℝ)
    (4322705222605/6490321691136:ℝ) (118086437/6250000000000:ℝ) (2217991790435067/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_170
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1023).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^4*thetaFirstMode x) ≤ (3631767634765327/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (85/128:ℝ) (171/256:ℝ)
    (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ) (2217991790435067/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_170 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_171 :
    (6785641645234077/500000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (171/256:ℝ) (43/64:ℝ)
    (4450965020915/6643930799616:ℝ) (862174341/50000000000000:ℝ) (65845773848071/8000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_171
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1029).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x) ≤ (2714405129189283/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (171/256:ℝ) (43/64:ℝ)
    (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ) (65845773848071/8000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_171 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_172 :
    (1583507120515889/125000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (43/64:ℝ) (173/256:ℝ)
    (1527417138975/2266750188032:ℝ) (1572577987/100000000000000:ℝ) (7630138077098641/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_172
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1035).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^4*thetaFirstMode x) ≤ (6334382720179533/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (43/64:ℝ) (173/256:ℝ)
    (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ) (7630138077098641/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_172 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_173 :
    (11814634038280629/1000000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (173/256:ℝ) (87/128:ℝ)
    (4716617662435/6959312687616:ℝ) (1433107653/100000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_173
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1041).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x) ≤ (2363061921884897/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (173/256:ℝ) (87/128:ℝ)
    (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_173 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_174 :
    (11009050731277391/1000000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (87/128:ℝ) (175/256:ℝ)
    (4854117630245/7121149057536:ℝ) (65251793/5000000000000:ℝ) (1308491592392887/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_174
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1047).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^4*thetaFirstMode x) ≤ (11009694371050619/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (87/128:ℝ) (175/256:ℝ)
    (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ) (1308491592392887/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_174 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_175 :
    (10249364357191289/1000000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (175/256:ℝ) (11/16:ℝ)
    (1664935272585/2428597248512:ℝ) (1187518953/100000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_175
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1053).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x) ≤ (2049995407790661/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (175/256:ℝ) (11/16:ℝ)
    (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_175 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_176 :
    (9533657528681073/1000000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (11/16:ℝ) (177/256:ℝ)
    (5138737350565/7453273007616:ℝ) (67485519/6250000000000:ℝ) (1118550559120073/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_176
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1059).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^4*thetaFirstMode x) ≤ (9534240232515533/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (11/16:ℝ) (177/256:ℝ)
    (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ) (1118550559120073/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_176 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_177 :
    (443002101094841/50000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (177/256:ℝ) (89/128:ℝ)
    (5285967986075/7623625284096:ℝ) (981047301/100000000000000:ℝ) (516493902482609/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_177
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1065).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x) ≤ (1772119146393969/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (177/256:ℝ) (89/128:ℝ)
    (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_177 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_178 :
    (65813298499729/8000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (89/128:ℝ) (179/256:ℝ)
    (1812184705695/2598960399872:ℝ) (445334231/50000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_178
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1071).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^4*thetaFirstMode x) ≤ (2056797000732101/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (89/128:ℝ) (179/256:ℝ)
    (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_178 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_179 :
    (305267948394337/40000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (179/256:ℝ) (45/64:ℝ)
    (5590552775395/7973073563136:ℝ) (807990663/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_179
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1077).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x) ≤ (7632197360311137/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (179/256:ℝ) (45/64:ℝ)
    (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_179 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_180 :
    (442085640405589/62500000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (45/64:ℝ) (181/256:ℝ)
    (5748021635405/8152235367936:ℝ) (366208247/50000000000000:ℝ) (1012236611442963/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_180
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1083).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^4*thetaFirstMode x) ≤ (7073842833204631/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (45/64:ℝ) (181/256:ℝ)
    (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_180 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_181 :
    (6549937221820919/1000000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (181/256:ℝ) (91/128:ℝ)
    (1969673005905/2778133263872:ℝ) (20730929/3125000000000:ℝ) (465931073813781/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_181
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1089).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x) ≤ (6550384690858961/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (181/256:ℝ) (91/128:ℝ)
    (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_181 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_182 :
    (3029851676691713/500000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (91/128:ℝ) (183/256:ℝ)
    (6073603892725/8519600196096:ℝ) (120078579/20000000000000:ℝ) (857180429569033/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_182
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1095).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^4*thetaFirstMode x) ≤ (3030063337222449/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (91/128:ℝ) (183/256:ℝ)
    (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ) (857180429569033/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_182 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_183 :
    (5601017808829737/1000000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (183/256:ℝ) (23/32:ℝ)
    (6241835884235/8707870127616:ℝ) (108588997/20000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_183
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1101).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x) ≤ (2800708956957989/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (183/256:ℝ) (23/32:ℝ)
    (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_183 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_184 :
    (2586138373368703/500000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (23/32:ℝ) (185/256:ℝ)
    (2137925091015/2966414438912:ℝ) (245299619/50000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_184
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1107).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^4*thetaFirstMode x) ≤ (517265456503623/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (23/32:ℝ) (185/256:ℝ)
    (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_184 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_185 :
    (4771924743698501/1000000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (185/256:ℝ) (93/128:ℝ)
    (6589483000555/9093753678336:ℝ) (88588211/20000000000000:ℝ) (2655662276511767/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_185
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1113).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x) ≤ (190891247559587/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (185/256:ℝ) (93/128:ℝ)
    (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ) (2655662276511767/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_185 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_186 :
    (1099613962275039/250000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (93/128:ℝ) (187/256:ℝ)
    (6769020672365/9291435311616:ℝ) (199793/50000000000:ℝ) (1217419628144391/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_186
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1119).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^4*thetaFirstMode x) ≤ (879758364972279/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (93/128:ℝ) (187/256:ℝ)
    (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_186 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_187 :
    (4050414466243743/1000000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (187/256:ℝ) (47/64:ℝ)
    (2317483520625/3164107500032:ℝ) (90044477/25000000000000:ℝ) (278814361538547/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_187
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1125).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x) ≤ (4050730857064251/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (187/256:ℝ) (47/64:ℝ)
    (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ) (278814361538547/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_187 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_188 :
    (232899747496409/62500000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (47/64:ℝ) (189/256:ℝ)
    (7139835613885/9696449711616:ℝ) (64877417/20000000000000:ℝ) (1020809179017363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_188
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1131).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^4*thetaFirstMode x) ≤ (3726693624120681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (47/64:ℝ) (189/256:ℝ)
    (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_188 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_189 :
    (3425047023102281/1000000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (189/256:ℝ) (95/128:ℝ)
    (7331239448195/9903851598336:ℝ) (291908599/100000000000000:ℝ) (933567662673261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_189
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1137).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x) ≤ (3425326804576397/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (189/256:ℝ) (95/128:ℝ)
    (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ) (933567662673261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_189 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_190 :
    (3145065886959819/1000000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (95/128:ℝ) (191/256:ℝ)
    (2508908787735/3371520998912:ℝ) (52492133/20000000000000:ℝ) (85305298899/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_190
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1143).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^4*thetaFirstMode x) ≤ (3145328606440829/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (95/128:ℝ) (191/256:ℝ)
    (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ) (85305298899/50000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_190 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_191 :
    (1442601132000437/500000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (191/256:ℝ) (3/4:ℝ)
    (7726361339515/10328618927616:ℝ) (23578311/10000000000000:ℝ) (778811480076807/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_191
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1149).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x) ≤ (577089747147669/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (191/256:ℝ) (3/4:ℝ)
    (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ) (778811480076807/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_191 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
