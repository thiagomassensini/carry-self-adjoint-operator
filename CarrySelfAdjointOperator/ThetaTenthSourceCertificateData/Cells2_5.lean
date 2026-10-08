import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature5

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_160 :
    (69613642859382691/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (5/8:ℝ) (161/256:ℝ)
    (49614723/79135744:ℝ) (906531311/20000000000000:ℝ) (4513506200394323/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_160
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0962).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x) ≤ (8702078822257903/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/8:ℝ) (161/256:ℝ)
    (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_160 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_161 :
    (64780335352857871/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (161/256:ℝ) (81/128:ℝ)
    (50547885/80124928:ℝ) (2082930867/50000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_161
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0968).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x) ≤ (64783177495891299/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (161/256:ℝ) (81/128:ℝ)
    (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_161 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_162 :
    (60237184194836161/1000000000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (81/128:ℝ) (163/256:ℝ)
    (51492675/81120256:ℝ) (191307857/5000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_162
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0974).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x) ≤ (15059971464641639/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (81/128:ℝ) (163/256:ℝ)
    (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_162 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_163 :
    (13992550515216313/250000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (163/256:ℝ) (41/64:ℝ)
    (52449165/82121728:ℝ) (1755878107/50000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_163
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0980).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x) ≤ (55972768298969939/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (163/256:ℝ) (41/64:ℝ)
    (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_163 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_164 :
    (25982917262930653/500000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (41/64:ℝ) (165/256:ℝ)
    (53417427/83129344:ℝ) (644194769/20000000000000:ℝ) (6852096667522953/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_164
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0986).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x) ≤ (6496033786858691/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (41/64:ℝ) (165/256:ℝ)
    (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_164 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_165 :
    (6026370391566787/125000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (165/256:ℝ) (83/128:ℝ)
    (54397533/84143104:ℝ) (2952221751/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_165
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0992).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x) ≤ (6026659166218521/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (165/256:ℝ) (83/128:ℝ)
    (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_165 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_166 :
    (4469290718546251/100000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (83/128:ℝ) (167/256:ℝ)
    (55389555/85163008:ℝ) (540800801/20000000000000:ℝ) (5944719025535047/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_166
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0998).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x) ≤ (2793443538831189/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (83/128:ℝ) (167/256:ℝ)
    (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (5944719025535047/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_166 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_167 :
    (8279884831310287/200000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (167/256:ℝ) (21/32:ℝ)
    (56393565/86189056:ℝ) (1237456347/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_167
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1004).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x) ≤ (1293796798665561/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (167/256:ℝ) (21/32:ℝ)
    (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_167 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_168 :
    (38318708827128053/1000000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (21/32:ℝ) (169/256:ℝ)
    (57409635/87221248:ℝ) (1131811857/50000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_168
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1010).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x) ≤ (38320670853452423/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (21/32:ℝ) (169/256:ℝ)
    (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_168 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_169 :
    (17719695693365731/500000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (169/256:ℝ) (85/128:ℝ)
    (58437837/88259584:ℝ) (2068892709/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_169
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1016).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x) ≤ (8860311641773013/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (169/256:ℝ) (85/128:ℝ)
    (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_169 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_170 :
    (32750534223771859/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (85/128:ℝ) (171/256:ℝ)
    (59478243/89304064:ℝ) (1889551133/100000000000000:ℝ) (2217991790435067/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_170
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1022).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x) ≤ (8188071761932399/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (85/128:ℝ) (171/256:ℝ)
    (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ) (2217991790435067/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_170 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_171 :
    (30241627990290957/1000000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (171/256:ℝ) (43/64:ℝ)
    (60530925/90354688:ℝ) (26945351/1562500000000:ℝ) (65845773848071/8000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_171
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1028).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x) ≤ (15121641402764203/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (171/256:ℝ) (43/64:ℝ)
    (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ) (65845773848071/8000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_171 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_172 :
    (5580517295020003/200000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (43/64:ℝ) (173/256:ℝ)
    (61595955/91411456:ℝ) (1572718537/100000000000000:ℝ) (7630138077098641/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_172
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1034).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x) ≤ (13952073760150493/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (43/64:ℝ) (173/256:ℝ)
    (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ) (7630138077098641/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_172 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_173 :
    (3215467599113887/125000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (173/256:ℝ) (87/128:ℝ)
    (62673405/92474368:ℝ) (71661801/5000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_173
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1040).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x) ≤ (5145042442973191/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (173/256:ℝ) (87/128:ℝ)
    (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_173 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_174 :
    (23695832696800819/1000000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (87/128:ℝ) (175/256:ℝ)
    (63763347/93543424:ℝ) (163144127/12500000000000:ℝ) (1308491592392887/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_174
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1046).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x) ≤ (592430463765183/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (87/128:ℝ) (175/256:ℝ)
    (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ) (1308491592392887/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_174 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_175 :
    (21810007274913781/1000000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (175/256:ℝ) (11/16:ℝ)
    (64865853/94618624:ℝ) (5938129/500000000000:ℝ) (6051318664087119/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_175
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1052).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x) ≤ (10905655744195151/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (175/256:ℝ) (11/16:ℝ)
    (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_175 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_176 :
    (5014451230464439/250000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (11/16:ℝ) (177/256:ℝ)
    (65980995/95699968:ℝ) (1079865679/100000000000000:ℝ) (1118550559120073/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_176
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1058).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^2*thetaFirstMode x) ≤ (10029515652427999/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (11/16:ℝ) (177/256:ℝ)
    (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ) (1118550559120073/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_176 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_177 :
    (2303894094989993/125000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (177/256:ℝ) (89/128:ℝ)
    (67108845/96787456:ℝ) (981135979/100000000000000:ℝ) (516493902482609/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_177
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1064).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x) ≤ (576009532020199/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (177/256:ℝ) (89/128:ℝ)
    (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_177 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_178 :
    (3384471127798349/200000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (89/128:ℝ) (179/256:ℝ)
    (68249475/97881088:ℝ) (22268729/2500000000000:ℝ) (4766133302660349/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_178
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1070).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^2*thetaFirstMode x) ≤ (16923437375040539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (89/128:ℝ) (179/256:ℝ)
    (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_178 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_179 :
    (7762043281145697/500000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (179/256:ℝ) (45/64:ℝ)
    (69402957/98980864:ℝ) (161612809/20000000000000:ℝ) (2197333628875833/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_179
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1076).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x) ≤ (15525101249749859/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (179/256:ℝ) (45/64:ℝ)
    (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_179 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_180 :
    (711468842515939/50000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (45/64:ℝ) (181/256:ℝ)
    (70569363/100086784:ℝ) (366241587/50000000000000:ℝ) (1012236611442963/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_180
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1082).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^2*thetaFirstMode x) ≤ (1778790981947233/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (45/64:ℝ) (181/256:ℝ)
    (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_180 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_181 :
    (13031605907369331/1000000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (181/256:ℝ) (91/128:ℝ)
    (71748765/101198848:ℝ) (66345027/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_181
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1088).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x) ≤ (814531031213241/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (181/256:ℝ) (91/128:ℝ)
    (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_181 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_182 :
    (11924490833301443/1000000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (91/128:ℝ) (183/256:ℝ)
    (72941235/102317056:ℝ) (37527989/6250000000000:ℝ) (857180429569033/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_182
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1094).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^2*thetaFirstMode x) ≤ (11925324142903377/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (91/128:ℝ) (183/256:ℝ)
    (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ) (857180429569033/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_182 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_183 :
    (10902075657788971/1000000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (183/256:ℝ) (23/32:ℝ)
    (74146845/103441408:ℝ) (271497391/50000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_183
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1100).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x) ≤ (10902854715676131/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (183/256:ℝ) (23/32:ℝ)
    (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_183 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_184 :
    (9958720597394971/1000000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (23/32:ℝ) (185/256:ℝ)
    (75365667/104571904:ℝ) (490644349/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_184
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1106).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^2*thetaFirstMode x) ≤ (9959448284903983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (23/32:ℝ) (185/256:ℝ)
    (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_184 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_185 :
    (2272272746655051/250000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (185/256:ℝ) (93/128:ℝ)
    (76597773/105708544:ℝ) (442981887/100000000000000:ℝ) (2655662276511767/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_185
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1112).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x) ≤ (9089770148674043/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (185/256:ℝ) (93/128:ℝ)
    (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ) (2655662276511767/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_185 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_186 :
    (8288146471293237/1000000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (93/128:ℝ) (187/256:ℝ)
    (77843235/106851328:ℝ) (399622931/100000000000000:ℝ) (1217419628144391/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_186
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1118).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^2*thetaFirstMode x) ≤ (8288779777639011/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (93/128:ℝ) (187/256:ℝ)
    (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_186 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_187 :
    (7551129778639389/1000000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (187/256:ℝ) (47/64:ℝ)
    (79102125/108000256:ℝ) (90052821/25000000000000:ℝ) (278814361538547/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_187
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1124).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x) ≤ (377585990983509/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (187/256:ℝ) (47/64:ℝ)
    (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ) (278814361538547/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_187 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_188 :
    (6873555837190409/1000000000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (47/64:ℝ) (189/256:ℝ)
    (80374515/109155328:ℝ) (40552153/12500000000000:ℝ) (1020809179017363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_188
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1130).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^2*thetaFirstMode x) ≤ (1374821015498971/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (47/64:ℝ) (189/256:ℝ)
    (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_188 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_189 :
    (250048029333427/40000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (189/256:ℝ) (95/128:ℝ)
    (81660477/110316544:ℝ) (291935793/100000000000000:ℝ) (933567662673261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_189
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1136).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x) ≤ (6251711538745157/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (189/256:ℝ) (95/128:ℝ)
    (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ) (933567662673261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_189 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_190 :
    (1420022717735671/250000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (95/128:ℝ) (191/256:ℝ)
    (82960083/111483904:ℝ) (262485181/100000000000000:ℝ) (85305298899/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_190
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1142).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^2*thetaFirstMode x) ≤ (5680565515749567/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (95/128:ℝ) (191/256:ℝ)
    (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ) (85305298899/50000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_190 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_191 :
    (5156492202020993/1000000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (191/256:ℝ) (3/4:ℝ)
    (84273405/112657408:ℝ) (117902597/50000000000000:ℝ) (778811480076807/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_191
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1148).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x) ≤ (1031386571082103/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (191/256:ℝ) (3/4:ℝ)
    (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ) (778811480076807/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_191 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
