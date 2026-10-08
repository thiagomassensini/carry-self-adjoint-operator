import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature5

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_160 :
    (10754210196493169/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/8:ℝ) (161/256:ℝ)
    (153653616612258567/245075155146180608:ℝ) (566483181/12500000000000:ℝ) (4513506200394323/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_160
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0964).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^6*thetaFirstMode x) ≤ (10754671411674741/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/8:ℝ) (161/256:ℝ)
    (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_160 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_161 :
    (10259281200753171/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (161/256:ℝ) (81/128:ℝ)
    (160481454610240505/254380587287115776:ℝ) (1041283337/25000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_161
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0970).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^6*thetaFirstMode x) ≤ (5129865490929471/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (161/256:ℝ) (81/128:ℝ)
    (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_161 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_162 :
    (24445638840233/2500000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (81/128:ℝ) (163/256:ℝ)
    (167567721804348775/263978612695980032:ℝ) (956371733/25000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_162
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0976).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^6*thetaFirstMode x) ≤ (977869377429271/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (81/128:ℝ) (163/256:ℝ)
    (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_162 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_163 :
    (4655655009751033/500000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (163/256:ℝ) (41/64:ℝ)
    (174920518482869145/273876545640114176:ℝ) (109723123/3125000000000:ℝ) (14697319411579383/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_163
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0982).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^6*thetaFirstMode x) ≤ (9311736630730517/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (163/256:ℝ) (41/64:ℝ)
    (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_163 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_164 :
    (2214644560729349/250000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (41/64:ℝ) (165/256:ℝ)
    (182548146793017383/284081836670609408:ℝ) (1610203763/50000000000000:ℝ) (6852096667522953/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_164
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0988).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^6*thetaFirstMode x) ≤ (8858993163326977/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (41/64:ℝ) (165/256:ℝ)
    (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_164 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_165 :
    (8420152121926747/1000000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (165/256:ℝ) (83/128:ℝ)
    (190459114490427097/294602074304780288:ℝ) (2951701683/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_165
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0994).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^6*thetaFirstMode x) ≤ (8420555309835591/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (165/256:ℝ) (83/128:ℝ)
    (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_165 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_166 :
    (7996083545441921/1000000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (83/128:ℝ) (167/256:ℝ)
    (198662138734783815/305444986718959616:ℝ) (337940841/12500000000000:ℝ) (5944719025535047/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_166
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1000).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^6*thetaFirstMode x) ≤ (7996474976543503/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (83/128:ℝ) (167/256:ℝ)
    (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (5944719025535047/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_166 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_167 :
    (3793193047395941/500000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (167/256:ℝ) (21/32:ℝ)
    (207166149931887545/316618443451615232:ℝ) (123723749/5000000000000:ℝ) (5531197575076283/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_167
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1006).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^6*thetaFirstMode x) ≤ (1896691441891667/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (167/256:ℝ) (21/32:ℝ)
    (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_167 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_168 :
    (7191036843146551/1000000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (21/32:ℝ) (169/256:ℝ)
    (215980295622426055/328130457116788736:ℝ) (452644511/20000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_168
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1012).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^6*thetaFirstMode x) ≤ (3595702388792333/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (21/32:ℝ) (169/256:ℝ)
    (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_168 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_169 :
    (6809978211434761/1000000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (169/256:ℝ) (85/128:ℝ)
    (225113944417741113/339989185127856128:ℝ) (2068525301/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_169
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1018).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^6*thetaFirstMode x) ≤ (6810334446298027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (169/256:ℝ) (85/128:ℝ)
    (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_169 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_170 :
    (644311987442759/100000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (85/128:ℝ) (171/256:ℝ)
    (234576689982869927/352202931431610368:ℝ) (188921487/10000000000000:ℝ) (2217991790435067/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_170
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1024).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^6*thetaFirstMode x) ≤ (6443464464220233/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (85/128:ℝ) (171/256:ℝ)
    (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ) (2217991790435067/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_170 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_171 :
    (3045170338974551/500000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (171/256:ℝ) (43/64:ℝ)
    (244378355067144025/364780148252665856:ℝ) (862097459/50000000000000:ℝ) (65845773848071/8000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_171
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1030).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^6*thetaFirstMode x) ≤ (761334212535761/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (171/256:ℝ) (43/64:ℝ)
    (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ) (65845773848071/8000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_171 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_172 :
    (5751490623634029/1000000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (43/64:ℝ) (173/256:ℝ)
    (254528995582627815/377729437848184832:ℝ) (393109363/25000000000000:ℝ) (7630138077098641/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_172
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1036).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^6*thetaFirstMode x) ≤ (2875906084123507/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (43/64:ℝ) (173/256:ℝ)
    (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ) (7630138077098641/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_172 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_173 :
    (542639283982927/100000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (173/256:ℝ) (87/128:ℝ)
    (265038904730679065/391059554272925696:ℝ) (1432979301/100000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_173
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1042).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^6*thetaFirstMode x) ≤ (5426703012847419/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (173/256:ℝ) (87/128:ℝ)
    (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_173 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_174 :
    (5114845550366747/1000000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (87/128:ℝ) (175/256:ℝ)
    (275918617176913543/404779405154613248:ℝ) (1304918717/100000000000000:ℝ) (1308491592392887/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_174
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1048).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^6*thetaFirstMode x) ≤ (5115144481588451/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (87/128:ℝ) (175/256:ℝ)
    (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ) (1308491592392887/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_174 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_175 :
    (2408312040845529/500000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (175/256:ℝ) (11/16:ℝ)
    (287178913274856057/418898053479630848:ℝ) (1187412117/100000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_175
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1054).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^6*thetaFirstMode x) ≤ (4816911907208737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (175/256:ℝ) (11/16:ℝ)
    (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_175 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_176 :
    (2265741402394671/500000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (11/16:ℝ) (177/256:ℝ)
    (298830823338560135/433424719389034496:ℝ) (1079670939/100000000000000:ℝ) (1118550559120073/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_176
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1060).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x) ≤ (4531759675910649/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/16:ℝ) (177/256:ℝ)
    (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ) (1118550559120073/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_176 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_177 :
    (1064789272535111/250000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (177/256:ℝ) (89/128:ℝ)
    (310885631964478585/448368781984888832:ℝ) (980958633/100000000000000:ℝ) (516493902482609/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_177
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1066).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x) ≤ (4259423171274811/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (177/256:ℝ) (89/128:ℝ)
    (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_177 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_178 :
    (1999682609687059/500000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (89/128:ℝ) (179/256:ℝ)
    (323354882402867175/463739781146925056:ℝ) (222646943/25000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_178
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1072).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x) ≤ (3999620694560131/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (89/128:ℝ) (179/256:ℝ)
    (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_178 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_179 :
    (3751810281518697/1000000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (179/256:ℝ) (45/64:ℝ)
    (336250380979003673/479547419359520768:ℝ) (807917289/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_179
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1078).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x) ≤ (3752055336641861/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (179/256:ℝ) (45/64:ℝ)
    (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_179 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_180 :
    (3516181982543793/1000000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (45/64:ℝ) (181/256:ℝ)
    (349584201564504487/495801563549001728:ℝ) (732349823/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_180
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1084).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x) ≤ (703283364100143/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (45/64:ℝ) (181/256:ℝ)
    (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_180 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_181 :
    (3292158453607973/1000000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (181/256:ℝ) (91/128:ℝ)
    (363368690099021145/512512246931265536:ℝ) (82916149/12500000000000:ℝ) (465931073813781/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_181
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1090).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x) ≤ (3292383284704379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (181/256:ℝ) (91/128:ℝ)
    (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_181 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_182 :
    (3079407975843337/1000000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (91/128:ℝ) (183/256:ℝ)
    (377616469162598855/529689670869727232:ℝ) (600337973/100000000000000:ℝ) (857180429569033/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_182
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1096).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x) ≤ (3079623019318433/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (91/128:ℝ) (183/256:ℝ)
    (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ) (857180429569033/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_182 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_183 :
    (719397661391417/250000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (183/256:ℝ) (23/32:ℝ)
    (392340442598979385/547344206743586816:ℝ) (542895193/100000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_183
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1102).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x) ≤ (2877796133590469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (183/256:ℝ) (23/32:ℝ)
    (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_183 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_184 :
    (1343180001277991/500000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (23/32:ℝ) (185/256:ℝ)
    (407553800190130503/565486397826418688:ℝ) (490554133/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_184
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1108).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x) ≤ (2686556162885737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (23/32:ℝ) (185/256:ℝ)
    (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_184 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_185 :
    (19573160461979/7812500000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (185/256:ℝ) (93/128:ℝ)
    (423270022382284217/584126961175083008:ℝ) (442900227/100000000000000:ℝ) (2655662276511767/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_185
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1114).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x) ≤ (2505551616584177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (185/256:ℝ) (93/128:ℝ)
    (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ) (2655662276511767/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_185 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_186 :
    (2334249191392619/1000000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (93/128:ℝ) (187/256:ℝ)
    (439502885063766055/603276789528958976:ℝ) (399549073/100000000000000:ℝ) (1217419628144391/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_186
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1120).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x) ≤ (2334427431542279/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (93/128:ℝ) (187/256:ℝ)
    (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_186 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_187 :
    (2172656720890847/1000000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (187/256:ℝ) (47/64:ℝ)
    (456266464394897625/622946953219500032:ℝ) (45018067/12500000000000:ℝ) (278814361538547/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_187
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1126).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x) ≤ (2172826374467101/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (187/256:ℝ) (47/64:ℝ)
    (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ) (278814361538547/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_187 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_188 :
    (1010114519431629/500000000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (47/64:ℝ) (189/256:ℝ)
    (473575141690254695/643148702090110976:ℝ) (6487139/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_188
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1132).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x) ≤ (252548794559667/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (47/64:ℝ) (189/256:ℝ)
    (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_188 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_189 :
    (1876608431755607/1000000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (189/256:ℝ) (95/128:ℝ)
    (491443608353563033/663893467426347008:ℝ) (291881409/100000000000000:ℝ) (933567662673261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_189
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1138).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x) ≤ (938380834888573/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (189/256:ℝ) (95/128:ℝ)
    (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ) (933567662673261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_189 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_190 :
    (870719364763287/500000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (95/128:ℝ) (191/256:ℝ)
    (509886870865514247/685192863896434688:ℝ) (262436151/100000000000000:ℝ) (85305298899/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_190
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1144).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x) ≤ (870792076091257/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (95/128:ℝ) (191/256:ℝ)
    (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ) (85305298899/50000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_190 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_191 :
    (1614366394898227/1000000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (191/256:ℝ) (3/4:ℝ)
    (528920255824783865/707058691502114816:ℝ) (58940257/25000000000000:ℝ) (778811480076807/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_191
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1150).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x) ≤ (64580170329767/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (191/256:ℝ) (3/4:ℝ)
    (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ) (778811480076807/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_191 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
