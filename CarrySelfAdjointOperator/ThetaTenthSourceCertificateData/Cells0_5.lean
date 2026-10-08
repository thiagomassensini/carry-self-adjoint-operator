import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature5

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_160 :
    (177117188085315171/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/8:ℝ) (161/256:ℝ)
    (321/512:ℝ) (4533052171/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_160
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0961).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x) ≤ (22140599050448551/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/8:ℝ) (161/256:ℝ)
    (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_160 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_161 :
    (162785097770302659/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (161/256:ℝ) (81/128:ℝ)
    (323/512:ℝ) (65097281/1562500000000:ℝ) (16869263981906327/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_161
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0967).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x) ≤ (81396121135947341/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (161/256:ℝ) (81/128:ℝ)
    (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_161 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_162 :
    (37377868564034427/250000000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (81/128:ℝ) (163/256:ℝ)
    (325/512:ℝ) (478311537/12500000000000:ℝ) (15751367210440041/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_162
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0973).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x) ≤ (149518182308037083/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (81/128:ℝ) (163/256:ℝ)
    (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_162 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_163 :
    (17153314611342071/125000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (163/256:ℝ) (41/64:ℝ)
    (327/512:ℝ) (1756032201/50000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_163
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0979).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x) ≤ (34308202736272341/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (163/256:ℝ) (41/64:ℝ)
    (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_163 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_164 :
    (31466097052220507/250000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (41/64:ℝ) (165/256:ℝ)
    (329/512:ℝ) (3221257049/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_164
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0985).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x) ≤ (125870289871298443/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/64:ℝ) (165/256:ℝ)
    (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_164 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_165 :
    (115363033854831137/1000000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (165/256:ℝ) (83/128:ℝ)
    (331/512:ℝ) (1476240913/50000000000000:ℝ) (1276914985091137/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_165
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0991).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x) ≤ (4614742552551009/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (165/256:ℝ) (83/128:ℝ)
    (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_165 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_166 :
    (10566400746537971/100000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (83/128:ℝ) (167/256:ℝ)
    (333/512:ℝ) (2704242681/100000000000000:ℝ) (5944719025535047/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_166
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0997).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x) ≤ (10566918559658433/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (83/128:ℝ) (167/256:ℝ)
    (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (5944719025535047/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_166 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_167 :
    (96712301294616243/1000000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (167/256:ℝ) (21/32:ℝ)
    (335/512:ℝ) (495026317/20000000000000:ℝ) (5531197575076283/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_167
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1003).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x) ≤ (96717146629517513/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (167/256:ℝ) (21/32:ℝ)
    (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_167 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_168 :
    (44228090938675891/500000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (21/32:ℝ) (169/256:ℝ)
    (337/512:ℝ) (90552973/4000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_168
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1009).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x) ≤ (44230356335538843/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/32:ℝ) (169/256:ℝ)
    (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_168 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_169 :
    (40423515658532629/500000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (169/256:ℝ) (85/128:ℝ)
    (339/512:ℝ) (2069076441/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_169
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1015).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x) ≤ (10106408122882123/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (169/256:ℝ) (85/128:ℝ)
    (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_169 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_170 :
    (73839193573484769/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (85/128:ℝ) (171/256:ℝ)
    (341/512:ℝ) (1889719291/100000000000000:ℝ) (2217991790435067/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_170
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1021).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x) ≤ (9230393357117089/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (85/128:ℝ) (171/256:ℝ)
    (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ) (2217991790435067/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_170 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_171 :
    (33694913226458789/500000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (171/256:ℝ) (43/64:ℝ)
    (343/512:ℝ) (862328131/50000000000000:ℝ) (65845773848071/8000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_171
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1027).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x) ≤ (4212094703639209/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (171/256:ℝ) (43/64:ℝ)
    (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ) (65845773848071/8000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_171 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_172 :
    (30729379162389013/500000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (43/64:ℝ) (173/256:ℝ)
    (345/512:ℝ) (786429551/50000000000000:ℝ) (7630138077098641/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_172
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1033).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x) ≤ (61462197881693947/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/64:ℝ) (173/256:ℝ)
    (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ) (7630138077098641/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_172 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_173 :
    (11201670123800243/200000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (173/256:ℝ) (87/128:ℝ)
    (347/512:ℝ) (3583411/250000000000:ℝ) (7068070913210319/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_173
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1039).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x) ≤ (5601155544168507/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (173/256:ℝ) (87/128:ℝ)
    (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_173 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_174 :
    (51003364932615867/1000000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (87/128:ℝ) (175/256:ℝ)
    (349/512:ℝ) (163158773/12500000000000:ℝ) (1308491592392887/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_174
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1045).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x) ≤ (25503174442384133/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (87/128:ℝ) (175/256:ℝ)
    (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ) (1308491592392887/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_174 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_175 :
    (5801354445699977/125000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (175/256:ℝ) (11/16:ℝ)
    (351/512:ℝ) (593866329/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_175
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1051).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x) ≤ (46413611837550367/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (175/256:ℝ) (11/16:ℝ)
    (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_175 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_176 :
    (42199946939320763/1000000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (11/16:ℝ) (177/256:ℝ)
    (353/512:ℝ) (134995383/12500000000000:ℝ) (1118550559120073/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_176
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1057).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x) ≤ (42202528035420973/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/16:ℝ) (177/256:ℝ)
    (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ) (1118550559120073/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_176 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_177 :
    (19170957890226277/500000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (177/256:ℝ) (89/128:ℝ)
    (355/512:ℝ) (490612333/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_177
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1063).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x) ≤ (38344313634407391/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (177/256:ℝ) (89/128:ℝ)
    (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_177 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_178 :
    (8702469624947471/250000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (89/128:ℝ) (179/256:ℝ)
    (357/512:ℝ) (890829867/100000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_178
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1069).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x) ≤ (34812104406670231/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (89/128:ℝ) (179/256:ℝ)
    (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_178 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_179 :
    (1578939139491259/50000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (179/256:ℝ) (45/64:ℝ)
    (359/512:ℝ) (404068717/50000000000000:ℝ) (2197333628875833/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_179
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1075).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x) ≤ (3158084756488089/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (179/256:ℝ) (45/64:ℝ)
    (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_179 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_180 :
    (28625284534463117/1000000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (45/64:ℝ) (181/256:ℝ)
    (361/512:ℝ) (732549859/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_180
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1081).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x) ≤ (14313599176474383/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/64:ℝ) (181/256:ℝ)
    (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_180 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_181 :
    (3240956073237791/125000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (181/256:ℝ) (91/128:ℝ)
    (363/512:ℝ) (663510819/100000000000000:ℝ) (465931073813781/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_181
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1087).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x) ≤ (25929421089914093/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (181/256:ℝ) (91/128:ℝ)
    (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_181 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_182 :
    (11732827172969823/500000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (91/128:ℝ) (183/256:ℝ)
    (365/512:ℝ) (600502759/100000000000000:ℝ) (857180429569033/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_182
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1093).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x) ≤ (91669119947493/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (91/128:ℝ) (183/256:ℝ)
    (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ) (857180429569033/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_182 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_183 :
    (21220505644183959/1000000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (183/256:ℝ) (23/32:ℝ)
    (367/512:ℝ) (108608917/20000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_183
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1099).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x) ≤ (21222022539757081/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (183/256:ℝ) (23/32:ℝ)
    (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_183 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_184 :
    (19174744756618031/1000000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (23/32:ℝ) (185/256:ℝ)
    (369/512:ℝ) (490689463/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_184
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1105).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x) ≤ (19176146365670187/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/32:ℝ) (185/256:ℝ)
    (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_184 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_185 :
    (17312170564859787/1000000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (185/256:ℝ) (93/128:ℝ)
    (371/512:ℝ) (110755681/25000000000000:ℝ) (2655662276511767/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_185
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1111).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x) ≤ (4328366148234169/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (185/256:ℝ) (93/128:ℝ)
    (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ) (2655662276511767/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_185 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_186 :
    (15617760504331511/1000000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (93/128:ℝ) (187/256:ℝ)
    (373/512:ℝ) (199829933/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_186
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1117).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x) ≤ (7809477132387239/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (93/128:ℝ) (187/256:ℝ)
    (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_186 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_187 :
    (703879836557963/50000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (187/256:ℝ) (47/64:ℝ)
    (375/512:ℝ) (45030583/12500000000000:ℝ) (278814361538547/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_187
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1123).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x) ≤ (14078697084556479/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (187/256:ℝ) (47/64:ℝ)
    (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ) (278814361538547/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_187 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_188 :
    (2535759129683313/200000000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (47/64:ℝ) (189/256:ℝ)
    (377/512:ℝ) (162223683/50000000000000:ℝ) (1020809179017363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_188
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1129).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x) ≤ (12679809093791869/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/64:ℝ) (189/256:ℝ)
    (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_188 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_189 :
    (2281888275523457/200000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (189/256:ℝ) (95/128:ℝ)
    (379/512:ℝ) (29196299/10000000000000:ℝ) (933567662673261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_189
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1135).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x) ≤ (11410373963515429/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (189/256:ℝ) (95/128:ℝ)
    (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ) (933567662673261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_189 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_190 :
    (1282315289535243/125000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (95/128:ℝ) (191/256:ℝ)
    (381/512:ℝ) (2625097/1000000000000:ℝ) (85305298899/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_190
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1141).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x) ≤ (10259379820561111/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (95/128:ℝ) (191/256:ℝ)
    (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ) (85305298899/50000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_190 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_191 :
    (9215871523468081/1000000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (191/256:ℝ) (3/4:ℝ)
    (383/512:ℝ) (2947841/1250000000000:ℝ) (778811480076807/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_191
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1147).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x) ≤ (2304164838851897/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (191/256:ℝ) (3/4:ℝ)
    (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ) (778811480076807/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_191 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator
