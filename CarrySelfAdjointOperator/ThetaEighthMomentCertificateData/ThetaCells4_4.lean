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

theorem thetaFirstMode_refined_cell_lower_4_128 :
    (6626353619093667327/54975581388800000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/2:ℝ) (129/256:ℝ) (1051135758085/2094049199616:ℝ) (4860477567/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0771).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^4*thetaFirstMode x) ≤ (198883227375844663969/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/2:ℝ) (129/256:ℝ) (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_129 :
    (64030540393308639067/549755813888000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (129/256:ℝ) (65/128:ℝ) (1092676686395/2159997467136:ℝ) (45532882117/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0777).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x) ≤ (48045667940073095363/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (129/256:ℝ) (65/128:ℝ) (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_130 :
    (61825423780126213361/549755813888000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (65/128:ℝ) (131/256:ℝ) (378506907135/742497101312:ℝ) (42632647211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0783).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^4*thetaFirstMode x) ≤ (61855236807501537789/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (65/128:ℝ) (131/256:ℝ) (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_131 :
    (2386020602536128577/21990232555520000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (131/256:ℝ) (33/64:ℝ) (1179698283715/2296554671616:ℝ) (1595837317/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0789).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x) ≤ (119359555148497430097/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (131/256:ℝ) (33/64:ℝ) (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_132 :
    (28753995134312153709/274877906944000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (33/64:ℝ) (133/256:ℝ) (1225240263725/2367211716096:ℝ) (18657450969/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0795).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^4*thetaFirstMode x) ≤ (345220139986605046841/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (33/64:ℝ) (133/256:ℝ) (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_133 :
    (5539987255074276569/54975581388800000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (133/256:ℝ) (67/128:ℝ) (424059341745/813162255872:ℝ) (3488201099/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0801).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x) ≤ (55427998322850961701/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (133/256:ℝ) (67/128:ℝ) (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_134 :
    (13332008126693019991/137438953472000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (67/128:ℝ) (135/256:ℝ) (1320543409045/2513404340736:ℝ) (8147501041/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0807).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^4*thetaFirstMode x) ≤ (21342229696364099541/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (67/128:ℝ) (135/256:ℝ) (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_135 :
    (25647094491092201259/274877906944000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (135/256:ℝ) (17/32:ℝ) (1370368736555/2588989134336:ℝ) (15215953059/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0813).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x) ≤ (7698170653156689389/82463372083200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (135/256:ℝ) (17/32:ℝ) (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_136 :
    (24649955165085694873/274877906944000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/32:ℝ) (137/256:ℝ) (473895604455/888755343872:ℝ) (14200507633/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0819).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^4*thetaFirstMode x) ≤ (98652516211894952499/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/32:ℝ) (137/256:ℝ) (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_137 :
    (47346616116496978519/549755813888000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (137/256:ℝ) (69/128:ℝ) (1474530932875/2745260100096:ℝ) (26490896929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0825).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x) ≤ (47372356142999454749/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (137/256:ℝ) (69/128:ℝ) (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_138 :
    (45435579240307284853/549755813888000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (69/128:ℝ) (139/256:ℝ) (1528934879885/2825996591616:ℝ) (24695376463/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0831).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^4*thetaFirstMode x) ≤ (272764234617019114187/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (69/128:ℝ) (139/256:ℝ) (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_139 :
    (348543427575290959/4398046511104000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (139/256:ℝ) (35/64:ℝ) (528310978065/969500314112:ℝ) (184068259/800000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0837).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x) ≤ (87184873585716187137/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (139/256:ℝ) (35/64:ℝ) (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_140 :
    (41744651214371574141/549755813888000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (35/64:ℝ) (141/256:ℝ) (1642559874205/2992798772736:ℝ) (21424689441/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0843).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^4*thetaFirstMode x) ≤ (41768537736532136701/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (35/64:ℝ) (141/256:ℝ) (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_141 :
    (3996659697735534173/54975581388800000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (141/256:ℝ) (71/128:ℝ) (1701850980515/3078915887616:ℝ) (1993841183/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0849).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x) ≤ (29992394295641539979/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (141/256:ℝ) (71/128:ℝ) (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_142 :
    (4779310083734943041/68719476736000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (71/128:ℝ) (143/256:ℝ) (587614013175/1055626092032:ℝ) (2318062031/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0855).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^4*thetaFirstMode x) ≤ (19128558353484215711/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (71/128:ℝ) (143/256:ℝ) (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_143 :
    (36548886556050990629/549755813888000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (143/256:ℝ) (9/16:ℝ) (1825569347035/3256712111616:ℝ) (17237965109/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0861).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x) ≤ (73141791854587077013/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (143/256:ℝ) (9/16:ℝ) (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_144 :
    (139641089356815839/2199023255552000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/16:ℝ) (145/256:ℝ) (1890069711845/3348443751936:ℝ) (64056239/400000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0867).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x) ≤ (13972662152782815089/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/16:ℝ) (145/256:ℝ) (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_145 :
    (416487168549325271/6871947673600000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (145/256:ℝ) (73/128:ℝ) (652126819785/1147366579712:ℝ) (185852921/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0873).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x) ≤ (3333973147541529979/54975581388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (145/256:ℝ) (73/128:ℝ) (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_146 :
    (31775207783454878369/549755813888000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (73/128:ℝ) (147/256:ℝ) (2024539435165/3537706799616:ℝ) (13796145899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0879).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x) ≤ (12718137160946382293/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (73/128:ℝ) (147/256:ℝ) (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_147 :
    (6055816016372201233/109951162777600000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (147/256:ℝ) (37/64:ℝ) (2094585008675/3635291844096:ℝ) (2558730853/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0885).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x) ≤ (9089578614633528781/164926744166400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (147/256:ℝ) (37/64:ℝ) (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_148 :
    (14415293585938937289/274877906944000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (37/64:ℝ) (149/256:ℝ) (722185358895/1244960655872:ℝ) (5928404469/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0891).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x) ≤ (7212371638462368317/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (37/64:ℝ) (149/256:ℝ) (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_149 :
    (13714811415085184701/274877906944000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (149/256:ℝ) (75/128:ℝ) (2240492066995/3836504449536:ℝ) (5490922951/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0897).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x) ≤ (13723955502918098017/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (149/256:ℝ) (75/128:ℝ) (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_150 :
    (26075982959163632319/549755813888000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (75/128:ℝ) (151/256:ℝ) (2316432942005/3940186753536:ℝ) (10165180569/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0903).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x) ≤ (26093665413066310449/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (75/128:ℝ) (151/256:ℝ) (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_151 :
    (2476937080686223307/54975581388800000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (151/256:ℝ) (19/32:ℝ) (798139734105/1348652175872:ℝ) (940340147/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0909).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x) ≤ (49572907523662055149/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (151/256:ℝ) (19/32:ℝ) (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_152 :
    (4701880451238656449/109951162777600000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/32:ℝ) (153/256:ℝ) (2474491890325/4153841604096:ℝ) (1738652809/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0915).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x) ≤ (28231071167662979851/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/32:ℝ) (153/256:ℝ) (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_153 :
    (11147805576465629277/274877906944000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (153/256:ℝ) (77/128:ℝ) (2556692593835/4263869999616:ℝ) (4015842267/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0921).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x) ≤ (44623033123425639211/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (153/256:ℝ) (77/128:ℝ) (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_154 :
    (21127454658464545427/549755813888000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (77/128:ℝ) (155/256:ℝ) (880354483215/1458689971712:ℝ) (7415733977/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0927).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x) ≤ (5285695827115701447/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (77/128:ℝ) (155/256:ℝ) (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_155 :
    (10002159283904531457/274877906944000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (155/256:ℝ) (39/64:ℝ) (2727647147155/4490469735936:ℝ) (3421316157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0933).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x) ≤ (10009539634329773679/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (155/256:ℝ) (39/64:ℝ) (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_156 :
    (9462761326624800329/274877906944000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (39/64:ℝ) (157/256:ℝ) (2816486931965/4607098031616:ℝ) (3154871309/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0939).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x) ≤ (37879449514656441223/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (39/64:ℝ) (157/256:ℝ) (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_157 :
    (4472581477632210327/137438953472000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (157/256:ℝ) (79/128:ℝ) (969208869825/1575327852032:ℝ) (1453641357/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0945).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x) ≤ (17903979281976286767/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (157/256:ℝ) (79/128:ℝ) (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_158 :
    (8448965891019664879/274877906944000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (79/128:ℝ) (159/256:ℝ) (3001110548485/4847155247616:ℝ) (2677366609/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0951).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x) ≤ (50733140263958880373/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (79/128:ℝ) (159/256:ℝ) (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_159 :
    (3986873323042715647/137438953472000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (159/256:ℝ) (5/8:ℝ) (3096983684795/4970642228736:ℝ) (1232001247/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0957).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x) ≤ (7980040312842265647/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (159/256:ℝ) (5/8:ℝ) (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
