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

theorem thetaFirstMode_cell_lower_0_064 :
    (470547883/128000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/2:ℝ) (65/128:ℝ) (129/256:ℝ) (470547883/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_257).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_064 :
    (∫ x in (1/2:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x) ≤ (471428537/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/2:ℝ) (65/128:ℝ) (7846301/15625000000:ℝ) (44069381/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_256).2 (thetaFirstMode_node_260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_065 :
    (412513101/128000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (65/128:ℝ) (33/64:ℝ) (131/256:ℝ) (412513101/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_261).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_065 :
    (∫ x in (65/128:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x) ≤ (41331221/12800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (65/128:ℝ) (33/64:ℝ) (44069381/100000000000:ℝ) (38593061/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_260).2 (thetaFirstMode_node_264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_066 :
    (180432481/64000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (33/64:ℝ) (67/128:ℝ) (133/256:ℝ) (180432481/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_265).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_066 :
    (∫ x in (33/64:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x) ≤ (723176979/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (33/64:ℝ) (67/128:ℝ) (38593061/100000000000:ℝ) (337246369/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_264).2 (thetaFirstMode_node_268).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_067 :
    (3149997/1280000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (67/128:ℝ) (17/32:ℝ) (135/256:ℝ) (3149997/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_269).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_067 :
    (∫ x in (67/128:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x) ≤ (157826669/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (67/128:ℝ) (17/32:ℝ) (337246369/1000000000000:ℝ) (294060307/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_268).2 (thetaFirstMode_node_272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_068 :
    (137179493/64000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/32:ℝ) (69/128:ℝ) (137/256:ℝ) (137179493/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_273).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_068 :
    (∫ x in (17/32:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x) ≤ (274948153/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/32:ℝ) (69/128:ℝ) (294060307/1000000000000:ℝ) (255835999/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_272).2 (thetaFirstMode_node_276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_069 :
    (238427751/128000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (69/128:ℝ) (35/64:ℝ) (139/256:ℝ) (238427751/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_277).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_069 :
    (∫ x in (69/128:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x) ≤ (477915181/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (69/128:ℝ) (35/64:ℝ) (255835999/1000000000000:ℝ) (111039591/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_276).2 (thetaFirstMode_node_280).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_070 :
    (206731989/128000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (35/64:ℝ) (71/128:ℝ) (141/256:ℝ) (206731989/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_281).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_070 :
    (∫ x in (35/64:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x) ≤ (82882947/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (35/64:ℝ) (71/128:ℝ) (111039591/500000000000:ℝ) (192335553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_280).2 (thetaFirstMode_node_284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_071 :
    (178836553/128000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (71/128:ℝ) (9/16:ℝ) (143/256:ℝ) (178836553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_285).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_071 :
    (∫ x in (71/128:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x) ≤ (358524127/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (71/128:ℝ) (9/16:ℝ) (192335553/1000000000000:ℝ) (83094287/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_284).2 (thetaFirstMode_node_288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_072 :
    (154342967/128000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/16:ℝ) (73/128:ℝ) (145/256:ℝ) (154342967/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_289).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_072 :
    (∫ x in (9/16:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x) ≤ (309445857/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/16:ℝ) (73/128:ℝ) (83094287/500000000000:ℝ) (143257283/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_288).2 (thetaFirstMode_node_292).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_073 :
    (8305453/8000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (73/128:ℝ) (37/64:ℝ) (147/256:ℝ) (8305453/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_293).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_073 :
    (∫ x in (73/128:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x) ≤ (266451427/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (73/128:ℝ) (37/64:ℝ) (143257283/1000000000000:ℝ) (3849817/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_292).2 (thetaFirstMode_node_296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_074 :
    (4565511/5120000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (37/64:ℝ) (75/128:ℝ) (149/256:ℝ) (4565511/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_297).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_074 :
    (∫ x in (37/64:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x) ≤ (28609633/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (37/64:ℝ) (75/128:ℝ) (3849817/31250000000:ℝ) (2642073/25000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_296).2 (thetaFirstMode_node_300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_075 :
    (97793183/128000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (75/128:ℝ) (19/32:ℝ) (151/256:ℝ) (97793183/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_301).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_075 :
    (∫ x in (75/128:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x) ≤ (24514941/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (75/128:ℝ) (19/32:ℝ) (2642073/25000000000:ℝ) (88317/976562500:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_300).2 (thetaFirstMode_node_304).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_076 :
    (83580323/128000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/32:ℝ) (77/128:ℝ) (153/256:ℝ) (83580323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_305).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_076 :
    (∫ x in (19/32:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x) ≤ (6705281/10240000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/32:ℝ) (77/128:ℝ) (88317/976562500:ℝ) (77195417/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_304).2 (thetaFirstMode_node_308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_077 :
    (35626137/64000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (77/128:ℝ) (39/64:ℝ) (155/256:ℝ) (35626137/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_309).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_077 :
    (∫ x in (77/128:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x) ≤ (35730057/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (77/128:ℝ) (39/64:ℝ) (77195417/1000000000000:ℝ) (65724811/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_308).2 (thetaFirstMode_node_312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_078 :
    (60586421/128000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (39/64:ℝ) (79/128:ℝ) (157/256:ℝ) (60586421/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_313).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_078 :
    (∫ x in (39/64:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x) ≤ (24307689/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (39/64:ℝ) (79/128:ℝ) (65724811/1000000000000:ℝ) (27906817/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_312).2 (thetaFirstMode_node_316).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_079 :
    (3211413/8000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (79/128:ℝ) (5/8:ℝ) (159/256:ℝ) (3211413/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_317).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_079 :
    (∫ x in (79/128:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x) ≤ (51542961/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (79/128:ℝ) (5/8:ℝ) (27906817/500000000000:ℝ) (1477259/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_316).2 (thetaFirstMode_node_320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_080 :
    (43461367/128000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/8:ℝ) (81/128:ℝ) (161/256:ℝ) (43461367/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_321).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_080 :
    (∫ x in (5/8:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x) ≤ (87203297/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/8:ℝ) (81/128:ℝ) (1477259/31250000000:ℝ) (39931009/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_320).2 (thetaFirstMode_node_324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_081 :
    (36662227/128000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (81/128:ℝ) (41/64:ℝ) (163/256:ℝ) (36662227/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_325).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_081 :
    (∫ x in (81/128:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x) ≤ (73569227/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (81/128:ℝ) (41/64:ℝ) (39931009/1000000000000:ℝ) (16819109/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_324).2 (thetaFirstMode_node_328).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_082 :
    (3084211/12800000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (41/64:ℝ) (83/128:ℝ) (165/256:ℝ) (3084211/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_329).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_082 :
    (∫ x in (41/64:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x) ≤ (30948587/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (41/64:ℝ) (83/128:ℝ) (16819109/500000000000:ℝ) (7064739/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_328).2 (thetaFirstMode_node_332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_083 :
    (1617113/8000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (83/128:ℝ) (21/32:ℝ) (167/256:ℝ) (1617113/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_333).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_083 :
    (∫ x in (83/128:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x) ≤ (10386473/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (83/128:ℝ) (21/32:ℝ) (7064739/250000000000:ℝ) (23673409/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_332).2 (thetaFirstMode_node_336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_084 :
    (2705569/16000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/32:ℝ) (85/128:ℝ) (169/256:ℝ) (2705569/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_337).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_084 :
    (∫ x in (21/32:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x) ≤ (21724463/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/32:ℝ) (85/128:ℝ) (23673409/1000000000000:ℝ) (19775517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_336).2 (thetaFirstMode_node_340).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_085 :
    (4513667/32000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (85/128:ℝ) (43/64:ℝ) (171/256:ℝ) (4513667/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_341).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_085 :
    (∫ x in (85/128:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x) ≤ (4530899/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (85/128:ℝ) (43/64:ℝ) (19775517/1000000000000:ℝ) (658867/40000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_340).2 (thetaFirstMode_node_344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_086 :
    (15016317/128000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (43/64:ℝ) (87/128:ℝ) (173/256:ℝ) (15016317/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_345).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_086 :
    (∫ x in (43/64:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x) ≤ (3768899/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (43/64:ℝ) (87/128:ℝ) (658867/40000000000:ℝ) (13679517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_344).2 (thetaFirstMode_node_348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_087 :
    (12452323/128000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (87/128:ℝ) (11/16:ℝ) (175/256:ℝ) (12452323/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_349).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_087 :
    (∫ x in (87/128:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x) ≤ (25006303/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (87/128:ℝ) (11/16:ℝ) (13679517/1000000000000:ℝ) (5663393/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_348).2 (thetaFirstMode_node_352).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_088 :
    (1029509/12800000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/16:ℝ) (89/128:ℝ) (177/256:ℝ) (1029509/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_353).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_088 :
    (∫ x in (11/16:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x) ≤ (20677079/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/16:ℝ) (89/128:ℝ) (5663393/500000000000:ℝ) (9350293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_352).2 (thetaFirstMode_node_356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_089 :
    (8485591/128000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (89/128:ℝ) (45/64:ℝ) (179/256:ℝ) (8485591/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_357).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_089 :
    (∫ x in (89/128:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x) ≤ (17045237/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (89/128:ℝ) (45/64:ℝ) (9350293/1000000000000:ℝ) (240467/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_356).2 (thetaFirstMode_node_360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_090 :
    (139449/2560000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (45/64:ℝ) (91/128:ℝ) (181/256:ℝ) (139449/20000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_361).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_090 :
    (∫ x in (45/64:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x) ≤ (14007809/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (45/64:ℝ) (91/128:ℝ) (240467/31250000000:ℝ) (1262573/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_360).2 (thetaFirstMode_node_364).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_091 :
    (2855543/64000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (91/128:ℝ) (23/32:ℝ) (183/256:ℝ) (2855543/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_365).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_091 :
    (∫ x in (91/128:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x) ≤ (2295089/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (91/128:ℝ) (23/32:ℝ) (1262573/200000000000:ℝ) (258129/50000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_364).2 (thetaFirstMode_node_368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_092 :
    (4662947/128000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/32:ℝ) (93/128:ℝ) (185/256:ℝ) (4662947/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_369).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_092 :
    (∫ x in (23/32:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x) ≤ (9370861/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/32:ℝ) (93/128:ℝ) (258129/50000000000:ℝ) (4208281/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_368).2 (thetaFirstMode_node_372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_093 :
    (9487/320000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (93/128:ℝ) (47/64:ℝ) (187/256:ℝ) (9487/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_373).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_093 :
    (∫ x in (93/128:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x) ≤ (762743/25600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (93/128:ℝ) (47/64:ℝ) (4208281/1000000000000:ℝ) (3419149/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_372).2 (thetaFirstMode_node_376).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_094 :
    (769523/32000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (47/64:ℝ) (95/128:ℝ) (189/256:ℝ) (769523/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_377).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_094 :
    (∫ x in (47/64:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x) ≤ (48343/2000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (47/64:ℝ) (95/128:ℝ) (3419149/1000000000000:ℝ) (553751/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_376).2 (thetaFirstMode_node_380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_095 :
    (19907/1024000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (95/128:ℝ) (3/4:ℝ) (191/256:ℝ) (19907/8000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_381).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_095 :
    (∫ x in (95/128:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x) ≤ (5003259/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (95/128:ℝ) (3/4:ℝ) (553751/200000000000:ℝ) (279313/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_380).2 (thetaFirstMode_node_384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
