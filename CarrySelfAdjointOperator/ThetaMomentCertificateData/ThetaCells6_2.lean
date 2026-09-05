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

theorem thetaFirstMode_cell_upper_6_064 :
    (∫ x in (1/2:ℝ)..(65/128:ℝ), x^6*thetaFirstMode x) ≤ (949781149098060674639/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/2:ℝ) (65/128:ℝ) (7846301/15625000000:ℝ) (44069381/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_256).2 (thetaFirstMode_node_260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_065 :
    (∫ x in (65/128:ℝ)..(33/64:ℝ), x^6*thetaFirstMode x) ≤ (22830277439586781631/394064967394918400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (65/128:ℝ) (33/64:ℝ) (44069381/100000000000:ℝ) (38593061/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_260).2 (thetaFirstMode_node_264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_066 :
    (∫ x in (33/64:ℝ)..(67/128:ℝ), x^6*thetaFirstMode x) ≤ (249986987802285045423/4503599627370496000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (33/64:ℝ) (67/128:ℝ) (38593061/100000000000:ℝ) (337246369/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_264).2 (thetaFirstMode_node_268).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_067 :
    (∫ x in (67/128:ℝ)..(17/32:ℝ), x^6*thetaFirstMode x) ≤ (835352750134577279533/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (67/128:ℝ) (17/32:ℝ) (337246369/1000000000000:ℝ) (294060307/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_268).2 (thetaFirstMode_node_272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_068 :
    (∫ x in (17/32:ℝ)..(69/128:ℝ), x^6*thetaFirstMode x) ≤ (397371843572459980979/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/32:ℝ) (69/128:ℝ) (294060307/1000000000000:ℝ) (255835999/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_272).2 (thetaFirstMode_node_276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_069 :
    (∫ x in (69/128:ℝ)..(35/64:ℝ), x^6*thetaFirstMode x) ≤ (301382843127723398603/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (69/128:ℝ) (35/64:ℝ) (255835999/1000000000000:ℝ) (111039591/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_276).2 (thetaFirstMode_node_280).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_070 :
    (∫ x in (35/64:ℝ)..(71/128:ℝ), x^6*thetaFirstMode x) ≤ (1423622498109487608453/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (35/64:ℝ) (71/128:ℝ) (111039591/500000000000:ℝ) (192335553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_280).2 (thetaFirstMode_node_284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_071 :
    (∫ x in (71/128:ℝ)..(9/16:ℝ), x^6*thetaFirstMode x) ≤ (1340218815222085243237/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (71/128:ℝ) (9/16:ℝ) (192335553/1000000000000:ℝ) (83094287/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_284).2 (thetaFirstMode_node_288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_072 :
    (∫ x in (9/16:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x) ≤ (1257274032295271355507/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/16:ℝ) (73/128:ℝ) (83094287/500000000000:ℝ) (143257283/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_288).2 (thetaFirstMode_node_292).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_073 :
    (∫ x in (73/128:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x) ≤ (235063668911054187329/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (73/128:ℝ) (37/64:ℝ) (143257283/1000000000000:ℝ) (3849817/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_292).2 (thetaFirstMode_node_296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_074 :
    (∫ x in (37/64:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x) ≤ (136854656660618240191/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (37/64:ℝ) (75/128:ℝ) (3849817/31250000000:ℝ) (2642073/25000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_296).2 (thetaFirstMode_node_300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_075 :
    (∫ x in (75/128:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x) ≤ (127033560587994528747/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (75/128:ℝ) (19/32:ℝ) (2642073/25000000000:ℝ) (88317/976562500:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_300).2 (thetaFirstMode_node_304).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_076 :
    (∫ x in (19/32:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x) ≤ (939999853658673706799/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/32:ℝ) (77/128:ℝ) (88317/976562500:ℝ) (77195417/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_304).2 (thetaFirstMode_node_308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_077 :
    (∫ x in (77/128:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x) ≤ (433183989510444503589/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (77/128:ℝ) (39/64:ℝ) (77195417/1000000000000:ℝ) (65724811/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_308).2 (thetaFirstMode_node_312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_078 :
    (∫ x in (39/64:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x) ≤ (795657940568802682617/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (39/64:ℝ) (79/128:ℝ) (65724811/1000000000000:ℝ) (27906817/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_312).2 (thetaFirstMode_node_316).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_079 :
    (∫ x in (79/128:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x) ≤ (364051848966599447223/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (79/128:ℝ) (5/8:ℝ) (27906817/500000000000:ℝ) (1477259/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_316).2 (thetaFirstMode_node_320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_080 :
    (∫ x in (5/8:ℝ)..(81/128:ℝ), x^6*thetaFirstMode x) ≤ (663889226447012729831/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/8:ℝ) (81/128:ℝ) (1477259/31250000000:ℝ) (39931009/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_320).2 (thetaFirstMode_node_324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_081 :
    (∫ x in (81/128:ℝ)..(41/64:ℝ), x^6*thetaFirstMode x) ≤ (120630078024052857997/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (81/128:ℝ) (41/64:ℝ) (39931009/1000000000000:ℝ) (16819109/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_324).2 (thetaFirstMode_node_328).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_082 :
    (∫ x in (41/64:ℝ)..(83/128:ℝ), x^6*thetaFirstMode x) ≤ (272988669258541189967/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (41/64:ℝ) (83/128:ℝ) (16819109/500000000000:ℝ) (7064739/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_328).2 (thetaFirstMode_node_332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_083 :
    (∫ x in (83/128:ℝ)..(21/32:ℝ), x^6*thetaFirstMode x) ≤ (492417405596931739957/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (83/128:ℝ) (21/32:ℝ) (7064739/250000000000:ℝ) (23673409/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_332).2 (thetaFirstMode_node_336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_084 :
    (∫ x in (21/32:ℝ)..(85/128:ℝ), x^6*thetaFirstMode x) ≤ (4424784013067143987/315251973915934720000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/32:ℝ) (85/128:ℝ) (23673409/1000000000000:ℝ) (19775517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_336).2 (thetaFirstMode_node_340).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_085 :
    (∫ x in (85/128:ℝ)..(43/64:ℝ), x^6*thetaFirstMode x) ≤ (198066108267522049451/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (85/128:ℝ) (43/64:ℝ) (19775517/1000000000000:ℝ) (658867/40000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_340).2 (thetaFirstMode_node_344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_086 :
    (∫ x in (43/64:ℝ)..(87/128:ℝ), x^6*thetaFirstMode x) ≤ (176659324939288789979/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (43/64:ℝ) (87/128:ℝ) (658867/40000000000:ℝ) (13679517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_344).2 (thetaFirstMode_node_348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_087 :
    (∫ x in (87/128:ℝ)..(11/16:ℝ), x^6*thetaFirstMode x) ≤ (44849903526947043019/4503599627370496000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (87/128:ℝ) (11/16:ℝ) (13679517/1000000000000:ℝ) (5663393/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_348).2 (thetaFirstMode_node_352).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_088 :
    (∫ x in (11/16:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x) ≤ (55582343922992560657/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/16:ℝ) (89/128:ℝ) (5663393/500000000000:ℝ) (9350293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_352).2 (thetaFirstMode_node_356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_089 :
    (∫ x in (89/128:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x) ≤ (49014614679416319751/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (89/128:ℝ) (45/64:ℝ) (9350293/1000000000000:ℝ) (240467/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_356).2 (thetaFirstMode_node_360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_090 :
    (∫ x in (45/64:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x) ≤ (215284273115505826679/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (45/64:ℝ) (91/128:ℝ) (240467/31250000000:ℝ) (1262573/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_360).2 (thetaFirstMode_node_364).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_091 :
    (∫ x in (91/128:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x) ≤ (7535342036380872691/1261007895663738880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (91/128:ℝ) (23/32:ℝ) (1262573/200000000000:ℝ) (258129/50000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_364).2 (thetaFirstMode_node_368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_092 :
    (∫ x in (23/32:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x) ≤ (164199947532256745731/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/32:ℝ) (93/128:ℝ) (258129/50000000000:ℝ) (4208281/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_368).2 (thetaFirstMode_node_372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_093 :
    (∫ x in (93/128:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x) ≤ (35639142709496067683/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (93/128:ℝ) (47/64:ℝ) (4208281/1000000000000:ℝ) (3419149/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_372).2 (thetaFirstMode_node_376).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_094 :
    (∫ x in (47/64:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x) ≤ (61636783887603414529/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (47/64:ℝ) (95/128:ℝ) (3419149/1000000000000:ℝ) (553751/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_376).2 (thetaFirstMode_node_380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_095 :
    (∫ x in (95/128:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x) ≤ (106170763552027686573/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (95/128:ℝ) (3/4:ℝ) (553751/200000000000:ℝ) (279313/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_380).2 (thetaFirstMode_node_384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
