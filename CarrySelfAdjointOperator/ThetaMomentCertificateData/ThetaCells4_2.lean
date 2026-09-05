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

theorem thetaFirstMode_cell_lower_4_064 :
    (40697884151105679/171798691840000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/2:ℝ) (65/128:ℝ) (11165689815/22156493056:ℝ) (470230479/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_259).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_064 :
    (∫ x in (1/2:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x) ≤ (8154816570303763/34359738368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/2:ℝ) (65/128:ℝ) (7846301/15625000000:ℝ) (44069381/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_256).2 (thetaFirstMode_node_260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_065 :
    (37942881179676297/171798691840000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (65/128:ℝ) (33/64:ℝ) (36175296955/70688218368:ℝ) (412234647/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_263).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_065 :
    (∫ x in (65/128:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x) ≤ (3801641281355531/17179869184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (65/128:ℝ) (33/64:ℝ) (44069381/100000000000:ℝ) (38593061/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_260).2 (thetaFirstMode_node_264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_066 :
    (7053210900333599/34359738368000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (33/64:ℝ) (67/128:ℝ) (39022160765/75104663808:ℝ) (72124229/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_267).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_066 :
    (∫ x in (33/64:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x) ≤ (212020746122411611/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (33/64:ℝ) (67/128:ℝ) (38593061/100000000000:ℝ) (337246369/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_264).2 (thetaFirstMode_node_268).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_067 :
    (32677515292251047/171798691840000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (67/128:ℝ) (17/32:ℝ) (14015167425/26574966016:ℝ) (314786627/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_271).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_067 :
    (∫ x in (67/128:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x) ≤ (4093168783480241/21474836480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (67/128:ℝ) (17/32:ℝ) (337246369/1000000000000:ℝ) (294060307/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_268).2 (thetaFirstMode_node_272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_068 :
    (603717108495603/3435973836800000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/32:ℝ) (69/128:ℝ) (45253402285/84555095808:ℝ) (5483463/20000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_275).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_068 :
    (∫ x in (17/32:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x) ≤ (30250704174705401/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/32:ℝ) (69/128:ℝ) (294060307/1000000000000:ℝ) (255835999/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_272).2 (thetaFirstMode_node_276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_069 :
    (13899086399583/85899345920000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (69/128:ℝ) (35/64:ℝ) (48654184595/89601523968:ℝ) (119133/500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_279).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_069 :
    (∫ x in (69/128:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x) ≤ (167159832423530917/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (69/128:ℝ) (35/64:ℝ) (255835999/1000000000000:ℝ) (111039591/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_276).2 (thetaFirstMode_node_280).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_070 :
    (6380028232220423/42949672960000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (35/64:ℝ) (71/128:ℝ) (17418806535/31623513856:ℝ) (51647873/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_283).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_070 :
    (∫ x in (35/64:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x) ≤ (51157641391995309/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (35/64:ℝ) (71/128:ℝ) (111039591/500000000000:ℝ) (192335553/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_280).2 (thetaFirstMode_node_284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_071 :
    (2919490858092507/21474836480000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (71/128:ℝ) (9/16:ℝ) (56068927915/100368599808:ℝ) (22339347/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_287).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_071 :
    (∫ x in (71/128:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x) ≤ (140469128785927747/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (71/128:ℝ) (9/16:ℝ) (192335553/1000000000000:ℝ) (83094287/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_284).2 (thetaFirstMode_node_288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_072 :
    (21308541039446001/171798691840000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/16:ℝ) (73/128:ℝ) (60100783925/106102242048:ℝ) (154237641/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_291).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_072 :
    (∫ x in (9/16:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x) ≤ (128166123951209741/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/16:ℝ) (73/128:ℝ) (83094287/500000000000:ℝ) (143257283/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_288).2 (thetaFirstMode_node_292).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_073 :
    (19379639891741943/171798691840000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (73/128:ℝ) (37/64:ℝ) (21453773145/37359367936:ℝ) (132796353/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_295).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_073 :
    (∫ x in (73/128:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x) ≤ (7771608385843301/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (73/128:ℝ) (37/64:ℝ) (143257283/1000000000000:ℝ) (3849817/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_292).2 (thetaFirstMode_node_296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_074 :
    (17569755087216257/171798691840000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (37/64:ℝ) (75/128:ℝ) (68860127245/118302912768:ℝ) (114059507/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_299).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_074 :
    (∫ x in (37/64:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x) ≤ (2642410785208261/25769803776000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (37/64:ℝ) (75/128:ℝ) (3849817/31250000000:ℝ) (2642073/25000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_296).2 (thetaFirstMode_node_300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_075 :
    (15878364727451443/171798691840000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (75/128:ℝ) (19/32:ℝ) (73607064755/124783488768:ℝ) (97725943/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_303).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_075 :
    (∫ x in (75/128:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x) ≤ (796083363922703/8589934592000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (75/128:ℝ) (19/32:ℝ) (2642073/25000000000:ℝ) (88317/976562500:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_300).2 (thetaFirstMode_node_304).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_076 :
    (14303994246499671/171798691840000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/32:ℝ) (77/128:ℝ) (26204085855/43842247936:ℝ) (83522691/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_307).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_076 :
    (∫ x in (19/32:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x) ≤ (28688695607778383/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/32:ℝ) (77/128:ℝ) (88317/976562500:ℝ) (77195417/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_304).2 (thetaFirstMode_node_308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_077 :
    (6422161555745867/85899345920000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (77/128:ℝ) (39/64:ℝ) (83886103075/138539682048:ℝ) (35601497/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_311).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_077 :
    (∫ x in (77/128:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x) ≤ (19322708760789641/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (77/128:ℝ) (39/64:ℝ) (77195417/1000000000000:ℝ) (65724811/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_308).2 (thetaFirstMode_node_312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_078 :
    (2299258157889187/34359738368000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (39/64:ℝ) (79/128:ℝ) (89439274085/145829399808:ℝ) (12108877/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_315).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_078 :
    (∫ x in (39/64:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x) ≤ (69185955183386717/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (39/64:ℝ) (79/128:ℝ) (65724811/1000000000000:ℝ) (27906817/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_312).2 (thetaFirstMode_node_316).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_079 :
    (5128101161041819/85899345920000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (79/128:ℝ) (5/8:ℝ) (31760907465/51134361856:ℝ) (25673419/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_319).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_079 :
    (∫ x in (79/128:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x) ≤ (10288223660510823/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (79/128:ℝ) (5/8:ℝ) (27906817/500000000000:ℝ) (1477259/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_316).2 (thetaFirstMode_node_320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_080 :
    (4559916889868703/85899345920000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/8:ℝ) (81/128:ℝ) (101427682405/161268019968:ℝ) (21715503/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_323).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_080 :
    (∫ x in (5/8:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x) ≤ (18298566281880951/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/8:ℝ) (81/128:ℝ) (1477259/31250000000:ℝ) (39931009/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_320).2 (thetaFirstMode_node_324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_081 :
    (4041265400120091/85899345920000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (81/128:ℝ) (41/64:ℝ) (107885674715/169431575808:ℝ) (18318261/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_327).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_081 :
    (∫ x in (81/128:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x) ≤ (3243809653439821/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (81/128:ℝ) (41/64:ℝ) (39931009/1000000000000:ℝ) (16819109/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_324).2 (thetaFirstMode_node_328).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_082 :
    (1784826631618311/42949672960000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (41/64:ℝ) (83/128:ℝ) (38222836575/59300406016:ℝ) (7705101/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_331).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_082 :
    (∫ x in (41/64:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x) ≤ (7163964776285297/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (41/64:ℝ) (83/128:ℝ) (16819109/500000000000:ℝ) (7064739/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_328).2 (thetaFirstMode_node_332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_083 :
    (3142464871096903/85899345920000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (83/128:ℝ) (21/32:ℝ) (121788291235/186684503808:ℝ) (12927763/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_335).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_083 :
    (∫ x in (83/128:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x) ≤ (37844271092242357/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (83/128:ℝ) (21/32:ℝ) (7064739/250000000000:ℝ) (23673409/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_332).2 (thetaFirstMode_node_336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_084 :
    (5514011240868097/171798691840000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/32:ℝ) (85/128:ℝ) (129257420045/195789082368:ℝ) (21629197/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_339).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_084 :
    (∫ x in (21/32:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x) ≤ (16603134029837141/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/32:ℝ) (85/128:ℝ) (23673409/1000000000000:ℝ) (19775517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_336).2 (thetaFirstMode_node_340).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_085 :
    (2410539097017053/85899345920000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (85/128:ℝ) (43/64:ℝ) (45696199185/68407565056:ℝ) (9020903/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_343).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_085 :
    (∫ x in (85/128:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x) ≤ (1209873039675263/42949672960000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (85/128:ℝ) (43/64:ℝ) (19775517/1000000000000:ℝ) (658867/40000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_340).2 (thetaFirstMode_node_344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_086 :
    (4200645565219763/171798691840000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (43/64:ℝ) (87/128:ℝ) (145294829365/214993175808:ℝ) (15005573/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_347).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_086 :
    (∫ x in (43/64:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x) ≤ (790731712459789/32212254720000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (43/64:ℝ) (87/128:ℝ) (658867/40000000000:ℝ) (13679517/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_344).2 (thetaFirstMode_node_348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_087 :
    (1823638433924207/85899345920000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (87/128:ℝ) (11/16:ℝ) (153889428875/225108450048:ℝ) (6221687/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_351).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_087 :
    (∫ x in (87/128:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x) ≤ (21973027722827699/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (87/128:ℝ) (11/16:ℝ) (13679517/1000000000000:ℝ) (5663393/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_348).2 (thetaFirstMode_node_352).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_088 :
    (3155638799011617/171798691840000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/16:ℝ) (89/128:ℝ) (54295340295/78525511936:ℝ) (10287657/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_355).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_088 :
    (∫ x in (11/16:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x) ≤ (1267585244201221/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/16:ℝ) (89/128:ℝ) (5663393/500000000000:ℝ) (9350293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_352).2 (thetaFirstMode_node_356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_089 :
    (680136729602309/42949672960000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (89/128:ℝ) (45/64:ℝ) (172298545195/246405543168:ℝ) (2119859/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_359).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_089 :
    (∫ x in (89/128:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x) ≤ (5464847328729423/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (89/128:ℝ) (45/64:ℝ) (9350293/1000000000000:ℝ) (240467/31250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_356).2 (thetaFirstMode_node_360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_090 :
    (2337004348789517/171798691840000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (45/64:ℝ) (91/128:ℝ) (182141260205/257603674368:ℝ) (6967367/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_363).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_090 :
    (∫ x in (45/64:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x) ≤ (4695104819858643/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (45/64:ℝ) (91/128:ℝ) (240467/31250000000:ℝ) (1262573/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_360).2 (thetaFirstMode_node_364).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_091 :
    (1000116829888231/85899345920000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (91/128:ℝ) (23/32:ℝ) (64142915505/89726407936:ℝ) (2853451/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_367).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_091 :
    (∫ x in (91/128:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x) ≤ (160765390385467/13743895347200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (91/128:ℝ) (23/32:ℝ) (1262573/200000000000:ℝ) (258129/50000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_364).2 (thetaFirstMode_node_368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_092 :
    (852850559493977/85899345920000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/32:ℝ) (93/128:ℝ) (203175910525/281140578048:ℝ) (2329757/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_371).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_092 :
    (∫ x in (23/32:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x) ≤ (10283577031878433/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/32:ℝ) (93/128:ℝ) (258129/50000000000:ℝ) (4208281/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_368).2 (thetaFirstMode_node_372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_093 :
    (1449134126143221/171798691840000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (93/128:ℝ) (47/64:ℝ) (214397988035/293496215808:ℝ) (3791991/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_375).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_093 :
    (∫ x in (93/128:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x) ≤ (1456361014855497/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (93/128:ℝ) (47/64:ℝ) (4208281/1000000000000:ℝ) (3419149/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_372).2 (thetaFirstMode_node_376).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_094 :
    (613267476092051/85899345920000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (47/64:ℝ) (95/128:ℝ) (75370182615/102084902656:ℝ) (1537901/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_379).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_094 :
    (∫ x in (47/64:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x) ≤ (61642890419939/8589934592000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (47/64:ℝ) (95/128:ℝ) (3419149/1000000000000:ℝ) (553751/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_376).2 (thetaFirstMode_node_380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_095 :
    (517092468866457/85899345920000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (95/128:ℝ) (3/4:ℝ) (238329495355/319424717568:ℝ) (1243257/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_383).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_095 :
    (∫ x in (95/128:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x) ≤ (1247635424958299/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (95/128:ℝ) (3/4:ℝ) (553751/200000000000:ℝ) (279313/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_380).2 (thetaFirstMode_node_384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
