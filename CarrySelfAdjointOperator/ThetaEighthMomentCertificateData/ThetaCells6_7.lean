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

theorem thetaFirstMode_refined_cell_lower_6_224 :
    (3643805086552432754621/50440315826549555200000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/8:ℝ) (225/256:ℝ) (1609598370787246343/1835425813694056448:ℝ) (4065821/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1348).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x) ≤ (2086990524084582030573/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/8:ℝ) (225/256:ℝ) (136283/3125000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_225 :
    (1626047950369163069179/25220157913274777600000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (225/256:ℝ) (113/128:ℝ) (1660461446893028857/1885028606660507648:ℝ) (1766629/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1354).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x) ≤ (26077936035657746864857/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (225/256:ℝ) (113/128:ℝ) (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_226 :
    (2898914850098875102129/50440315826549555200000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (113/128:ℝ) (227/256:ℝ) (1712696009065125735/1935743510899152896:ℝ) (3067027/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1360).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x) ≤ (3320963120318543479857/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (113/128:ℝ) (227/256:ℝ) (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_227 :
    (2580881262089196318807/50440315826549555200000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (227/256:ℝ) (57/64:ℝ) (1766332737496293785/1987590384755320832:ℝ) (2659323/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1366).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x) ≤ (10348603544469228574721/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (227/256:ℝ) (57/64:ℝ) (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_228 :
    (327838414884672549313/7205759403792793600000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (57/64:ℝ) (229/256:ℝ) (1821402858995508775/2040589351345350656:ℝ) (2303203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1372).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x) ≤ (18404277013105754084193/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (57/64:ℝ) (229/256:ℝ) (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_229 :
    (2037986441634268617463/50440315826549555200000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (229/256:ℝ) (115/128:ℝ) (1877938154259808473/2094760800899667968:ℝ) (1992493/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1378).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x) ≤ (1167486519137194048707/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (229/256:ℝ) (115/128:ℝ) (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_230 :
    (361513978633694160273/10088063165309911040000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (115/128:ℝ) (231/256:ℝ) (1935970965210345287/2150125393116182528:ℝ) (344343/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1384).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x) ≤ (14497449257660527572431/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (115/128:ℝ) (231/256:ℝ) (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_231 :
    (228737590177818883159/7205759403792793600000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (231/256:ℝ) (29/32:ℝ) (1995534202392930745/2206704059524007936:ℝ) (1486009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1390).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x) ≤ (6421259226707877411753/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (231/256:ℝ) (29/32:ℝ) (40007/2500000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_232 :
    (88531817956539409803/3152519739159347200000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (29/32:ℝ) (233/256:ℝ) (2056661352443354055/2264518005857503232:ℝ) (80067/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1396).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x) ≤ (5680968468055559779999/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/32:ℝ) (233/256:ℝ) (690197/50000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_233 :
    (156441736849646500729/6305039478318694400000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (233/256:ℝ) (117/128:ℝ) (2119386485617756985/2323588714440636416:ℝ) (137887/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1402).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x) ≤ (10039095881101381704469/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (233/256:ℝ) (117/128:ℝ) (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_234 :
    (552169150587174973829/25220157913274777600000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (117/128:ℝ) (235/256:ℝ) (2183744263388347303/2383937946581669888:ℝ) (474359/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1408).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x) ≤ (126553777111358212351/5764607523034234880000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (117/128:ℝ) (235/256:ℝ) (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_235 :
    (973182714324761933749/50440315826549555200000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (235/256:ℝ) (59/64:ℝ) (2249769946104733017/2445587744978167808:ℝ) (814969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1414).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x) ≤ (1115286573803660840941/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (235/256:ℝ) (59/64:ℝ) (879727/100000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_236 :
    (12235356541272362393/720575940379279360000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (59/64:ℝ) (237/256:ℝ) (2317499400721159655/2508560436132325376:ℝ) (69923/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1420).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x) ≤ (137421569427430594633/8070450532247928832000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (59/64:ℝ) (237/256:ℝ) (3021/400000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_237 :
    (752766749941952122341/50440315826549555200000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (237/256:ℝ) (119/128:ℝ) (2386969108589932825/2572878632776620032:ℝ) (599199/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1426).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x) ≤ (754919082031150381897/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (237/256:ℝ) (119/128:ℝ) (1619/250000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_238 :
    (660735128357537456063/50440315826549555200000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (119/128:ℝ) (239/256:ℝ) (2458216173321308295/2638565236309784576:ℝ) (512849/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1432).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x) ≤ (5301241727160944311137/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (119/128:ℝ) (239/256:ℝ) (69327/12500000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_239 :
    (579178119827937134321/50440315826549555200000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (239/256:ℝ) (15/16:ℝ) (2531278328710131833/2705643439243102208:ℝ) (438401/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1438).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x) ≤ (2323554298194485477437/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (239/256:ℝ) (15/16:ℝ) (474399/100000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_240 :
    (507001932717251119333/50440315826549555200000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (15/16:ℝ) (241/256:ℝ) (2606193946729511047/2774136727657023488:ℝ) (374293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1444).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^6*thetaFirstMode x) ≤ (127131230248346027929/12610078956637388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/16:ℝ) (241/256:ℝ) (405281/100000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_241 :
    (443217861739564840153/50440315826549555200000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (241/256:ℝ) (121/128:ℝ) (2683002045591801465/2844068883668105216:ℝ) (319159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1450).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^6*thetaFirstMode x) ≤ (508081568898668935827/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (241/256:ℝ) (121/128:ℝ) (345801/100000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_242 :
    (55275659758990530111/7205759403792793600000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (121/128:ℝ) (243/256:ℝ) (2761742297877189095/2915463987906271232:ℝ) (271803/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1456).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^6*thetaFirstMode x) ≤ (3105037714523444181523/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (121/128:ℝ) (243/256:ℝ) (147339/50000000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_243 :
    (168662096959392017273/25220157913274777600000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (243/256:ℝ) (61/64:ℝ) (2842455038730151705/2988346422002395136:ℝ) (115589/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1462).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^6*thetaFirstMode x) ≤ (386729465491010737669/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (243/256:ℝ) (61/64:ℝ) (50159/20000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_244 :
    (73417547648552274673/12610078956637388800000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (61/64:ℝ) (245/256:ℝ) (2925181274124081063/3062740871086204928:ℝ) (49093/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1468).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^6*thetaFirstMode x) ≤ (117845013269498386741/20176126330619822080000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (61/64:ℝ) (245/256:ℝ) (106587/50000000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_245 :
    (255309844487172189181/50440315826549555200000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (245/256:ℝ) (123/128:ℝ) (3009962689194348377/3138672326294509568:ℝ) (166591/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1474).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^6*thetaFirstMode x) ≤ (409828227864698400101/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (245/256:ℝ) (123/128:ℝ) (90481/50000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_246 :
    (110824246555724984237/25220157913274777600000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (123/128:ℝ) (247/256:ℝ) (3096841656640095175/3216166087289747456:ℝ) (70571/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1480).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^6*thetaFirstMode x) ≤ (889535562256520180653/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (123/128:ℝ) (247/256:ℝ) (153419/100000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_247 :
    (1501204181908204797/394064967394918400000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (247/256:ℝ) (31/32:ℝ) (3185861245195031865/3295247764788856832:ℝ) (933/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1486).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^6*thetaFirstMode x) ≤ (1542407306360452443243/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (247/256:ℝ) (31/32:ℝ) (129897/100000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_248 :
    (166345978773300470201/50440315826549555200000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (31/32:ℝ) (249/256:ℝ) (3277065228167526215/3375943283102468096:ℝ) (100913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1492).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^6*thetaFirstMode x) ≤ (667662822844623580567/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/32:ℝ) (249/256:ℝ) (27459/25000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_249 :
    (71899441672763591829/25220157913274777600000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (249/256:ℝ) (125/128:ℝ) (3370498092050263993/3458278882684418048:ℝ) (42579/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1498).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^6*thetaFirstMode x) ≤ (1154394782452611043467/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (249/256:ℝ) (125/128:ℝ) (371/400000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_250 :
    (62064293713643643633/25220157913274777600000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (125/128:ℝ) (251/256:ℝ) (3466205045199764007/3542281122691586048:ℝ) (35883/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1504).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^6*thetaFirstMode x) ≤ (996541363417019687321/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (125/128:ℝ) (251/256:ℝ) (78217/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_251 :
    (53496715774633212523/25220157913274777600000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (251/256:ℝ) (63/64:ℝ) (3564232026586029785/3627976883554052096:ℝ) (30199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1510).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^6*thetaFirstMode x) ≤ (107378162131777119123/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (251/256:ℝ) (63/64:ℝ) (4117/6250000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_252 :
    (92088419351567693149/50440315826549555200000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (63/64:ℝ) (253/256:ℝ) (3664625714612620135/3715393369555576832:ℝ) (50761/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1516).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^6*thetaFirstMode x) ≤ (739405860546112875439/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (63/64:ℝ) (253/256:ℝ) (277/500000000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_253 :
    (79143354111823174041/50440315826549555200000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (253/256:ℝ) (127/128:ℝ) (3767433536007420825/3804558111424403456:ℝ) (42603/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1522).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^6*thetaFirstMode x) ≤ (635505323222210991719/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (253/256:ℝ) (127/128:ℝ) (46529/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_254 :
    (33958175338078864323/25220157913274777600000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (127/128:ℝ) (255/256:ℝ) (3872703674784399623/3895498968934381568:ℝ) (17853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1528).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^6*thetaFirstMode x) ≤ (136348338920697308633/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (127/128:ℝ) (255/256:ℝ) (2439/6250000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_255 :
    (14548912071045469231/12610078956637388800000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (255/256:ℝ) (1/1:ℝ) (3980485081276626937/3988244133516412928:ℝ) (7471/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1534).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x) ≤ (116841276315106236959/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (255/256:ℝ) (1/1:ℝ) (8171/25000000000000:ℝ) (3417/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
