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

theorem thetaFirstMode_refined_cell_lower_8_224 :
    (26233367576101116188081311/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/8:ℝ) (225/256:ℝ) (130381348261662627095241/148673423925516220418560:ℝ) (4065399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1349).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^8*thetaFirstMode x) ≤ (1183232250121156489699201717/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/8:ℝ) (225/256:ℝ) (136283/3125000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_225 :
    (7086693791725932731077213/141670994486089356410880000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (225/256:ℝ) (113/128:ℝ) (135702249480635062632759/154054636064115110786560:ℝ) (353289/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1355).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^8*thetaFirstMode x) ≤ (2131006921011278343180510629/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (225/256:ℝ) (113/128:ℝ) (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_226 :
    (95598275868237761366461883/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (113/128:ℝ) (227/256:ℝ) (141215303034674977169457/159605509118049574428160:ℝ) (1533353/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1361).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^8*thetaFirstMode x) ≤ (638845094345535445368290653/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (113/128:ℝ) (227/256:ℝ) (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_227 :
    (14310591148947667268517127/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (227/256:ℝ) (57/64:ℝ) (29385310700934990796995/33066121515527560919552:ℝ) (664761/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1367).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^8*thetaFirstMode x) ≤ (19127143320778202261971929/472236648286964521369600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (227/256:ℝ) (57/64:ℝ) (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_228 :
    (1925519674698038846519807/53126622932283508654080000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (57/64:ℝ) (229/256:ℝ) (152842207727465608740993/171234597812449350300160:ℝ) (28787/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1373).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^8*thetaFirstMode x) ≤ (514739801592379846188689177/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (57/64:ℝ) (229/256:ℝ) (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_229 :
    (137998478110337427574167673/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (229/256:ℝ) (115/128:ℝ) (158968638409273606456191/177322249882403159887360:ℝ) (1992283/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1379).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^8*thetaFirstMode x) ≤ (3842911517158111771024037/118059162071741130342400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (229/256:ℝ) (115/128:ℝ) (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_230 :
    (10288756137061118492204131/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (115/128:ℝ) (231/256:ℝ) (165312387803273059105209/183598439372905969845760:ℝ) (430383/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1385).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^8*thetaFirstMode x) ≤ (1237800952351053626540594351/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (115/128:ℝ) (231/256:ℝ) (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_231 :
    (110317558452174212832183011/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (231/256:ℝ) (29/32:ℝ) (171880171452079192654407/190068149254242844572160:ℝ) (1485851/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1391).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^8*thetaFirstMode x) ≤ (553018052908783629418687729/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (231/256:ℝ) (29/32:ℝ) (40007/2500000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_232 :
    (19688018161004250775568627/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (29/32:ℝ) (233/256:ℝ) (35735776399208126994885/39347294353086520381952:ℝ) (256187/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1397).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^8*thetaFirstMode x) ≤ (98699547942859654872146239/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (29/32:ℝ) (233/256:ℝ) (690197/50000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_233 :
    (43862464413394365549257879/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (233/256:ℝ) (117/128:ℝ) (185715593048194171355943/203608610322761788188160:ℝ) (551489/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1403).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^8*thetaFirstMode x) ≤ (19546656977233196477931873/944473296573929042739200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (233/256:ℝ) (117/128:ℝ) (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_234 :
    (9758974247295896512939547/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (117/128:ℝ) (235/256:ℝ) (192997563136753342300641/210689881453211795484160:ℝ) (118577/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1409).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^8*thetaFirstMode x) ≤ (21745667176835891247537173/1180591620717411303424000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (117/128:ℝ) (235/256:ℝ) (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_235 :
    (23129221204869404624188807/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (235/256:ℝ) (59/64:ℝ) (200532239716009818864159/217985716752994642792960:ℝ) (814881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1415).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^8*thetaFirstMode x) ≤ (695796895868888525648633177/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (235/256:ℝ) (59/64:ℝ) (879727/100000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_236 :
    (12317235664310419181161291/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (59/64:ℝ) (237/256:ℝ) (208327263246534084091857/225501664871413871772160:ℝ) (139831/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1421).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^8*thetaFirstMode x) ≤ (12351881067583468870259809/850025966916536138465280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (59/64:ℝ) (237/256:ℝ) (3021/400000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_237 :
    (27293759244799259762320157/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (237/256:ℝ) (119/128:ℝ) (43278094269113915002275/46648678704053587338752:ℝ) (299567/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1427).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^8*thetaFirstMode x) ≤ (13685897739358717144778417/1062532458645670173081600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (237/256:ℝ) (119/128:ℝ) (1619/250000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_238 :
    (5368673215667622386702047/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (119/128:ℝ) (239/256:ℝ) (224729903008522098228393/241216691509014397212160:ℝ) (512793/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1433).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^8*thetaFirstMode x) ≤ (53842756498615546043356171/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (119/128:ℝ) (239/256:ℝ) (69327/12500000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_239 :
    (42709875043040971119208673/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (239/256:ℝ) (15/16:ℝ) (233353802902454023413591/249427470805914151528960:ℝ) (438353/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1439).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^8*thetaFirstMode x) ≤ (53545015218666177060418459/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (239/256:ℝ) (15/16:ℝ) (474399/100000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_240 :
    (9425074967928141849114443/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (15/16:ℝ) (241/256:ℝ) (242270625732500482869609/257881768625375876508160:ℝ) (93563/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1445).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x) ≤ (37813538670910047007342709/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (15/16:ℝ) (241/256:ℝ) (405281/100000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_241 :
    (8307999095385978341314091/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (241/256:ℝ) (121/128:ℝ) (251489040682132561926807/266585749541721770268160:ℝ) (79781/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1451).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x) ≤ (111111543892347328198138193/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (241/256:ℝ) (121/128:ℝ) (345801/100000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_242 :
    (3250255364566769213663087/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (121/128:ℝ) (243/256:ℝ) (52203587185640050827165/55109141525919324349952:ℝ) (271773/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1457).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x) ≤ (58686039553647261229016393/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (121/128:ℝ) (243/256:ℝ) (147339/50000000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_243 :
    (1607048549810769509022467/265633114661417543270400000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (243/256:ℝ) (61/64:ℝ) (270866423231695777103343/284768068631243160732160:ℝ) (14447/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1463).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x) ≤ (257939247446234002886686777/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (243/256:ℝ) (61/64:ℝ) (50159/20000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_244 :
    (22569580432896483743248171/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (61/64:ℝ) (245/256:ℝ) (281043842605185699355041/294259392150867570741760:ℝ) (196351/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1469).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x) ≤ (28302375666979114347853091/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (61/64:ℝ) (245/256:ℝ) (106587/50000000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_245 :
    (19782259834257909143534863/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (245/256:ℝ) (123/128:ℝ) (291559767057868215806559/304026373876319976271360:ℝ) (166573/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1475).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x) ≤ (198467119166930601666213533/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (245/256:ℝ) (123/128:ℝ) (90481/50000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_246 :
    (2885694537800707921481431/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (123/128:ℝ) (247/256:ℝ) (302424007419219829279257/314075847828315644700160:ℝ) (70563/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1481).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x) ≤ (21714539374072463453361907/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (123/128:ℝ) (247/256:ℝ) (153419/100000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_247 :
    (1513217574656044873659661/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (247/256:ℝ) (31/32:ℝ) (62729323448440729602555/64882957727484714455552:ℝ) (11941/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1487).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x) ≤ (3374039534198870467971537/944473296573929042739200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (247/256:ℝ) (31/32:ℝ) (129897/100000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_248 :
    (2200992628124794817589737/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (31/32:ℝ) (249/256:ℝ) (325237897787019494300793/335050313849050052508160:ℝ) (50451/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1493).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x) ≤ (66255652004890550933604421/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (31/32:ℝ) (249/256:ℝ) (27459/25000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_249 :
    (2876985332556725847875537/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (249/256:ℝ) (125/128:ℝ) (337208403086384037209991/345989686256645754242560:ℝ) (21287/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1499).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x) ≤ (115480367327980191763807967/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (249/256:ℝ) (125/128:ℝ) (371/400000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_250 :
    (5006806760630195433513629/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (125/128:ℝ) (251/256:ℝ) (349568945093337212835009/357240316263365765762560:ℝ) (35879/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1505).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x) ≤ (20098018224694386108293213/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (125/128:ℝ) (251/256:ℝ) (78217/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_251 :
    (8700308778974723783446051/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (251/256:ℝ) (63/64:ℝ) (362330598912579278694207/368809764272412990108160:ℝ) (60391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1511).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x) ≤ (10914507502335240507632767/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (251/256:ℝ) (63/64:ℝ) (4117/6250000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_252 :
    (1509587499325004994478571/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (63/64:ℝ) (253/256:ℝ) (75100941623270192936445/76141148621259241175552:ℝ) (10151/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1517).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x) ≤ (15151219700805374457447469/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (63/64:ℝ) (253/256:ℝ) (277/500000000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_253 :
    (3269197824053144940108089/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (253/256:ℝ) (127/128:ℝ) (389102890145877331465743/392936120455235036700160:ℝ) (21299/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1523).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x) ≤ (525021147667962065128073/340010386766614455386112000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (253/256:ℝ) (127/128:ℝ) (46529/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_254 :
    (2827632716838720008864581/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (127/128:ℝ) (255/256:ℝ) (403137041799404128338441/405508921354945001551360:ℝ) (17851/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1529).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x) ≤ (567671188203114452358011/425012983458268069232640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (127/128:ℝ) (255/256:ℝ) (2439/6250000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_255 :
    (4884053309948637515215801/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (255/256:ℝ) (1/1:ℝ) (417619344807863656339959/418432330694036747061760:ℝ) (29881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1535).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x) ≤ (12257143957794075144345077/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (255/256:ℝ) (1/1:ℝ) (8171/25000000000000:ℝ) (3417/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
