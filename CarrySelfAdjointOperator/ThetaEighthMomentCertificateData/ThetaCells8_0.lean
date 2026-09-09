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

theorem thetaFirstMode_refined_cell_lower_8_000 :
    (176420311451/88544371553805847756800000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (0/1:ℝ) (1/256:ℝ) (9/2560:ℝ) (529260934353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0005).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x) ≤ (42341536839263/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (0/1:ℝ) (1/256:ℝ) (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_001 :
    (4238982053351213/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/256:ℝ) (1/128:ℝ) (9207/1308160:ℝ) (8295463900883/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0011).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x) ≤ (5652130811383/5666839779443574256435200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/256:ℝ) (1/128:ℝ) (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_002 :
    (77845172001476059/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/128:ℝ) (3/256:ℝ) (104445/9815552:ℝ) (4060569193129/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0017).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x) ≤ (51898590062623709/1416709944860893564108800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/128:ℝ) (3/256:ℝ) (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_003 :
    (642052741209937897/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/256:ℝ) (1/64:ℝ) (8905743/620700160:ℝ) (7944198133431/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0023).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x) ≤ (1284155665433600197/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/256:ℝ) (1/64:ℝ) (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_004 :
    (656654424096565033/212506491729134034616320000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/64:ℝ) (5/256:ℝ) (78453441/4328911360:ℝ) (388327499893/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0029).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x) ≤ (5253454774688122367/1700051933833072276930560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/64:ℝ) (5/256:ℝ) (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_005 :
    (20554078120615099697/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/256:ℝ) (3/128:ℝ) (456304959/20798901760:ℝ) (7589598806121/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0035).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x) ≤ (102774884142794459567/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/256:ℝ) (3/128:ℝ) (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_006 :
    (37411594597673872859/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/128:ℝ) (7/256:ℝ) (1998081657/77506332160:ℝ) (3707065455207/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0041).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x) ≤ (748265809536579058429/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/128:ℝ) (7/256:ℝ) (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_007 :
    (679631234147504776709/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/256:ℝ) (1/32:ℝ) (1424279835/48058429952:ℝ) (7240585933229/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0047).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x) ≤ (339831502800724910989/2125064917291340346163200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/256:ℝ) (1/32:ℝ) (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_008 :
    (1789946000130064654087/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/32:ℝ) (9/256:ℝ) (21717383193/648199068160:ℝ) (7069219913167/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0053).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x) ≤ (8950160143048291107523/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/32:ℝ) (9/256:ℝ) (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_009 :
    (1056728496455581269781/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (9/256:ℝ) (5/128:ℝ) (58618940391/1568203548160:ℝ) (1725047079571/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0059).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x) ≤ (21135612247862452053181/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (9/256:ℝ) (5/128:ℝ) (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_010 :
    (3047953739642026867819/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/128:ℝ) (11/256:ℝ) (143436821409/3476346088960:ℝ) (6733588693827/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0065).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x) ≤ (91443233779256805154333/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/128:ℝ) (11/256:ℝ) (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_011 :
    (18406593488541629440141/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (11/256:ℝ) (3/64:ℝ) (323819456607/7172691612160:ℝ) (6569483518681/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0071).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x) ≤ (15339621737625726996091/3541774862152233910272000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (11/256:ℝ) (3/64:ℝ) (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_012 :
    (5814881003293076074829/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/64:ℝ) (13/256:ℝ) (136694029725/2787696138752:ℝ) (3203956520547/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0077).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x) ≤ (23260755799742646165607/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/64:ℝ) (13/256:ℝ) (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_013 :
    (62842387392421294202713/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (13/256:ℝ) (7/128:ℝ) (1362565468143/25744761372160:ℝ) (6248902811683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0083).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x) ≤ (314228956617314525808143/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (13/256:ℝ) (7/128:ℝ) (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_014 :
    (36112725156167153079607/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/128:ℝ) (15/256:ℝ) (2586561620841/45522720232960:ℝ) (6092468283531/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0089).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x) ≤ (270860438423535127431733/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/128:ℝ) (15/256:ℝ) (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_015 :
    (9988793728619027024941/236118324143482260684800000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (15/256:ℝ) (1/16:ℝ) (4705751134359/77506860444160:ℝ) (2969308861029/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0095).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x) ≤ (1798084649661640553211571/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (15/256:ℝ) (1/16:ℝ) (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_016 :
    (19240405870159458331541/283341988972178712821760000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/16:ℝ) (17/256:ℝ) (8248340454057/127663103388160:ℝ) (1157470820943/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0101).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^8*thetaFirstMode x) ≤ (80172995230504567185703/1180591620717411303424000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/16:ℝ) (17/256:ℝ) (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_017 :
    (449805188501943025878271/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (17/256:ℝ) (9/128:ℝ) (2798051987115/40842963901952:ℝ) (5638676396401/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0107).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^8*thetaFirstMode x) ≤ (299887848230154348991057/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (17/256:ℝ) (9/128:ℝ) (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_018 :
    (170720944295154948236191/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (9/128:ℝ) (19/256:ℝ) (23045391280593/318280722972160:ℝ) (1373145106981/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0113).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^8*thetaFirstMode x) ≤ (2276416681440463290804323/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (9/128:ℝ) (19/256:ℝ) (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_019 :
    (22503172699808522359841/94447329657392904273920000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (19/256:ℝ) (5/64:ℝ) (36980403679791/484639493685760:ℝ) (1069811902989/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0119).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^8*thetaFirstMode x) ≤ (10127052130732686269048563/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (19/256:ℝ) (5/64:ℝ) (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_020 :
    (19601921265049113729739/56668397794435742564352000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/64:ℝ) (21/256:ℝ) (57958928803809/722636919247360:ℝ) (208324196157/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0125).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^8*thetaFirstMode x) ≤ (7351183356861757758000883/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/64:ℝ) (21/256:ℝ) (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_021 :
    (1046866860170730915054791/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (21/256:ℝ) (11/128:ℝ) (88920376319007/1057252278300160:ℝ) (2534853049781/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0131).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^8*thetaFirstMode x) ≤ (1046934174023075921787043/2125064917291340346163200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (21/256:ℝ) (11/128:ℝ) (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_022 :
    (244177707316472313656741/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (11/128:ℝ) (23/256:ℝ) (26759859160005/304068323159552:ℝ) (1233462777513/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0137).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^8*thetaFirstMode x) ≤ (81397912578040055593627/118059162071741130342400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (11/128:ℝ) (23/256:ℝ) (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_023 :
    (1345195378557199866630857/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (23/256:ℝ) (3/32:ℝ) (197791827765543/2152076489628160:ℝ) (4800526634211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0143).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^8*thetaFirstMode x) ≤ (1345285537214945243121359/1416709944860893564108800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (23/256:ℝ) (3/32:ℝ) (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_024 :
    (304281361397448187718661/236118324143482260684800000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/32:ℝ) (25/256:ℝ) (287676456077241/3002597697026560:ℝ) (2334859103349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0149).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^8*thetaFirstMode x) ≤ (3043021795022719077667397/2361183241434822606848000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/32:ℝ) (25/256:ℝ) (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_025 :
    (305562437459962436818157/177088743107611695513600000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (25/256:ℝ) (13/128:ℝ) (412196976114759/4133904418178560:ℝ) (567676289121/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0155).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^8*thetaFirstMode x) ≤ (73340106333828238166141167/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (25/256:ℝ) (13/128:ℝ) (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_026 :
    (3232347374092411318484083/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (13/128:ℝ) (27/256:ℝ) (582516327971457/5622000143388160:ℝ) (4415586481659/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0161).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^8*thetaFirstMode x) ≤ (10775259212256934294431119/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (13/128:ℝ) (27/256:ℝ) (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_027 :
    (396073306722520475670131/132816557330708771635200000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (27/256:ℝ) (7/64:ℝ) (162550142281395/1511863535831552:ℝ) (134132167511/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0167).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^8*thetaFirstMode x) ≤ (2816726171078989858696417/944473296573929042739200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (27/256:ℝ) (7/64:ℝ) (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_028 :
    (16387826323806154600627771/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/64:ℝ) (29/256:ℝ) (1120594199442993/10057446457500160:ℝ) (4171320778711/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0173).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^8*thetaFirstMode x) ≤ (1280393970872968877131879/332041393326771929088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/64:ℝ) (29/256:ℝ) (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_029 :
    (874038231253726681510627/177088743107611695513600000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (29/256:ℝ) (15/128:ℝ) (1528044900298191/13250186301775360:ℝ) (506605225251/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0179).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^8*thetaFirstMode x) ≤ (104892532526120189169400807/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (29/256:ℝ) (15/128:ℝ) (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_030 :
    (26599286189584183226222911/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (15/128:ℝ) (31/256:ℝ) (2062244582827209/17296952731317760:ℝ) (3936772777441/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0185).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^8*thetaFirstMode x) ≤ (53202684058240893716738017/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (15/128:ℝ) (31/256:ℝ) (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_031 :
    (16715997756644201779403003/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (31/256:ℝ) (1/8:ℝ) (2756444578756407/22386559816092160:ℝ) (1911546687323/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0191).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^8*thetaFirstMode x) ≤ (334346318639199419361928283/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (31/256:ℝ) (1/8:ℝ) (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
