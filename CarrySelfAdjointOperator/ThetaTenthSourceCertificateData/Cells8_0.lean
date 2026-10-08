import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature0

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_000 :
    (1/1000000000000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (0/1:ℝ) (1/256:ℝ)
    (9/2560:ℝ) (529260934353/6250000000000:ℝ) (882017793809669459/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_000
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0005).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^8*thetaFirstMode x) ≤ (1/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (0/1:ℝ) (1/256:ℝ)
    (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ) (882017793809669459/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_001 :
    (997/1000000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/256:ℝ) (1/128:ℝ)
    (9207/1308160:ℝ) (8295463900883/100000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_001
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0011).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^8*thetaFirstMode x) ≤ (499/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/256:ℝ) (1/128:ℝ)
    (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_001 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_002 :
    (4579/125000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/128:ℝ) (3/256:ℝ)
    (104445/9815552:ℝ) (4060569193129/50000000000000:ℝ) (176197573183638029/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_002
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0017).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^8*thetaFirstMode x) ≤ (36633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/128:ℝ) (3/256:ℝ)
    (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (176197573183638029/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_002 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_003 :
    (113301/250000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/256:ℝ) (1/64:ℝ)
    (8905743/620700160:ℝ) (7944198133431/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_003
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0023).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^8*thetaFirstMode x) ≤ (226603/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/256:ℝ) (1/64:ℝ)
    (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_003 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_004 :
    (3090081/1000000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/64:ℝ) (5/256:ℝ)
    (78453441/4328911360:ℝ) (388327499893/5000000000000:ℝ) (351573408933338897/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_004
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0029).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^8*thetaFirstMode x) ≤ (386261/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/64:ℝ) (5/256:ℝ)
    (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ) (351573408933338897/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_004 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_005 :
    (3627127/250000000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (5/256:ℝ) (3/128:ℝ)
    (456304959/20798901760:ℝ) (7589598806121/100000000000000:ℝ) (219381292635168023/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_005
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0035).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^8*thetaFirstMode x) ≤ (7254269/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/256:ℝ) (3/128:ℝ)
    (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ) (219381292635168023/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_005 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_006 :
    (52815487/1000000000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/128:ℝ) (7/256:ℝ)
    (1998081657/77506332160:ℝ) (3707065455207/50000000000000:ℝ) (875864604429554181/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_006
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0041).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^8*thetaFirstMode x) ≤ (52815597/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/128:ℝ) (7/256:ℝ)
    (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_006 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_007 :
    (159910657/1000000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/256:ℝ) (1/32:ℝ)
    (1424279835/48058429952:ℝ) (7240585933229/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_007
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0047).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^8*thetaFirstMode x) ≤ (159910993/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/256:ℝ) (1/32:ℝ)
    (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_007 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_008 :
    (210578599/500000000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/32:ℝ) (9/256:ℝ)
    (21717383193/648199068160:ℝ) (7069219913167/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_008
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0053).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^8*thetaFirstMode x) ≤ (421158099/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/32:ℝ) (9/256:ℝ)
    (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_008 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_009 :
    (198910591/200000000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (9/256:ℝ) (5/128:ℝ)
    (58618940391/1568203548160:ℝ) (1725047079571/25000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_009
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0059).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^8*thetaFirstMode x) ≤ (12431939/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/256:ℝ) (5/128:ℝ)
    (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_009 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_010 :
    (2151465167/1000000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (5/128:ℝ) (11/256:ℝ)
    (143436821409/3476346088960:ℝ) (6733588693827/100000000000000:ℝ) (433367564585813153/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_010
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0065).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^8*thetaFirstMode x) ≤ (2151469933/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/128:ℝ) (11/256:ℝ)
    (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ) (433367564585813153/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_010 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_011 :
    (2165450713/500000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (11/256:ℝ) (3/64:ℝ)
    (323819456607/7172691612160:ℝ) (6569483518681/100000000000000:ℝ) (107980133847500327/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_011
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0071).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^8*thetaFirstMode x) ≤ (1082727797/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/256:ℝ) (3/64:ℝ)
    (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_011 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_012 :
    (256535317/31250000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/64:ℝ) (13/256:ℝ)
    (136694029725/2787696138752:ℝ) (3203956520547/50000000000000:ℝ) (430353464465377497/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_012
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0077).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^8*thetaFirstMode x) ≤ (8209148969/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/64:ℝ) (13/256:ℝ)
    (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ) (430353464465377497/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_012 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_013 :
    (14786245513/1000000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (13/256:ℝ) (7/128:ℝ)
    (1362565468143/25744761372160:ℝ) (6248902811683/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_013
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0083).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^8*thetaFirstMode x) ≤ (14786280007/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/256:ℝ) (7/128:ℝ)
    (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_013 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_014 :
    (12745501749/500000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/128:ℝ) (15/256:ℝ)
    (2586561620841/45522720232960:ℝ) (6092468283531/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_014
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0089).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^8*thetaFirstMode x) ≤ (25491063987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/128:ℝ) (15/256:ℝ)
    (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_014 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_015 :
    (1322029557/31250000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (15/256:ℝ) (1/16:ℝ)
    (4705751134359/77506860444160:ℝ) (2969308861029/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_015
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0095).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^8*thetaFirstMode x) ≤ (42305047933/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/256:ℝ) (1/16:ℝ)
    (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_015 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_016 :
    (67906486431/1000000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/16:ℝ) (17/256:ℝ)
    (8248340454057/127663103388160:ℝ) (1157470820943/20000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_016
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0101).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^8*thetaFirstMode x) ≤ (3395332657/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/16:ℝ) (17/256:ℝ)
    (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_016 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_017 :
    (105835267707/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (17/256:ℝ) (9/128:ℝ)
    (2798051987115/40842963901952:ℝ) (5638676396401/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_017
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0107).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^8*thetaFirstMode x) ≤ (52917765989/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (17/256:ℝ) (9/128:ℝ)
    (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_017 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_018 :
    (160676709511/1000000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (9/128:ℝ) (19/256:ℝ)
    (23045391280593/318280722972160:ℝ) (1373145106981/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_018
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0113).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^8*thetaFirstMode x) ≤ (160677117591/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/128:ℝ) (19/256:ℝ)
    (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_018 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_019 :
    (23826627999/100000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (19/256:ℝ) (5/64:ℝ)
    (36980403679791/484639493685760:ℝ) (1069811902989/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_019
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0119).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^8*thetaFirstMode x) ≤ (238266895501/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (19/256:ℝ) (5/64:ℝ)
    (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_019 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_020 :
    (345912620287/1000000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (5/64:ℝ) (21/256:ℝ)
    (57958928803809/722636919247360:ℝ) (208324196157/4000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_020
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0125).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^8*thetaFirstMode x) ≤ (172956764609/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/64:ℝ) (21/256:ℝ)
    (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_020 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_021 :
    (492638261823/1000000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (21/256:ℝ) (11/128:ℝ)
    (88920376319007/1057252278300160:ℝ) (2534853049781/50000000000000:ℝ) (12846388361106899/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_021
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0131).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^8*thetaFirstMode x) ≤ (61579947319/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (21/256:ℝ) (11/128:ℝ)
    (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (12846388361106899/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_021 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_022 :
    (689436291013/1000000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (11/128:ℝ) (23/256:ℝ)
    (26759859160005/304068323159552:ℝ) (1233462777513/25000000000000:ℝ) (326719829522905161/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_022
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0137).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^8*thetaFirstMode x) ≤ (344719082747/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/128:ℝ) (23/256:ℝ)
    (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (326719829522905161/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_022 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_023 :
    (949540947503/1000000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (23/256:ℝ) (3/32:ℝ)
    (197791827765543/2152076489628160:ℝ) (4800526634211/100000000000000:ℝ) (64898119919301951/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_023
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0143).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^8*thetaFirstMode x) ≤ (237385893437/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (23/256:ℝ) (3/32:ℝ)
    (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_023 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_024 :
    (644354896659/500000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/32:ℝ) (25/256:ℝ)
    (287676456077241/3002597697026560:ℝ) (2334859103349/50000000000000:ℝ) (805453755869069143/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_024
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0149).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^8*thetaFirstMode x) ≤ (1288713419329/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/32:ℝ) (25/256:ℝ)
    (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ) (805453755869069143/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_024 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_025 :
    (1725514766431/1000000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (25/256:ℝ) (13/128:ℝ)
    (412196976114759/4133904418178560:ℝ) (567676289121/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_025
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0155).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^8*thetaFirstMode x) ≤ (1725519705707/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (25/256:ℝ) (13/128:ℝ)
    (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_025 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_026 :
    (2281639137/1000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (13/128:ℝ) (27/256:ℝ)
    (582516327971457/5622000143388160:ℝ) (4415586481659/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_026
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0161).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^8*thetaFirstMode x) ≤ (2281645781793/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/128:ℝ) (27/256:ℝ)
    (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_026 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_027 :
    (2982177121887/1000000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (27/256:ℝ) (7/64:ℝ)
    (162550142281395/1511863535831552:ℝ) (134132167511/3125000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_027
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0167).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^8*thetaFirstMode x) ≤ (2982185958339/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (27/256:ℝ) (7/64:ℝ)
    (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_027 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_028 :
    (192796634289/50000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/64:ℝ) (29/256:ℝ)
    (1120594199442993/10057446457500160:ℝ) (4171320778711/100000000000000:ℝ) (97556613961683183/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_028
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0173).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^8*thetaFirstMode x) ≤ (96398607777/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/64:ℝ) (29/256:ℝ)
    (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ) (97556613961683183/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_028 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_029 :
    (4935713868137/1000000000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (29/256:ℝ) (15/128:ℝ)
    (1528044900298191/13250186301775360:ℝ) (506605225251/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_029
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0179).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^8*thetaFirstMode x) ≤ (4935729009883/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/256:ℝ) (15/128:ℝ)
    (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_029 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_030 :
    (1251723765319/200000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (15/128:ℝ) (31/256:ℝ)
    (2062244582827209/17296952731317760:ℝ) (3936772777441/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_030
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0185).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^8*thetaFirstMode x) ≤ (6258638364433/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/128:ℝ) (31/256:ℝ)
    (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_030 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_031 :
    (7866309680319/1000000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (31/256:ℝ) (1/8:ℝ)
    (2756444578756407/22386559816092160:ℝ) (1911546687323/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_031
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0191).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^8*thetaFirstMode x) ≤ (3933167335063/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/256:ℝ) (1/8:ℝ)
    (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_031 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
