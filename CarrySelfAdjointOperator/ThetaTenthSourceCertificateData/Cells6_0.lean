import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature0

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_000 :
    (8399/50000000000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (0/1:ℝ) (1/256:ℝ)
    (7/2048:ℝ) (847299499563/10000000000000:ℝ) (882017793809669459/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_000
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0004).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^6*thetaFirstMode x) ≤ (83991/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (0/1:ℝ) (1/256:ℝ)
    (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ) (882017793809669459/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_001 :
    (10454097/500000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/256:ℝ) (1/128:ℝ)
    (1785/260096:ℝ) (8304005063483/100000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_001
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0010).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^6*thetaFirstMode x) ≤ (20908231/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/256:ℝ) (1/128:ℝ)
    (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_001 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_002 :
    (331854779/1000000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/128:ℝ) (3/256:ℝ)
    (44135/4216832:ℝ) (8129522400843/100000000000000:ℝ) (176197573183638029/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_002
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0016).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^6*thetaFirstMode x) ≤ (331855393/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/128:ℝ) (3/256:ℝ)
    (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (176197573183638029/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_002 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_003 :
    (2238006703/1000000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/256:ℝ) (1/64:ℝ)
    (412825/29075456:ℝ) (7951285690833/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_003
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0022).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^6*thetaFirstMode x) ≤ (1119005509/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/256:ℝ) (1/64:ℝ)
    (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_003 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_004 :
    (4756960157/500000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/64:ℝ) (5/256:ℝ)
    (2275623/126445568:ℝ) (3886225298979/50000000000000:ℝ) (351573408933338897/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_004
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0028).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^6*thetaFirstMode x) ≤ (4756969593/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/64:ℝ) (5/256:ℝ)
    (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ) (351573408933338897/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_004 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_005 :
    (379827219/12500000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/256:ℝ) (3/128:ℝ)
    (9022937/413308928:ℝ) (949320948709/12500000000000:ℝ) (219381292635168023/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_005
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0034).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^6*thetaFirstMode x) ≤ (30386239181/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/256:ℝ) (3/128:ℝ)
    (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ) (219381292635168023/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_005 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_006 :
    (39975374769/500000000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/128:ℝ) (7/256:ℝ)
    (28596295/1113307136:ℝ) (3709189972931/50000000000000:ℝ) (875864604429554181/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_006
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0040).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^6*thetaFirstMode x) ≤ (39975457531/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/128:ℝ) (7/256:ℝ)
    (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_006 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_007 :
    (22864911089/125000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/256:ℝ) (1/32:ℝ)
    (77086905/2608351232:ℝ) (57954176141/800000000000:ℝ) (873953451803742743/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_007
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0046).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^6*thetaFirstMode x) ≤ (182919674539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/256:ℝ) (1/32:ℝ)
    (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_007 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_008 :
    (75319179999/200000000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/32:ℝ) (9/256:ℝ)
    (183886535/5500553216:ℝ) (7072457449143/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_008
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0052).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^6*thetaFirstMode x) ≤ (376596708653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/32:ℝ) (9/256:ℝ)
    (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_008 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_009 :
    (178498344643/250000000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (9/256:ℝ) (5/128:ℝ)
    (398672953/10684479488:ℝ) (6903061783463/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_009
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0058).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^6*thetaFirstMode x) ≤ (356997469321/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/256:ℝ) (5/128:ℝ)
    (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_009 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_010 :
    (633502617591/500000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/128:ℝ) (11/256:ℝ)
    (800512167/19429726208:ℝ) (1347232326663/20000000000000:ℝ) (433367564585813153/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_010
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0064).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^6*thetaFirstMode x) ≤ (126700805143/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/128:ℝ) (11/256:ℝ)
    (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ) (433367564585813153/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_010 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_011 :
    (2129557050631/1000000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (11/256:ℝ) (3/64:ℝ)
    (1509359705/33473816576:ℝ) (3285902331711/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_011
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0070).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^6*thetaFirstMode x) ≤ (2129561865163/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/256:ℝ) (3/64:ℝ)
    (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_011 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_012 :
    (3420667791109/1000000000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/64:ℝ) (13/256:ℝ)
    (2700243175/55125420032:ℝ) (50078284763/781250000000:ℝ) (430353464465377497/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_012
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0076).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^6*thetaFirstMode x) ≤ (3420675656233/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/64:ℝ) (13/256:ℝ)
    (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ) (430353464465377497/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_012 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_013 :
    (528735866151/100000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (13/256:ℝ) (7/128:ℝ)
    (4620408345/87377893376:ℝ) (6250826706611/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_013
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0082).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^6*thetaFirstMode x) ≤ (2643685512483/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/256:ℝ) (7/128:ℝ)
    (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_013 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_014 :
    (1976838465367/250000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/128:ℝ) (15/256:ℝ)
    (7609710983/134033143808:ℝ) (1218846605409/20000000000000:ℝ) (106716101744309517/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_014
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0088).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^6*thetaFirstMode x) ≤ (3953686332271/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/128:ℝ) (15/256:ℝ)
    (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_014 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_015 :
    (5745762112287/500000000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (15/256:ℝ) (1/16:ℝ)
    (12124536697/199835813888:ℝ) (371265201129/6250000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_015
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0094).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^6*thetaFirstMode x) ≤ (11491552013401/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (15/256:ℝ) (1/16:ℝ)
    (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_015 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_016 :
    (4071507788089/250000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/16:ℝ) (17/256:ℝ)
    (18765531015/290617788416:ℝ) (5788856811631/100000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_016
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0100).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^6*thetaFirstMode x) ≤ (2035758900349/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/16:ℝ) (17/256:ℝ)
    (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_016 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_017 :
    (22574134489509/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (17/256:ℝ) (9/128:ℝ)
    (28309421945/413453023232:ℝ) (5640070071609/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_017
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0106).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^6*thetaFirstMode x) ≤ (22574190945633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (17/256:ℝ) (9/128:ℝ)
    (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_017 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_018 :
    (15338817006287/500000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (9/128:ℝ) (19/256:ℝ)
    (41745217255/576822695936:ℝ) (2746938341771/50000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_018
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0112).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^6*thetaFirstMode x) ≤ (7669428009793/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/128:ℝ) (19/256:ℝ)
    (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_018 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_019 :
    (40957920012733/1000000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (19/256:ℝ) (5/64:ℝ)
    (60315058713/790790678528:ℝ) (5350268239193/100000000000000:ℝ) (832280181221222783/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_019
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0118).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^6*thetaFirstMode x) ≤ (20479012980527/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/256:ℝ) (5/64:ℝ)
    (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_019 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_020 :
    (53816614029123/1000000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/64:ℝ) (21/256:ℝ)
    (85560015527/1067189331968:ℝ) (2604617292273/50000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_020
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0124).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^6*thetaFirstMode x) ≤ (26908377808227/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/64:ℝ) (21/256:ℝ)
    (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_020 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_021 :
    (69695786130707/1000000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (21/256:ℝ) (11/128:ℝ)
    (119371099225/1419815622656:ℝ) (2535382037707/50000000000000:ℝ) (12846388361106899/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_021
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0130).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^6*thetaFirstMode x) ≤ (69695972633053/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (21/256:ℝ) (11/128:ℝ)
    (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (12846388361106899/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_021 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_022 :
    (44538870117421/500000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (11/128:ℝ) (23/256:ℝ)
    (164045782215/1864637560832:ℝ) (4934843768989/100000000000000:ℝ) (326719829522905161/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_022
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0136).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^6*thetaFirstMode x) ≤ (89077982692661/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/128:ℝ) (23/256:ℝ)
    (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (326719829522905161/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_022 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_023 :
    (2812109094711/25000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (23/256:ℝ) (3/32:ℝ)
    (222350302265/2420010960896:ℝ) (150045611573/3125000000000:ℝ) (64898119919301951/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_023
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0142).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^6*thetaFirstMode x) ≤ (112484675224073/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (23/256:ℝ) (3/32:ℝ)
    (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_023 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_024 :
    (140476042710137/1000000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/32:ℝ) (25/256:ℝ)
    (297588035143/3106906523648:ℝ) (2335298173297/50000000000000:ℝ) (805453755869069143/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_024
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0148).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^6*thetaFirstMode x) ≤ (70238219178483/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/32:ℝ) (25/256:ℝ)
    (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ) (805453755869069143/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_024 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_025 :
    (173650146799971/1000000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (25/256:ℝ) (13/128:ℝ)
    (393674217657/3949147240448:ℝ) (181689520713/4000000000000:ℝ) (799485594891087013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_025
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0154).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^6*thetaFirstMode x) ≤ (34730128868747/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (25/256:ℝ) (13/128:ℝ)
    (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_025 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_026 :
    (340222551773/1600000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (13/128:ℝ) (27/256:ℝ)
    (515217303335/4973656119296:ℝ) (4416367630773/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_026
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0160).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^6*thetaFirstMode x) ≤ (212639714685787/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/128:ℝ) (27/256:ℝ)
    (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_026 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_027 :
    (51621602499141/200000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (27/256:ℝ) (7/64:ℝ)
    (667607232985/6210714232832:ℝ) (536620927461/12500000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_027
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0166).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^6*thetaFirstMode x) ≤ (258108777957173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (27/256:ℝ) (7/64:ℝ)
    (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_027 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_028 :
    (310751999117593/1000000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/64:ℝ) (29/256:ℝ)
    (857110902375/7694229088256:ℝ) (2086009428901/50000000000000:ℝ) (97556613961683183/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_028
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0172).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^6*thetaFirstMode x) ≤ (38844117098971/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/64:ℝ) (29/256:ℝ)
    (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ) (97556613961683183/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_028 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_029 :
    (5801453495563/15625000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (29/256:ℝ) (15/128:ℝ)
    (1090975109273/9462013319168:ℝ) (2026751350699/50000000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_029
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0178).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^6*thetaFirstMode x) ≤ (185647081842963/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (29/256:ℝ) (15/128:ℝ)
    (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_029 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_030 :
    (440476472046117/1000000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (15/128:ℝ) (31/256:ℝ)
    (1377537262087/11556073699328:ℝ) (3937399028481/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_030
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0184).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^6*thetaFirstMode x) ≤ (88095569635329/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (15/128:ℝ) (31/256:ℝ)
    (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_030 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_031 :
    (129766842584483/250000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (31/256:ℝ) (1/8:ℝ)
    (1726344132345/14022910478336:ℝ) (3823687273083/100000000000000:ℝ) (759825734717146723/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_031
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0190).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^6*thetaFirstMode x) ≤ (519069020566093/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (31/256:ℝ) (1/8:ℝ)
    (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_031 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
