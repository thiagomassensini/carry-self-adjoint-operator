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

theorem thetaFirstMode_refined_cell_lower_6_000 :
    (847299499563/5044031582654955520000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (0/1:ℝ) (1/256:ℝ) (7/2048:ℝ) (847299499563/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0004).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^6*thetaFirstMode x) ≤ (33892616352937/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (0/1:ℝ) (1/256:ℝ) (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_001 :
    (1054608643062341/50440315826549555200000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/256:ℝ) (1/128:ℝ) (1785/260096:ℝ) (8304005063483/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0010).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^6*thetaFirstMode x) ≤ (131830233513039/6305039478318694400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/256:ℝ) (1/128:ℝ) (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_002 :
    (16738686623335737/50440315826549555200000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/128:ℝ) (3/256:ℝ) (44135/4216832:ℝ) (8129522400843/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0016).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^6*thetaFirstMode x) ≤ (66957281656365547/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/128:ℝ) (3/256:ℝ) (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_003 :
    (112884402952756101/50440315826549555200000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/256:ℝ) (1/64:ℝ) (412825/29075456:ℝ) (7951285690833/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0022).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^6*thetaFirstMode x) ≤ (129016046251759189/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/256:ℝ) (1/64:ℝ) (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_004 :
    (239939436184262439/25220157913274777600000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/64:ℝ) (5/256:ℝ) (2275623/126445568:ℝ) (3886225298979/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0028).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^6*thetaFirstMode x) ≤ (3839196589340041639/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/64:ℝ) (5/256:ℝ) (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_005 :
    (27369058568558857/900719925474099200000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/256:ℝ) (3/128:ℝ) (9022937/413308928:ℝ) (949320948709/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0034).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^6*thetaFirstMode x) ≤ (1226188654895065101/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/256:ℝ) (3/128:ℝ) (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_006 :
    (2016341633615102117/25220157913274777600000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/128:ℝ) (7/256:ℝ) (28596295/1113307136:ℝ) (3709189972931/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0040).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^6*thetaFirstMode x) ≤ (1290518109680813577/16140901064495857664000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/128:ℝ) (7/256:ℝ) (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_007 :
    (73810960320762869/403522526612396441600000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/256:ℝ) (1/32:ℝ) (77086905/2608351232:ℝ) (57954176141/800000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0046).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^6*thetaFirstMode x) ≤ (36907227013966860293/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/256:ℝ) (1/32:ℝ) (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_008 :
    (18995326448684904831/50440315826549555200000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/32:ℝ) (9/256:ℝ) (183886535/5500553216:ℝ) (7072457449143/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0052).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^6*thetaFirstMode x) ≤ (18996248329577993601/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/32:ℝ) (9/256:ℝ) (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_009 :
    (36013487319241758353/50440315826549555200000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (9/256:ℝ) (5/128:ℝ) (398672953/10684479488:ℝ) (6903061783463/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0058).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^6*thetaFirstMode x) ≤ (7203055470567636499/10088063165309911040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/256:ℝ) (5/128:ℝ) (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_010 :
    (12781423459779740373/10088063165309911040000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/128:ℝ) (11/256:ℝ) (800512167/19429726208:ℝ) (1347232326663/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0064).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^6*thetaFirstMode x) ≤ (511282944446826917153/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/128:ℝ) (11/256:ℝ) (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_011 :
    (53706880829269883907/25220157913274777600000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (11/256:ℝ) (3/64:ℝ) (1509359705/33473816576:ℝ) (3285902331711/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0070).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^6*thetaFirstMode x) ≤ (107419350271336131153/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/256:ℝ) (3/64:ℝ) (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_012 :
    (1347942618184804967/394064967394918400000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/64:ℝ) (13/256:ℝ) (2700243175/55125420032:ℝ) (50078284763/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0076).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^6*thetaFirstMode x) ≤ (1380366667879718659811/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/64:ℝ) (13/256:ℝ) (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_013 :
    (266691440176811129057/50440315826549555200000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (13/256:ℝ) (7/128:ℝ) (4620408345/87377893376:ℝ) (6250826706611/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0082).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^6*thetaFirstMode x) ≤ (533411882663380048091/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/256:ℝ) (7/128:ℝ) (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_014 :
    (79768477706385316239/10088063165309911040000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/128:ℝ) (15/256:ℝ) (7609710983/134033143808:ℝ) (1218846605409/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0088).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^6*thetaFirstMode x) ≤ (1595458200708968295779/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/128:ℝ) (15/256:ℝ) (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_015 :
    (36226603337844595449/3152519739159347200000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (15/256:ℝ) (1/16:ℝ) (12124536697/199835813888:ℝ) (371265201129/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0094).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^6*thetaFirstMode x) ≤ (927453694591080165613/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/256:ℝ) (1/16:ℝ) (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_016 :
    (821457404322801916927/50440315826549555200000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/16:ℝ) (17/256:ℝ) (18765531015/290617788416:ℝ) (5788856811631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0100).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^6*thetaFirstMode x) ≤ (821505043138302905133/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/16:ℝ) (17/256:ℝ) (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_017 :
    (1138625010911652236631/50440315826549555200000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (17/256:ℝ) (9/128:ℝ) (28309421945/413453023232:ℝ) (5640070071609/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0106).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^6*thetaFirstMode x) ≤ (1301362806392424422453/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/256:ℝ) (9/128:ℝ) (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_018 :
    (773679872983551553097/25220157913274777600000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (9/128:ℝ) (19/256:ℝ) (41745217255/576822695936:ℝ) (2746938341771/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0112).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^6*thetaFirstMode x) ≤ (2475925360366872035093/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/128:ℝ) (19/256:ℝ) (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_019 :
    (2065889771083125133373/50440315826549555200000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (19/256:ℝ) (5/64:ℝ) (60315058713/790790678528:ℝ) (5350268239193/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0118).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^6*thetaFirstMode x) ≤ (2361162726585424513877/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/256:ℝ) (5/64:ℝ) (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_020 :
    (1357236224693908143693/25220157913274777600000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/64:ℝ) (21/256:ℝ) (85560015527/1067189331968:ℝ) (2604617292273/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0124).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^6*thetaFirstMode x) ≤ (1357321828737506939073/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/64:ℝ) (21/256:ℝ) (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_021 :
    (1757702649676661267329/25220157913274777600000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (21/256:ℝ) (11/128:ℝ) (119371099225/1419815622656:ℝ) (2535382037707/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0130).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^6*thetaFirstMode x) ≤ (14062526678213062395217/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/256:ℝ) (11/128:ℝ) (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_022 :
    (4493015160397774727851/50440315826549555200000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (11/128:ℝ) (23/256:ℝ) (164045782215/1864637560832:ℝ) (4934843768989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0136).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^6*thetaFirstMode x) ≤ (17973242074953806906007/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/128:ℝ) (23/256:ℝ) (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_023 :
    (177300793281740091821/1576259869579673600000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (23/256:ℝ) (3/32:ℝ) (222350302265/2420010960896:ℝ) (150045611573/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0142).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^6*thetaFirstMode x) ≤ (2269602441516118789599/20176126330619822080000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/256:ℝ) (3/32:ℝ) (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_024 :
    (3542750551406106900697/25220157913274777600000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/32:ℝ) (25/256:ℝ) (297588035143/3106906523648:ℝ) (2335298173297/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0148).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^6*thetaFirstMode x) ≤ (14171972812053673647229/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/32:ℝ) (25/256:ℝ) (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_025 :
    (350350912764679534863/2017612633061982208000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (25/256:ℝ) (13/128:ℝ) (393674217657/3949147240448:ℝ) (181689520713/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0154).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^6*thetaFirstMode x) ≤ (70075080827708510168549/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/256:ℝ) (13/128:ℝ) (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_026 :
    (1532191259197468538553/7205759403792793600000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (13/128:ℝ) (27/256:ℝ) (515217303335/4973656119296:ℝ) (4416367630773/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0160).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^6*thetaFirstMode x) ≤ (85808831874629743063981/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/128:ℝ) (27/256:ℝ) (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_027 :
    (1627343374910908660449/6305039478318694400000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (27/256:ℝ) (7/64:ℝ) (667607232985/6210714232832:ℝ) (536620927461/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0166).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^6*thetaFirstMode x) ≤ (14879651217379204071169/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/256:ℝ) (7/64:ℝ) (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_028 :
    (7837028528430840081097/25220157913274777600000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/64:ℝ) (29/256:ℝ) (857110902375/7694229088256:ℝ) (2086009428901/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0172).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^6*thetaFirstMode x) ≤ (4478634712646192587963/14411518807585587200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/64:ℝ) (29/256:ℝ) (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_029 :
    (9363841931130699310009/25220157913274777600000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (29/256:ℝ) (15/128:ℝ) (1090975109273/9462013319168:ℝ) (2026751350699/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0178).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^6*thetaFirstMode x) ≤ (74916413922729805612597/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/256:ℝ) (15/128:ℝ) (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_030 :
    (22217223318744581495391/50440315826549555200000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (15/128:ℝ) (31/256:ℝ) (1377537262087/11556073699328:ℝ) (3937399028481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0184).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^6*thetaFirstMode x) ≤ (25393076157927307558801/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/128:ℝ) (31/256:ℝ) (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_031 :
    (26181261878708792474331/50440315826549555200000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (31/256:ℝ) (1/8:ℝ) (1726344132345/14022910478336:ℝ) (3823687273083/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0190).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^6*thetaFirstMode x) ≤ (41893324419372837090293/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/256:ℝ) (1/8:ℝ) (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
