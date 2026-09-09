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

theorem thetaFirstMode_refined_cell_lower_2_000 :
    (8497121034577/5033164800000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (0/1:ℝ) (1/256:ℝ) (3/1024:ℝ) (8497121034577/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0002).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^2*thetaFirstMode x) ≤ (3398955076057/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (0/1:ℝ) (1/256:ℝ) (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_001 :
    (19442614491587/1677721600000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/256:ℝ) (1/128:ℝ) (45/7168:ℝ) (8332549067823/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0008).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x) ≤ (9721700007257/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/256:ℝ) (1/128:ℝ) (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_002 :
    (10324452335667/335544320000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/128:ℝ) (3/256:ℝ) (195/19456:ℝ) (1630176684579/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0014).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^2*thetaFirstMode x) ≤ (103248907819097/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/128:ℝ) (3/256:ℝ) (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_003 :
    (294797646634367/5033164800000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/256:ℝ) (1/64:ℝ) (525/37888:ℝ) (7967503963091/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0020).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x) ≤ (393080724605793/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/256:ℝ) (1/64:ℝ) (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_004 :
    (79150492673481/838860800000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/64:ℝ) (5/256:ℝ) (1107/62464:ℝ) (3892647180663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0026).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^2*thetaFirstMode x) ≤ (1899697031826407/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/64:ℝ) (5/256:ℝ) (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_005 :
    (86507981773577/629145600000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/256:ℝ) (3/128:ℝ) (2013/93184:ℝ) (950637162347/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0032).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x) ≤ (461397085852691/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/256:ℝ) (3/128:ℝ) (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_006 :
    (943259794122689/5033164800000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/128:ℝ) (7/256:ℝ) (3315/130048:ℝ) (7427242473407/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0038).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^2*thetaFirstMode x) ≤ (251547756880907/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/128:ℝ) (7/256:ℝ) (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_007 :
    (1225568168959823/5033164800000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/256:ℝ) (1/32:ℝ) (5085/173056:ℝ) (7251882656567/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0044).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x) ≤ (2451254011207339/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/256:ℝ) (1/32:ℝ) (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_008 :
    (256027311698739/838860800000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/32:ℝ) (9/256:ℝ) (7395/222208:ℝ) (3539548088001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0050).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^2*thetaFirstMode x) ≤ (1536239244780371/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/32:ℝ) (9/256:ℝ) (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_009 :
    (624106259065513/1677721600000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/256:ℝ) (5/128:ℝ) (10317/277504:ℝ) (6908925377109/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0056).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x) ≤ (1872412654506629/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/256:ℝ) (5/128:ℝ) (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_010 :
    (5810940569721/13107200000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/128:ℝ) (11/256:ℝ) (13923/338944:ℝ) (52667135073/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0062).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^2*thetaFirstMode x) ≤ (8926061958468793/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/128:ℝ) (11/256:ℝ) (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_011 :
    (870291709194419/1677721600000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/256:ℝ) (3/64:ℝ) (18285/406528:ℝ) (6576511656381/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0068).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x) ≤ (217584313802479/419430400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/256:ℝ) (3/64:ℝ) (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_012 :
    (1002766576176757/1677721600000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/64:ℝ) (13/256:ℝ) (23475/480256:ℝ) (6414285135459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0074).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^2*thetaFirstMode x) ≤ (4011280729556221/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/64:ℝ) (13/256:ℝ) (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_013 :
    (1710664181053633/2516582400000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/256:ℝ) (7/128:ℝ) (29565/560128:ℝ) (3127356820939/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0080).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x) ≤ (1710757585694969/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/256:ℝ) (7/128:ℝ) (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_014 :
    (1923853921920377/2516582400000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/128:ℝ) (15/256:ℝ) (36627/646144:ℝ) (3048896865167/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0086).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^2*thetaFirstMode x) ≤ (1539168963017809/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/128:ℝ) (15/256:ℝ) (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_015 :
    (428527752107791/503316480000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/256:ℝ) (1/16:ℝ) (44733/738304:ℝ) (594351944671/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0092).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x) ≤ (17142086215303933/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/256:ℝ) (1/16:ℝ) (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_016 :
    (2365984154222629/2516582400000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/16:ℝ) (17/256:ℝ) (53955/836608:ℝ) (2895941437237/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0098).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^2*thetaFirstMode x) ≤ (98588405685291/104857600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/16:ℝ) (17/256:ℝ) (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_017 :
    (2592900831631577/2516582400000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/256:ℝ) (9/128:ℝ) (64365/941056:ℝ) (2821437248783/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0104).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x) ≤ (6914812756536601/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/256:ℝ) (9/128:ℝ) (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_018 :
    (2822444251175497/2516582400000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/128:ℝ) (19/256:ℝ) (76035/1051648:ℝ) (2748241724611/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0110).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^2*thetaFirstMode x) ≤ (1505394852525687/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/128:ℝ) (19/256:ℝ) (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_019 :
    (40716187079673/33554432000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/256:ℝ) (5/64:ℝ) (89037/1168384:ℝ) (107053953759/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0116).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x) ≤ (24431224152434131/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/256:ℝ) (5/64:ℝ) (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_020 :
    (1642926675510913/1258291200000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/64:ℝ) (21/256:ℝ) (103443/1291264:ℝ) (1302876031333/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0122).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^2*thetaFirstMode x) ≤ (6572121888694673/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/64:ℝ) (21/256:ℝ) (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_021 :
    (234536555232801/167772160000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/256:ℝ) (11/128:ℝ) (119325/1420288:ℝ) (507288872169/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0128).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x) ≤ (14073100837356391/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/256:ℝ) (11/128:ℝ) (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_022 :
    (2499684911295019/1677721600000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/128:ℝ) (23/256:ℝ) (136755/1555456:ℝ) (4936836559503/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0134).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^2*thetaFirstMode x) ≤ (4999698912475887/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/128:ℝ) (23/256:ℝ) (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_023 :
    (3979560480487199/2516582400000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/256:ℝ) (3/32:ℝ) (155805/1696768:ℝ) (2401665950807/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0140).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x) ≤ (2072827004809/1310720000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/256:ℝ) (3/32:ℝ) (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_024 :
    (1051864648403591/629145600000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/32:ℝ) (25/256:ℝ) (176547/1844224:ℝ) (584044779791/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0146).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^2*thetaFirstMode x) ≤ (1402582364411519/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/32:ℝ) (25/256:ℝ) (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_025 :
    (4432572817830469/2516582400000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/256:ℝ) (13/128:ℝ) (199053/1997824:ℝ) (2271949163419/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0152).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x) ≤ (35463063934043713/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/256:ℝ) (13/128:ℝ) (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_026 :
    (4654293705938471/2516582400000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/128:ℝ) (27/256:ℝ) (223395/2157568:ℝ) (2208967112453/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0158).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^2*thetaFirstMode x) ≤ (12412336161843331/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/128:ℝ) (27/256:ℝ) (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_027 :
    (3248033656747999/1677721600000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/256:ℝ) (7/64:ℝ) (249645/2323456:ℝ) (4294447320513/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0164).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x) ≤ (12993081305396233/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/256:ℝ) (7/64:ℝ) (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_028 :
    (3390206846441919/1677721600000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/64:ℝ) (29/256:ℝ) (277875/2495488:ℝ) (4173418358361/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0170).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^2*thetaFirstMode x) ≤ (10171376708343143/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/64:ℝ) (29/256:ℝ) (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_029 :
    (3529051503002641/1677721600000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/256:ℝ) (15/128:ℝ) (308157/2673664:ℝ) (4054827464193/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0176).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x) ≤ (21175915242482977/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/256:ℝ) (15/128:ℝ) (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_030 :
    (10992783781606931/5033164800000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/128:ℝ) (31/256:ℝ) (340563/2857984:ℝ) (3938654167541/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0182).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^2*thetaFirstMode x) ≤ (43974538163730731/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/128:ℝ) (31/256:ℝ) (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_031 :
    (11386660088535953/5033164800000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/256:ℝ) (1/8:ℝ) (375165/3048448:ℝ) (3824877423089/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0188).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x) ≤ (9110047295077153/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/256:ℝ) (1/8:ℝ) (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
