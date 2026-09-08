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

theorem thetaFirstMode_refined_cell_lower_0_000 :
    (8545502162793/25600000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (0/1:ℝ) (1/256:ℝ) (1/512:ℝ) (8545502162793/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0001).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x) ≤ (8545854893959/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (0/1:ℝ) (1/256:ℝ) (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_001 :
    (1044126246807/3200000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/256:ℝ) (1/128:ℝ) (3/512:ℝ) (1044126246807/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0007).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x) ≤ (4176681221943/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/256:ℝ) (1/128:ℝ) (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_002 :
    (408163493967/1280000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/128:ℝ) (3/256:ℝ) (5/512:ℝ) (408163493967/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0013).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x) ≤ (8163621987547/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/128:ℝ) (3/256:ℝ) (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_003 :
    (7976280005461/25600000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/256:ℝ) (1/64:ℝ) (7/512:ℝ) (7976280005461/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0019).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x) ≤ (15953263306771/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/256:ℝ) (1/64:ℝ) (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_004 :
    (7792037685867/25600000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/64:ℝ) (5/256:ℝ) (9/512:ℝ) (7792037685867/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0025).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x) ≤ (15584777549791/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/64:ℝ) (5/256:ℝ) (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_005 :
    (380526973097/1280000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/256:ℝ) (3/128:ℝ) (11/512:ℝ) (380526973097/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0031).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x) ≤ (7610889893997/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/256:ℝ) (3/128:ℝ) (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_006 :
    (7431781087363/25600000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/128:ℝ) (7/256:ℝ) (13/512:ℝ) (7431781087363/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0037).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x) ≤ (14864261529843/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/128:ℝ) (7/256:ℝ) (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_007 :
    (7255757532429/25600000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/256:ℝ) (1/32:ℝ) (15/512:ℝ) (7255757532429/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0043).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x) ≤ (3628053179299/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/256:ℝ) (1/32:ℝ) (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_008 :
    (1770615747231/6400000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/32:ℝ) (9/256:ℝ) (17/512:ℝ) (1770615747231/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0049).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x) ≤ (1416562173507/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/32:ℝ) (9/256:ℝ) (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_009 :
    (1382378175107/5120000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/256:ℝ) (5/128:ℝ) (19/512:ℝ) (1382378175107/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0055).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x) ≤ (6912237711167/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/256:ℝ) (5/128:ℝ) (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_010 :
    (6744033843673/25600000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/128:ℝ) (11/256:ℝ) (21/512:ℝ) (6744033843673/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0061).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x) ≤ (13488759083453/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/128:ℝ) (11/256:ℝ) (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_011 :
    (3289441891889/12800000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/256:ℝ) (3/64:ℝ) (23/512:ℝ) (3289441891889/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0067).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x) ≤ (3289614125289/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/256:ℝ) (3/64:ℝ) (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_012 :
    (3208215916119/12800000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/64:ℝ) (13/256:ℝ) (25/512:ℝ) (3208215916119/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0073).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x) ≤ (12833549950001/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/64:ℝ) (13/256:ℝ) (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_013 :
    (6256668378569/25600000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/256:ℝ) (7/128:ℝ) (27/512:ℝ) (6256668378569/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0079).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x) ≤ (6257010105541/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/256:ℝ) (7/128:ℝ) (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_014 :
    (1524895768329/6400000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/128:ℝ) (15/256:ℝ) (29/512:ℝ) (1524895768329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0085).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x) ≤ (381245205863/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/128:ℝ) (15/256:ℝ) (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_015 :
    (148629120907/640000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/256:ℝ) (1/16:ℝ) (31/512:ℝ) (148629120907/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0091).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x) ≤ (11891006921387/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/256:ℝ) (1/16:ℝ) (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_016 :
    (1448350466289/6400000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/16:ℝ) (17/256:ℝ) (33/512:ℝ) (1448350466289/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0097).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x) ≤ (579373880511/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/16:ℝ) (17/256:ℝ) (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_017 :
    (1411070411223/6400000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/256:ℝ) (9/128:ℝ) (35/512:ℝ) (1411070411223/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0103).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x) ≤ (11289233626391/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/256:ℝ) (9/128:ℝ) (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_018 :
    (2748895478593/12800000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/128:ℝ) (19/256:ℝ) (37/512:ℝ) (2748895478593/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0109).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x) ≤ (10996248535921/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/128:ℝ) (19/256:ℝ) (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_019 :
    (2676957945317/12800000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/256:ℝ) (5/64:ℝ) (39/512:ℝ) (2676957945317/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0115).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x) ≤ (10708494518747/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/256:ℝ) (5/64:ℝ) (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_020 :
    (1303160462837/6400000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/64:ℝ) (21/256:ℝ) (41/512:ℝ) (1303160462837/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0121).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x) ≤ (5212971194907/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/64:ℝ) (21/256:ℝ) (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_021 :
    (2536976786917/12800000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/256:ℝ) (11/128:ℝ) (43/512:ℝ) (2536976786917/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0127).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x) ≤ (1268570202631/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/256:ℝ) (11/128:ℝ) (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_022 :
    (1234458783113/6400000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/128:ℝ) (23/256:ℝ) (45/512:ℝ) (1234458783113/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0133).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x) ≤ (2469080091051/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/128:ℝ) (23/256:ℝ) (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_023 :
    (960853990651/5120000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/256:ℝ) (3/32:ℝ) (47/512:ℝ) (960853990651/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0139).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x) ≤ (960918547449/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/256:ℝ) (3/32:ℝ) (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_024 :
    (934648165241/5120000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/32:ℝ) (25/256:ℝ) (49/512:ℝ) (934648165241/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0145).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x) ≤ (4673561267513/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/32:ℝ) (25/256:ℝ) (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_025 :
    (1136182479459/6400000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/256:ℝ) (13/128:ℝ) (51/512:ℝ) (1136182479459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0151).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x) ≤ (1818019176439/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/256:ℝ) (13/128:ℝ) (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_026 :
    (4418718784289/25600000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/128:ℝ) (27/256:ℝ) (53/512:ℝ) (4418718784289/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0157).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x) ≤ (8838068631691/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/128:ℝ) (27/256:ℝ) (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_027 :
    (2147594192367/12800000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/256:ℝ) (7/64:ℝ) (55/512:ℝ) (2147594192367/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0163).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x) ≤ (8591002705333/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/256:ℝ) (7/64:ℝ) (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_028 :
    (4174119095129/25600000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/64:ℝ) (29/256:ℝ) (57/512:ℝ) (4174119095129/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0169).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x) ≤ (260901839333/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/64:ℝ) (29/256:ℝ) (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_029 :
    (405549072243/2560000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/256:ℝ) (15/128:ℝ) (59/512:ℝ) (405549072243/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0175).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x) ≤ (4055798354587/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/256:ℝ) (15/128:ℝ) (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_030 :
    (3939282518997/25600000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/128:ℝ) (31/256:ℝ) (61/512:ℝ) (3939282518997/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0181).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x) ≤ (7879174765393/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/128:ℝ) (31/256:ℝ) (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_031 :
    (382547319749/2560000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/256:ℝ) (1/8:ℝ) (63/512:ℝ) (382547319749/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0187).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x) ≤ (7651550456467/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/256:ℝ) (1/8:ℝ) (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
