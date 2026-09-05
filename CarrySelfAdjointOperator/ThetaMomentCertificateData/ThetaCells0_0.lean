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

theorem thetaFirstMode_cell_lower_0_000 :
    (42244559843/64000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (0/1:ℝ) (1/128:ℝ) (1/256:ℝ) (42244559843/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_001).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x) ≤ (169005937053/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (0/1:ℝ) (1/128:ℝ) (10803486627/125000000000:ℝ) (82578044037/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_000).2 (thetaFirstMode_node_004).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_001 :
    (80694313103/128000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/128:ℝ) (1/64:ℝ) (3/256:ℝ) (80694313103/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_005).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_001 :
    (∫ x in (1/128:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x) ≤ (161416281393/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/128:ℝ) (1/64:ℝ) (82578044037/1000000000000:ℝ) (19709559339/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_004).2 (thetaFirstMode_node_008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_002 :
    (77009458073/128000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/64:ℝ) (3/128:ℝ) (5/256:ℝ) (77009458073/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_009).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_002 :
    (∫ x in (1/64:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x) ≤ (77023248537/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/64:ℝ) (3/128:ℝ) (19709559339/250000000000:ℝ) (37604129859/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_008).2 (thetaFirstMode_node_012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_003 :
    (73434278003/128000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/128:ℝ) (1/32:ℝ) (7/256:ℝ) (73434278003/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_013).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_003 :
    (∫ x in (3/128:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x) ≤ (146896031309/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/128:ℝ) (1/32:ℝ) (37604129859/500000000000:ℝ) (71687771591/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_012).2 (thetaFirstMode_node_016).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_004 :
    (17492092671/32000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/32:ℝ) (5/128:ℝ) (9/256:ℝ) (17492092671/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_017).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_004 :
    (∫ x in (1/32:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x) ≤ (139964080061/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/32:ℝ) (5/128:ℝ) (71687771591/1000000000000:ℝ) (6827630847/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_016).2 (thetaFirstMode_node_020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_005 :
    (66611209773/128000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/128:ℝ) (3/64:ℝ) (11/256:ℝ) (66611209773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_021).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_005 :
    (∫ x in (5/128:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x) ≤ (33312397777/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/128:ℝ) (3/64:ℝ) (6827630847/100000000000:ℝ) (32486641319/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_020).2 (thetaFirstMode_node_024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_006 :
    (7920268339/16000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/64:ℝ) (7/128:ℝ) (13/256:ℝ) (7920268339/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_025).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_006 :
    (∫ x in (3/64:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x) ≤ (63375633947/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/64:ℝ) (7/128:ℝ) (32486641319/500000000000:ℝ) (7722248157/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_024).2 (thetaFirstMode_node_028).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_007 :
    (6022041291/12800000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/128:ℝ) (1/16:ℝ) (15/256:ℝ) (6022041291/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_029).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_007 :
    (∫ x in (7/128:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x) ≤ (60233786927/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/128:ℝ) (1/16:ℝ) (7722248157/125000000000:ℝ) (29344794299/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_028).2 (thetaFirstMode_node_032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_008 :
    (57185122197/128000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/16:ℝ) (9/128:ℝ) (17/256:ℝ) (57185122197/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_033).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_008 :
    (∫ x in (1/16:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x) ≤ (114396737361/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/16:ℝ) (9/128:ℝ) (29344794299/500000000000:ℝ) (55707148763/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_032).2 (thetaFirstMode_node_036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_009 :
    (10851054733/25600000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/128:ℝ) (5/64:ℝ) (19/256:ℝ) (10851054733/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_037).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_009 :
    (∫ x in (9/128:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x) ≤ (2170735147/5120000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/128:ℝ) (5/64:ℝ) (55707148763/1000000000000:ℝ) (52829608587/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_036).2 (thetaFirstMode_node_040).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_010 :
    (25714877361/64000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/64:ℝ) (11/128:ℝ) (21/256:ℝ) (25714877361/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_041).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_010 :
    (∫ x in (5/64:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x) ≤ (20577081897/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/64:ℝ) (11/128:ℝ) (52829608587/1000000000000:ℝ) (25027900449/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_040).2 (thetaFirstMode_node_044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_011 :
    (48707344451/128000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/128:ℝ) (3/32:ℝ) (23/256:ℝ) (48707344451/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_045).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_011 :
    (∫ x in (11/128:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x) ≤ (24360063223/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/128:ℝ) (3/32:ℝ) (25027900449/500000000000:ℝ) (23692225997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_044).2 (thetaFirstMode_node_048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_012 :
    (46086717321/128000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/32:ℝ) (13/128:ℝ) (25/256:ℝ) (46086717321/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_049).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_012 :
    (∫ x in (3/32:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x) ≤ (92198637467/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/32:ℝ) (13/128:ℝ) (23692225997/500000000000:ℝ) (44814185473/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_048).2 (thetaFirstMode_node_052).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_013 :
    (871328941/2560000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/128:ℝ) (7/64:ℝ) (27/256:ℝ) (871328941/20000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_053).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_013 :
    (∫ x in (13/128:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x) ≤ (87157711681/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/128:ℝ) (7/64:ℝ) (44814185473/1000000000000:ℝ) (661617597/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_052).2 (thetaFirstMode_node_056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_014 :
    (41145010773/128000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/64:ℝ) (15/128:ℝ) (29/256:ℝ) (41145010773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_057).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_014 :
    (∫ x in (7/64:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x) ≤ (82314430919/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/64:ℝ) (15/128:ℝ) (661617597/15625000000:ℝ) (39970904711/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_056).2 (thetaFirstMode_node_060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_015 :
    (38820793481/128000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/128:ℝ) (1/8:ℝ) (31/256:ℝ) (38820793481/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_061).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_015 :
    (∫ x in (15/128:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x) ≤ (606762237/2000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/128:ℝ) (1/8:ℝ) (39970904711/1000000000000:ℝ) (301557293/8000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_060).2 (thetaFirstMode_node_064).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_016 :
    (731841853/2560000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/8:ℝ) (17/128:ℝ) (33/256:ℝ) (731841853/20000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_065).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_016 :
    (∫ x in (1/8:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x) ≤ (2928308563/10240000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/8:ℝ) (17/128:ℝ) (301557293/8000000000:ℝ) (710261049/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_064).2 (thetaFirstMode_node_068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_017 :
    (1722856153/6400000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/128:ℝ) (9/64:ℝ) (35/256:ℝ) (1722856153/50000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_069).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_017 :
    (∫ x in (17/128:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x) ≤ (17234326243/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/128:ℝ) (9/64:ℝ) (710261049/20000000000:ℝ) (16712126261/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_068).2 (thetaFirstMode_node_072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_018 :
    (32414021867/128000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/64:ℝ) (19/128:ℝ) (37/256:ℝ) (32414021867/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_073).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_018 :
    (∫ x in (9/64:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x) ≤ (32425307323/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/64:ℝ) (19/128:ℝ) (16712126261/500000000000:ℝ) (7856590531/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_072).2 (thetaFirstMode_node_076).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_019 :
    (6092170757/25600000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/128:ℝ) (5/32:ℝ) (39/256:ℝ) (6092170757/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_077).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_019 :
    (∫ x in (19/128:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x) ≤ (952246467/4000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/128:ℝ) (5/32:ℝ) (7856590531/250000000000:ℝ) (7379352941/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_076).2 (thetaFirstMode_node_080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_020 :
    (28595616483/128000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/32:ℝ) (21/128:ℝ) (41/256:ℝ) (28595616483/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_081).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_020 :
    (∫ x in (5/32:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x) ≤ (14303194847/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/32:ℝ) (21/128:ℝ) (7379352941/250000000000:ℝ) (3461920953/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_080).2 (thetaFirstMode_node_084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_021 :
    (6704061517/32000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/128:ℝ) (11/64:ℝ) (43/256:ℝ) (6704061517/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_085).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_021 :
    (∫ x in (21/128:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x) ≤ (53653504757/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/128:ℝ) (11/64:ℝ) (3461920953/125000000000:ℝ) (25958137133/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_084).2 (thetaFirstMode_node_088).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_022 :
    (785019459/4000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/64:ℝ) (23/128:ℝ) (45/256:ℝ) (785019459/31250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_089).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_022 :
    (∫ x in (11/64:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x) ≤ (50261711759/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/64:ℝ) (23/128:ℝ) (25958137133/1000000000000:ℝ) (12151787313/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_088).2 (thetaFirstMode_node_092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_023 :
    (23506576293/128000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/128:ℝ) (3/16:ℝ) (47/256:ℝ) (23506576293/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_093).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_023 :
    (∫ x in (23/128:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x) ≤ (734891589/4000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/128:ℝ) (3/16:ℝ) (12151787313/500000000000:ℝ) (2272948707/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_092).2 (thetaFirstMode_node_096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_024 :
    (10985946169/64000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/16:ℝ) (25/128:ℝ) (49/256:ℝ) (10985946169/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_097).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_024 :
    (∫ x in (3/16:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x) ≤ (21981563493/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/16:ℝ) (25/128:ℝ) (2272948707/100000000000:ℝ) (5308409979/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_096).2 (thetaFirstMode_node_100).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_025 :
    (20514317709/128000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/128:ℝ) (13/64:ℝ) (51/256:ℝ) (20514317709/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_101).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_025 :
    (∫ x in (25/128:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x) ≤ (20523701411/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/128:ℝ) (13/64:ℝ) (5308409979/250000000000:ℝ) (9906881453/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_100).2 (thetaFirstMode_node_104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_026 :
    (19131566483/128000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/64:ℝ) (27/128:ℝ) (53/256:ℝ) (19131566483/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_105).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_026 :
    (∫ x in (13/64:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x) ≤ (2392582429/16000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/64:ℝ) (27/128:ℝ) (9906881453/500000000000:ℝ) (9233777979/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_104).2 (thetaFirstMode_node_108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_027 :
    (8910662933/64000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/128:ℝ) (7/32:ℝ) (55/256:ℝ) (8910662933/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_109).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_027 :
    (∫ x in (27/128:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x) ≤ (7132050191/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/128:ℝ) (7/32:ℝ) (9233777979/500000000000:ℝ) (17192694997/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_108).2 (thetaFirstMode_node_112).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_028 :
    (16581261977/128000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/32:ℝ) (29/128:ℝ) (57/256:ℝ) (16581261977/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_113).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_028 :
    (∫ x in (7/32:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x) ≤ (4147441599/32000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/32:ℝ) (29/128:ℝ) (17192694997/1000000000000:ℝ) (3197367559/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_112).2 (thetaFirstMode_node_116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_029 :
    (3852256419/32000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/128:ℝ) (15/64:ℝ) (59/256:ℝ) (3852256419/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_117).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_029 :
    (∫ x in (29/128:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x) ≤ (15417233761/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/128:ℝ) (15/64:ℝ) (3197367559/200000000000:ℝ) (14847629727/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_116).2 (thetaFirstMode_node_120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_030 :
    (7151129133/64000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/64:ℝ) (31/128:ℝ) (61/256:ℝ) (7151129133/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_121).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_030 :
    (∫ x in (15/64:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x) ≤ (28620339181/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/64:ℝ) (31/128:ℝ) (14847629727/1000000000000:ℝ) (6886354727/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_120).2 (thetaFirstMode_node_124).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_031 :
    (6629298589/64000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/128:ℝ) (1/4:ℝ) (63/256:ℝ) (6629298589/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_125).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_031 :
    (∫ x in (31/128:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x) ≤ (26532423983/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/128:ℝ) (1/4:ℝ) (6886354727/500000000000:ℝ) (12759714529/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_124).2 (thetaFirstMode_node_128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
