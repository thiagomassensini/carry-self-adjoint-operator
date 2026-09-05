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

theorem thetaFirstMode_cell_lower_4_000 :
    (83211955461/171798691840000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (0/1:ℝ) (1/128:ℝ) (5/768:ℝ) (83211955461/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_003).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_000 :
    (∫ x in (0/1:ℝ)..(1/128:ℝ), x^4*thetaFirstMode x) ≤ (166439371067/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (0/1:ℝ) (1/128:ℝ) (10803486627/125000000000:ℝ) (82578044037/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_000).2 (thetaFirstMode_node_004).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_001 :
    (61978719399/4294967296000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(1/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/128:ℝ) (1/64:ℝ) (105/7936:ℝ) (1999313529/25000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_007).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_001 :
    (∫ x in (1/128:ℝ)..(1/64:ℝ), x^4*thetaFirstMode x) ≤ (4959027043011/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/128:ℝ) (1/64:ℝ) (82578044037/1000000000000:ℝ) (19709559339/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_004).2 (thetaFirstMode_node_008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_002 :
    (1615238150421/17179869184000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(3/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/64:ℝ) (3/128:ℝ) (3325/162048:ℝ) (7655157111/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_011).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_002 :
    (∫ x in (1/64:ℝ)..(3/128:ℝ), x^4*thetaFirstMode x) ≤ (16155106037627/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/64:ℝ) (3/128:ℝ) (19709559339/250000000000:ℝ) (37604129859/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_008).2 (thetaFirstMode_node_012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_003 :
    (2283915602903/6871947673600000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(1/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/128:ℝ) (1/32:ℝ) (16835/599808:ℝ) (2924347763/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_015).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_003 :
    (∫ x in (3/128:ℝ)..(1/32:ℝ), x^4*thetaFirstMode x) ≤ (342649509509869/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/128:ℝ) (1/32:ℝ) (37604129859/500000000000:ℝ) (71687771591/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_012).2 (thetaFirstMode_node_016).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_004 :
    (73241101440617/85899345920000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(5/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/32:ℝ) (5/128:ℝ) (19215/537856:ℝ) (34860114917/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_019).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_004 :
    (∫ x in (1/32:ℝ)..(5/128:ℝ), x^4*thetaFirstMode x) ≤ (58604124898627/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/32:ℝ) (5/128:ℝ) (71687771591/1000000000000:ℝ) (6827630847/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_016).2 (thetaFirstMode_node_020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_005 :
    (61777840951049/34359738368000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(3/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/128:ℝ) (3/64:ℝ) (155155/3571968:ℝ) (13282700699/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_023).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_005 :
    (∫ x in (5/128:ℝ)..(3/64:ℝ), x^4*thetaFirstMode x) ≤ (92685444276941/51539607552000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/128:ℝ) (3/64:ℝ) (6827630847/100000000000:ℝ) (32486641319/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_020).2 (thetaFirstMode_node_024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_006 :
    (71344638886697/21474836480000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(7/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/64:ℝ) (7/128:ℝ) (354965/6935808:ℝ) (7899971087/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_027).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_006 :
    (∫ x in (3/64:ℝ)..(7/128:ℝ), x^4*thetaFirstMode x) ≤ (68505317229347/20615843020800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/64:ℝ) (7/128:ℝ) (32486641319/500000000000:ℝ) (7722248157/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_024).2 (thetaFirstMode_node_028).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_007 :
    (239750594342017/42949672960000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(1/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/128:ℝ) (1/16:ℝ) (240825/4086016:ℝ) (15021025897/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_031).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_007 :
    (∫ x in (7/128:ℝ)..(1/16:ℝ), x^4*thetaFirstMode x) ≤ (959214153497957/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/128:ℝ) (1/16:ℝ) (7722248157/125000000000:ℝ) (29344794299/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_028).2 (thetaFirstMode_node_032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_008 :
    (187478170693067/21474836480000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/16:ℝ) (9/128:ℝ) (1346485/20183808:ℝ) (7133601107/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_035).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_008 :
    (∫ x in (1/16:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x) ≤ (9001028029008733/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/16:ℝ) (9/128:ℝ) (29344794299/500000000000:ℝ) (55707148763/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_032).2 (thetaFirstMode_node_036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_009 :
    (443538335049431/34359738368000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/128:ℝ) (5/64:ℝ) (2342795/31450368:ℝ) (10830952481/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_039).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_009 :
    (∫ x in (9/128:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x) ≤ (6654676967844031/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/128:ℝ) (5/64:ℝ) (55707148763/1000000000000:ℝ) (52829608587/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_036).2 (thetaFirstMode_node_040).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_010 :
    (1567241108620489/85899345920000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/64:ℝ) (11/128:ℝ) (1285935/15629056:ℝ) (25671014539/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_043).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_010 :
    (∫ x in (5/64:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x) ≤ (6270539141558439/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/64:ℝ) (11/128:ℝ) (52829608587/1000000000000:ℝ) (25027900449/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_040).2 (thetaFirstMode_node_044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_011 :
    (853760858970281/34359738368000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/128:ℝ) (3/32:ℝ) (6072115/67415808:ℝ) (9726032501/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_047).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_011 :
    (∫ x in (11/128:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x) ≤ (6404883639731413/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/128:ℝ) (3/32:ℝ) (25027900449/500000000000:ℝ) (23692225997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_044).2 (thetaFirstMode_node_048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_012 :
    (2817727631492529/85899345920000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/32:ℝ) (13/128:ℝ) (9204125/94050048:ℝ) (23009183589/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_051).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_012 :
    (∫ x in (3/32:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x) ≤ (11273987772684437/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/32:ℝ) (13/128:ℝ) (23692225997/500000000000:ℝ) (44814185473/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_048).2 (thetaFirstMode_node_052).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_013 :
    (3622514842199199/85899345920000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/128:ℝ) (7/64:ℝ) (4504545/42631936:ℝ) (21752795829/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_055).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_013 :
    (∫ x in (13/128:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x) ≤ (14494181712701491/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/128:ℝ) (7/64:ℝ) (44814185473/1000000000000:ℝ) (661617597/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_052).2 (thetaFirstMode_node_056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_014 :
    (568978770420049/10737418240000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/64:ℝ) (15/128:ℝ) (19305445/170151168:ℝ) (2568161599/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_059).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_014 :
    (∫ x in (7/64:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x) ≤ (54638149516975631/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/64:ℝ) (15/128:ℝ) (661617597/15625000000:ℝ) (39970904711/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_056).2 (thetaFirstMode_node_060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_015 :
    (11212882902883629/171798691840000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/128:ℝ) (1/8:ℝ) (26932955/222106368:ℝ) (38771936829/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_063).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_015 :
    (∫ x in (15/128:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x) ≤ (16824515244985519/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/128:ℝ) (1/8:ℝ) (39970904711/1000000000000:ℝ) (301557293/8000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_060).2 (thetaFirstMode_node_064).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_016 :
    (6784806992589037/85899345920000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/8:ℝ) (17/128:ℝ) (12267255/95047936:ℝ) (18274048477/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_067).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_016 :
    (∫ x in (1/8:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x) ≤ (1085917936832809/13743895347200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/8:ℝ) (17/128:ℝ) (301557293/8000000000:ℝ) (710261049/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_064).2 (thetaFirstMode_node_068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_017 :
    (1616623135730867/17179869184000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/128:ℝ) (9/64:ℝ) (49373275/360738048:ℝ) (3441739997/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_071).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_017 :
    (∫ x in (17/128:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x) ≤ (24257457478742479/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/128:ℝ) (9/64:ℝ) (710261049/20000000000:ℝ) (16712126261/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_068).2 (thetaFirstMode_node_072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_018 :
    (474768642329927/4294967296000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/64:ℝ) (19/128:ℝ) (65168285/450455808:ℝ) (809451917/25000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_075).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_018 :
    (∫ x in (9/64:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x) ≤ (18997355534571361/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/64:ℝ) (19/128:ℝ) (16712126261/500000000000:ℝ) (7856590531/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_072).2 (thetaFirstMode_node_076).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_019 :
    (2753381564470607/21474836480000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/128:ℝ) (5/32:ℝ) (28256865/185318656:ℝ) (3803533307/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_079).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_019 :
    (∫ x in (19/128:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x) ≤ (2754378634668483/21474836480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/128:ℝ) (5/32:ℝ) (7856590531/250000000000:ℝ) (7379352941/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_076).2 (thetaFirstMode_node_080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_020 :
    (3156906649041097/21474836480000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/32:ℝ) (21/128:ℝ) (108830605/678989568:ℝ) (3570753397/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_083).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_020 :
    (∫ x in (5/32:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x) ≤ (37897149750264271/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/32:ℝ) (21/128:ℝ) (7379352941/250000000000:ℝ) (3461920953/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_080).2 (thetaFirstMode_node_084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_021 :
    (28652033981408507/171798691840000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/128:ℝ) (11/64:ℝ) (138068915/821399808:ℝ) (26789344097/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_087).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_021 :
    (∫ x in (21/128:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x) ≤ (34395910256456729/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/128:ℝ) (11/64:ℝ) (3461920953/125000000000:ℝ) (25958137133/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_084).2 (thetaFirstMode_node_088).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_022 :
    (32191092143129611/171798691840000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/64:ℝ) (23/128:ℝ) (57759975/328374016:ℝ) (25096137901/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_091).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_022 :
    (∫ x in (11/64:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x) ≤ (64408410268082789/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/64:ℝ) (23/128:ℝ) (25958137133/1000000000000:ℝ) (12151787313/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_088).2 (thetaFirstMode_node_092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_023 :
    (1792179927463253/8589934592000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/128:ℝ) (3/16:ℝ) (215335435/1172183808:ℝ) (1174213613/50000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_095).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_023 :
    (∫ x in (23/128:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x) ≤ (8964694446387631/42949672960000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/128:ℝ) (3/16:ℝ) (12151787313/500000000000:ℝ) (2272948707/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_092).2 (thetaFirstMode_node_096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_024 :
    (9894671596019243/42949672960000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/16:ℝ) (25/128:ℝ) (265188245/1384704768:ℝ) (5487890243/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_099).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_024 :
    (∫ x in (3/16:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x) ≤ (39596108271999311/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/16:ℝ) (25/128:ℝ) (2272948707/100000000000:ℝ) (5308409979/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_096).2 (thetaFirstMode_node_100).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_025 :
    (43363956162167113/171798691840000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/128:ℝ) (13/64:ℝ) (107958585/541632256:ℝ) (20495774863/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_103).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_025 :
    (∫ x in (25/128:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x) ≤ (43383793543714241/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/128:ℝ) (13/64:ℝ) (5308409979/250000000000:ℝ) (9906881453/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_100).2 (thetaFirstMode_node_104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_026 :
    (47165987646424977/171798691840000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/64:ℝ) (27/128:ℝ) (392523565/1895063808:ℝ) (19114648467/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_107).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_026 :
    (∫ x in (13/64:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x) ≤ (17695652842308839/64424509440000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/64:ℝ) (27/128:ℝ) (9906881453/500000000000:ℝ) (9233777979/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_104).2 (thetaFirstMode_node_108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_027 :
    (10190169960896761/34359738368000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/128:ℝ) (7/32:ℝ) (472349075/2197602048:ℝ) (3561177301/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_111).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_027 :
    (∫ x in (27/128:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x) ≤ (61171213649067631/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/128:ℝ) (7/32:ℝ) (9233777979/500000000000:ℝ) (17192694997/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_108).2 (thetaFirstMode_node_112).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_028 :
    (54684600814672279/171798691840000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/32:ℝ) (29/128:ℝ) (188221695/844999936:ℝ) (16567170259/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_115).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_028 :
    (∫ x in (7/32:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x) ≤ (27356326445393649/85899345920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/32:ℝ) (29/128:ℝ) (17192694997/1000000000000:ℝ) (3197367559/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_112).2 (thetaFirstMode_node_116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_029 :
    (11666754080281399/34359738368000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/128:ℝ) (15/64:ℝ) (670883395/2909837568:ℝ) (3079232749/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_119).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_029 :
    (∫ x in (29/128:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x) ≤ (175094548569193721/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/128:ℝ) (15/64:ℝ) (3197367559/200000000000:ℝ) (14847629727/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_116).2 (thetaFirstMode_node_120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_030 :
    (30932908993724239/85899345920000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/64:ℝ) (31/128:ℝ) (792518405/3324787968:ℝ) (7145259889/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_123).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_030 :
    (∫ x in (15/64:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x) ≤ (371400277681586237/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/64:ℝ) (31/128:ℝ) (14847629727/1000000000000:ℝ) (6886354727/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_120).2 (thetaFirstMode_node_124).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_031 :
    (13049912127911737/34359738368000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/128:ℝ) (1/4:ℝ) (310396905/1260871936:ℝ) (2649577177/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_127).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_031 :
    (∫ x in (31/128:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x) ≤ (130574087630239373/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/128:ℝ) (1/4:ℝ) (6886354727/500000000000:ℝ) (12759714529/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_124).2 (thetaFirstMode_node_128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
