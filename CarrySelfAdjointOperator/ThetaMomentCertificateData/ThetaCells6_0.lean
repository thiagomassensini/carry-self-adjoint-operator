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

theorem thetaFirstMode_cell_upper_6_000 :
    (∫ x in (0/1:ℝ)..(1/128:ℝ), x^6*thetaFirstMode x) ≤ (26578968051/1261007895663738880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (0/1:ℝ) (1/128:ℝ) (10803486627/125000000000:ℝ) (82578044037/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_000).2 (thetaFirstMode_node_004).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_001 :
    (∫ x in (1/128:ℝ)..(1/64:ℝ), x^6*thetaFirstMode x) ≤ (81023381403903/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/128:ℝ) (1/64:ℝ) (82578044037/1000000000000:ℝ) (19709559339/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_004).2 (thetaFirstMode_node_008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_002 :
    (∫ x in (1/64:ℝ)..(3/128:ℝ), x^6*thetaFirstMode x) ≤ (629000182990587/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/64:ℝ) (3/128:ℝ) (19709559339/250000000000:ℝ) (37604129859/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_008).2 (thetaFirstMode_node_012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_003 :
    (∫ x in (3/128:ℝ)..(1/32:ℝ), x^6*thetaFirstMode x) ≤ (8288036673239249/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/128:ℝ) (1/32:ℝ) (37604129859/500000000000:ℝ) (71687771591/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_012).2 (thetaFirstMode_node_016).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_004 :
    (∫ x in (1/32:ℝ)..(5/128:ℝ), x^6*thetaFirstMode x) ≤ (4912208904331031/4503599627370496000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/32:ℝ) (5/128:ℝ) (71687771591/1000000000000:ℝ) (6827630847/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_016).2 (thetaFirstMode_node_020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_005 :
    (∫ x in (5/128:ℝ)..(3/64:ℝ), x^6*thetaFirstMode x) ≤ (13386470570609357/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/128:ℝ) (3/64:ℝ) (6827630847/100000000000:ℝ) (32486641319/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_020).2 (thetaFirstMode_node_024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_006 :
    (∫ x in (3/64:ℝ)..(7/128:ℝ), x^6*thetaFirstMode x) ≤ (27456111264053239/3152519739159347200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/64:ℝ) (7/128:ℝ) (32486641319/500000000000:ℝ) (7722248157/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_024).2 (thetaFirstMode_node_028).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_007 :
    (∫ x in (7/128:ℝ)..(1/16:ℝ), x^6*thetaFirstMode x) ≤ (305821996024418087/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/128:ℝ) (1/16:ℝ) (7722248157/125000000000:ℝ) (29344794299/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_028).2 (thetaFirstMode_node_032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_008 :
    (∫ x in (1/16:ℝ)..(9/128:ℝ), x^6*thetaFirstMode x) ≤ (1225263838192487283/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/16:ℝ) (9/128:ℝ) (29344794299/500000000000:ℝ) (55707148763/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_032).2 (thetaFirstMode_node_036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_009 :
    (∫ x in (9/128:ℝ)..(5/64:ℝ), x^6*thetaFirstMode x) ≤ (40333741259694613/562949953421312000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/128:ℝ) (5/64:ℝ) (55707148763/1000000000000:ℝ) (52829608587/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_036).2 (thetaFirstMode_node_040).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_010 :
    (∫ x in (5/64:ℝ)..(11/128:ℝ), x^6*thetaFirstMode x) ≤ (3894408469593472473/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/64:ℝ) (11/128:ℝ) (52829608587/1000000000000:ℝ) (25027900449/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_040).2 (thetaFirstMode_node_044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_011 :
    (∫ x in (11/128:ℝ)..(3/32:ℝ), x^6*thetaFirstMode x) ≤ (794425105708901189/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/128:ℝ) (3/32:ℝ) (25027900449/500000000000:ℝ) (23692225997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_044).2 (thetaFirstMode_node_048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_012 :
    (∫ x in (3/32:ℝ)..(13/128:ℝ), x^6*thetaFirstMode x) ≤ (9904702548141639137/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/32:ℝ) (13/128:ℝ) (23692225997/500000000000:ℝ) (44814185473/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_048).2 (thetaFirstMode_node_052).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_013 :
    (∫ x in (13/128:ℝ)..(7/64:ℝ), x^6*thetaFirstMode x) ≤ (14843225563267578103/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/128:ℝ) (7/64:ℝ) (44814185473/1000000000000:ℝ) (661617597/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_052).2 (thetaFirstMode_node_056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_014 :
    (∫ x in (7/64:ℝ)..(15/128:ℝ), x^6*thetaFirstMode x) ≤ (21505875174471051137/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/64:ℝ) (15/128:ℝ) (661617597/15625000000:ℝ) (39970904711/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_056).2 (thetaFirstMode_node_060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_015 :
    (∫ x in (15/128:ℝ)..(1/8:ℝ), x^6*thetaFirstMode x) ≤ (15128033313259064853/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/128:ℝ) (1/8:ℝ) (39970904711/1000000000000:ℝ) (301557293/8000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_060).2 (thetaFirstMode_node_064).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_016 :
    (∫ x in (1/8:ℝ)..(17/128:ℝ), x^6*thetaFirstMode x) ≤ (1659151898084006527/1261007895663738880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/8:ℝ) (17/128:ℝ) (301557293/8000000000:ℝ) (710261049/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_064).2 (thetaFirstMode_node_068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_017 :
    (∫ x in (17/128:ℝ)..(9/64:ℝ), x^6*thetaFirstMode x) ≤ (6946559534233193639/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/128:ℝ) (9/64:ℝ) (710261049/20000000000:ℝ) (16712126261/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_068).2 (thetaFirstMode_node_072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_018 :
    (∫ x in (9/64:ℝ)..(19/128:ℝ), x^6*thetaFirstMode x) ≤ (36469872105671087263/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/64:ℝ) (19/128:ℝ) (16712126261/500000000000:ℝ) (7856590531/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_072).2 (thetaFirstMode_node_076).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_019 :
    (∫ x in (19/128:ℝ)..(5/32:ℝ), x^6*thetaFirstMode x) ≤ (11747193900046430769/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/128:ℝ) (5/32:ℝ) (7856590531/250000000000:ℝ) (7379352941/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_076).2 (thetaFirstMode_node_080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_020 :
    (∫ x in (5/32:ℝ)..(21/128:ℝ), x^6*thetaFirstMode x) ≤ (29766691735086141803/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/32:ℝ) (21/128:ℝ) (7379352941/250000000000:ℝ) (3461920953/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_080).2 (thetaFirstMode_node_084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_021 :
    (∫ x in (21/128:ℝ)..(11/64:ℝ), x^6*thetaFirstMode x) ≤ (29712322996237775617/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/128:ℝ) (11/64:ℝ) (3461920953/125000000000:ℝ) (25958137133/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_084).2 (thetaFirstMode_node_088).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_022 :
    (∫ x in (11/64:ℝ)..(23/128:ℝ), x^6*thetaFirstMode x) ≤ (182779219034104766459/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/64:ℝ) (23/128:ℝ) (25958137133/1000000000000:ℝ) (12151787313/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_088).2 (thetaFirstMode_node_092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_023 :
    (∫ x in (23/128:ℝ)..(3/16:ℝ), x^6*thetaFirstMode x) ≤ (7928197983958006053/1125899906842624000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/128:ℝ) (3/16:ℝ) (12151787313/500000000000:ℝ) (2272948707/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_092).2 (thetaFirstMode_node_096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_024 :
    (∫ x in (3/16:ℝ)..(25/128:ℝ), x^6*thetaFirstMode x) ≤ (133202998542010837353/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/16:ℝ) (25/128:ℝ) (2272948707/100000000000:ℝ) (5308409979/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_096).2 (thetaFirstMode_node_100).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_025 :
    (∫ x in (25/128:ℝ)..(13/64:ℝ), x^6*thetaFirstMode x) ≤ (158088473198537659079/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/128:ℝ) (13/64:ℝ) (5308409979/250000000000:ℝ) (9906881453/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_100).2 (thetaFirstMode_node_104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_026 :
    (∫ x in (13/64:ℝ)..(27/128:ℝ), x^6*thetaFirstMode x) ≤ (92844590934291253021/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/64:ℝ) (27/128:ℝ) (9906881453/500000000000:ℝ) (9233777979/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_104).2 (thetaFirstMode_node_108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_027 :
    (∫ x in (27/128:ℝ)..(7/32:ℝ), x^6*thetaFirstMode x) ≤ (17280311984950132423/1261007895663738880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/128:ℝ) (7/32:ℝ) (9233777979/500000000000:ℝ) (17192694997/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_108).2 (thetaFirstMode_node_112).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_028 :
    (∫ x in (7/32:ℝ)..(29/128:ℝ), x^6*thetaFirstMode x) ≤ (248989919660736166389/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/32:ℝ) (29/128:ℝ) (17192694997/1000000000000:ℝ) (3197367559/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_112).2 (thetaFirstMode_node_116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_029 :
    (∫ x in (29/128:ℝ)..(15/64:ℝ), x^6*thetaFirstMode x) ≤ (142280791132779660353/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/128:ℝ) (15/64:ℝ) (3197367559/200000000000:ℝ) (14847629727/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_116).2 (thetaFirstMode_node_120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_030 :
    (∫ x in (15/64:ℝ)..(31/128:ℝ), x^6*thetaFirstMode x) ≤ (18433694354877170987/900719925474099200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/64:ℝ) (31/128:ℝ) (14847629727/1000000000000:ℝ) (6886354727/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_120).2 (thetaFirstMode_node_124).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_031 :
    (∫ x in (31/128:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x) ≤ (725803105577737796099/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/128:ℝ) (1/4:ℝ) (6886354727/500000000000:ℝ) (12759714529/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_124).2 (thetaFirstMode_node_128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
