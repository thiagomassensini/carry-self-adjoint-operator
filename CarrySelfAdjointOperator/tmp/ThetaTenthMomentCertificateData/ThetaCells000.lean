import CarrySelfAdjointOperator.tmp.ThetaTenthMomentCertificateData.ThetaNodes000
import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaTenth_first_cell_lower_0_000 :
    (376946299/40000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (0/1:ℝ) (1/4:ℝ)
      (1/8:ℝ) (376946299/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0001).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x) ≤ (495937687/40000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_0_000 :
    (523/10000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^0*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 0 (0/1:ℝ) (1/4:ℝ)
      (1/8:ℝ) (523/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0001).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^0*thetaSecondMode x) ≤ (6977/8000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 0 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_2_000 :
    (113647327/960000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (0/1:ℝ) (1/4:ℝ)
      (3/16:ℝ) (113647327/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0002).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_2_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x) ≤ (124706939/768000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_2_000 :
    (251/1920000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^2*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 2 (0/1:ℝ) (1/4:ℝ)
      (3/16:ℝ) (251/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0002).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_2_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^2*thetaSecondMode x) ≤ (2909/320000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 2 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_4_000 :
    (189082303/51200000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (0/1:ℝ) (1/4:ℝ)
      (5/24:ℝ) (189082303/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0003).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_4_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x) ≤ (751131703/153600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_4_000 :
    (29/12800000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^4*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 4 (0/1:ℝ) (1/4:ℝ)
      (5/24:ℝ) (29/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0003).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_4_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^4*thetaSecondMode x) ≤ (34931/153600000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 4 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_6_000 :
    (6877071/45875200000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (0/1:ℝ) (1/4:ℝ)
      (7/32:ℝ) (6877071/400000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0004).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_6_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x) ≤ (125532673/655360000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_6_000 :
    (39/573440000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^6*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 6 (0/1:ℝ) (1/4:ℝ)
      (7/32:ℝ) (39/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0004).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_6_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^6*thetaSecondMode x) ≤ (17477/2293760000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 6 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_8_000 :
    (162225851/23592960000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (0/1:ℝ) (1/4:ℝ)
      (9/40:ℝ) (162225851/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0005).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_8_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x) ≤ (1006325719/117964800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_8_000 :
    (61/23592960000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^8*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 8 (0/1:ℝ) (1/4:ℝ)
      (9/40:ℝ) (61/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0005).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_8_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^8*thetaSecondMode x) ≤ (11659/39321600000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 8 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_10_000 :
    (155997967/461373440000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^10*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 10 (0/1:ℝ) (1/4:ℝ)
      (11/48:ℝ) (155997967/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0006).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_10_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^10*thetaFirstMode x) ≤ (1133922727/2768240640000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 10 (0/1:ℝ) (1/4:ℝ)
      (432139183/5000000000:ℝ) (7974813/625000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.1 (thetaTenth_node_0007).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_10_000 :
    (13/115343360000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/4:ℝ), x^10*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 10 (0/1:ℝ) (1/4:ℝ)
      (11/48:ℝ) (13/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0006).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_10_000 :
    (∫ x in (0/1:ℝ)..(1/4:ℝ), x^10*thetaSecondMode x) ≤ (7/553648128000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 10 (0/1:ℝ) (1/4:ℝ)
      (69747/10000000000:ℝ) (23/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0000).2.2.2 (thetaTenth_node_0007).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_0_001 :
    (15597157/20000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/4:ℝ) (1/2:ℝ)
      (3/8:ℝ) (15597157/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0008).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_0_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x) ≤ (16577329/10000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_0_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^0*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 0 (1/4:ℝ) (1/2:ℝ)
      (3/8:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0008).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_0_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^0*thetaSecondMode x) ≤ (3/10000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 0 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_2_001 :
    (153474181/1920000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/4:ℝ) (1/2:ℝ)
      (45/112:ℝ) (21924883/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0009).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_2_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x) ≤ (186116837/960000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_2_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^2*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 2 (1/4:ℝ) (1/2:ℝ)
      (45/112:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0009).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_2_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^2*thetaSecondMode x) ≤ (9/256000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 2 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_4_001 :
    (252011803/25600000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/4:ℝ) (1/2:ℝ)
      (105/248:ℝ) (8129413/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0010).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_4_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x) ≤ (330034123/12800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_4_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^4*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 4 (1/4:ℝ) (1/2:ℝ)
      (105/248:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0010).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_4_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^4*thetaSecondMode x) ≤ (3/640000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 4 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_6_001 :
    (234881293/163840000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/4:ℝ) (1/2:ℝ)
      (1785/4064:ℝ) (12946213/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0011).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_6_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x) ≤ (4422261229/1146880000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_6_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^6*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 6 (1/4:ℝ) (1/2:ℝ)
      (1785/4064:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0011).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_6_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^6*thetaSecondMode x) ≤ (129/183500800000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 6 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_8_001 :
    (2801895271/11796480000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/4:ℝ) (1/2:ℝ)
      (9207/20440:ℝ) (5483161/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0012).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_8_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x) ≤ (18728670329/29491200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_8_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^8*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 8 (1/4:ℝ) (1/2:ℝ)
      (9207/20440:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0012).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_8_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^8*thetaSecondMode x) ≤ (761/6553600000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 8 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_10_001 :
    (19893464497/461373440000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^10*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 10 (1/4:ℝ) (1/2:ℝ)
      (15015/32752:ℝ) (9718351/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0013).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_10_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^10*thetaFirstMode x) ≤ (25992769367/230686720000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 10 (1/4:ℝ) (1/2:ℝ)
      (7974813/625000000:ℝ) (627703/1250000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.1 (thetaTenth_node_0014).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_10_001 :
    (0/1:ℝ) ≤ ∫ x in (1/4:ℝ)..(1/2:ℝ), x^10*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 10 (1/4:ℝ) (1/2:ℝ)
      (15015/32752:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0013).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_10_001 :
    (∫ x in (1/4:ℝ)..(1/2:ℝ), x^10*thetaSecondMode x) ≤ (3813/184549376000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 10 (1/4:ℝ) (1/2:ℝ)
      (23/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0007).2.2.2 (thetaTenth_node_0014).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_0_002 :
    (472721/40000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/2:ℝ) (3/4:ℝ)
      (5/8:ℝ) (472721/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0015).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_0_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x) ≤ (5043969/80000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_0_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^0*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 0 (1/2:ℝ) (3/4:ℝ)
      (5/8:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0015).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_0_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^0*thetaSecondMode x) ≤ (1/40000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 0 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_2_002 :
    (627589/192000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/2:ℝ) (3/4:ℝ)
      (195/304:ℝ) (33031/1000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0016).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_2_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x) ≤ (166674427/7680000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_2_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^2*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 2 (1/2:ℝ) (3/4:ℝ)
      (195/304:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0016).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_2_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^2*thetaSecondMode x) ≤ (19/1920000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 2 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_4_002 :
    (49557781/51200000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/2:ℝ) (3/4:ℝ)
      (3325/5064:ℝ) (234871/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0017).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_4_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x) ≤ (2392947737/307200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_4_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^4*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 4 (1/2:ℝ) (3/4:ℝ)
      (3325/5064:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0017).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_4_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^4*thetaSecondMode x) ≤ (211/51200000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 4 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_6_002 :
    (177858479/573440000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/2:ℝ) (3/4:ℝ)
      (44135/65888:ℝ) (86381/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0018).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_6_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x) ≤ (26769259239/9175040000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_6_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^6*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 6 (1/2:ℝ) (3/4:ℝ)
      (44135/65888:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0018).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_6_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^6*thetaSecondMode x) ≤ (2059/1146880000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 6 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_8_002 :
    (635154401/5898240000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/2:ℝ) (3/4:ℝ)
      (104445/153368:ℝ) (33131/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0019).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_8_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^8*thetaFirstMode x) ≤ (53754123089/47185920000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_8_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^8*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 8 (1/2:ℝ) (3/4:ℝ)
      (104445/153368:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0019).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_8_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^8*thetaSecondMode x) ≤ (19171/23592960000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 8 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_10_002 :
    (18576428009/461373440000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^10*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 10 (1/2:ℝ) (3/4:ℝ)
      (5800795/8404752:ℝ) (106091/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0020).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_10_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^10*thetaFirstMode x) ≤ (2560433549411/5536481280000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 10 (1/2:ℝ) (3/4:ℝ)
      (627703/1250000000:ℝ) (4469/2000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.1 (thetaTenth_node_0021).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_10_002 :
    (0/1:ℝ) ≤ ∫ x in (1/2:ℝ)..(3/4:ℝ), x^10*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 10 (1/2:ℝ) (3/4:ℝ)
      (5800795/8404752:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0020).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_10_002 :
    (∫ x in (1/2:ℝ)..(3/4:ℝ), x^10*thetaSecondMode x) ≤ (175099/461373440000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 10 (1/2:ℝ) (3/4:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0014).2.2.2 (thetaTenth_node_0021).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_0_003 :
    (109/10000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/4:ℝ) (1/1:ℝ)
      (7/8:ℝ) (109/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0022).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_0_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x) ≤ (5587/20000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_0_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^0*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 0 (3/4:ℝ) (1/1:ℝ)
      (7/8:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0022).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_0_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^0*thetaSecondMode x) ≤ (1/40000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 0 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_2_003 :
    (2627/480000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/4:ℝ) (1/1:ℝ)
      (525/592:ℝ) (71/2500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0023).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_2_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x) ≤ (748679/3840000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_2_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^2*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 2 (3/4:ℝ) (1/1:ℝ)
      (525/592:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0023).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_2_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^2*thetaSecondMode x) ≤ (37/1920000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 2 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_4_003 :
    (146047/51200000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/4:ℝ) (1/1:ℝ)
      (16835/18744:ℝ) (187/10000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0024).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_4_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x) ≤ (5333117/38400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_4_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^4*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 4 (3/4:ℝ) (1/1:ℝ)
      (16835/18744:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0024).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_4_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^4*thetaSecondMode x) ≤ (781/51200000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 4 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_6_003 :
    (14197/9175040000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/4:ℝ) (1/1:ℝ)
      (412825/454304:ℝ) (1/80000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0025).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_6_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x) ≤ (463532273/4587520000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_6_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^6*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 6 (3/4:ℝ) (1/1:ℝ)
      (412825/454304:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0025).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_6_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^6*thetaSecondMode x) ≤ (14197/1146880000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 6 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_8_003 :
    (10425823/11796480000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/4:ℝ) (1/1:ℝ)
      (8905743/9698440:ℝ) (43/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0026).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_8_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x) ≤ (4429427551/58982400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_8_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^8*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 8 (3/4:ℝ) (1/1:ℝ)
      (8905743/9698440:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0026).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_8_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^8*thetaSecondMode x) ≤ (242461/23592960000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 8 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_lower_10_003 :
    (124531867/230686720000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^10*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 10 (3/4:ℝ) (1/1:ℝ)
      (178703525/192823536:ℝ) (31/5000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0027).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_first_cell_upper_10_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^10*thetaFirstMode x) ≤ (157806951707/2768240640000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 10 (3/4:ℝ) (1/1:ℝ)
      (4469/2000000000:ℝ) (3/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.1 (thetaTenth_node_0028).2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_lower_10_003 :
    (0/1:ℝ) ≤ ∫ x in (3/4:ℝ)..(1/1:ℝ), x^10*thetaSecondMode x := by
  have h := thetaSecondMode_weighted_cell_lower 10 (3/4:ℝ) (1/1:ℝ)
      (178703525/192823536:ℝ) (0/1:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass])
    (thetaTenth_node_0027).2.2.1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaTenth_second_cell_upper_10_003 :
    (∫ x in (3/4:ℝ)..(1/1:ℝ), x^10*thetaSecondMode x) ≤ (4017157/461373440000000000:ℝ) := by
  have h := thetaSecondMode_weighted_cell_upper 10 (3/4:ℝ) (1/1:ℝ)
      (1/10000000000:ℝ) (1/10000000000:ℝ)
    (by norm_num) (by norm_num) (thetaTenth_node_0021).2.2.2 (thetaTenth_node_0028).2.2.2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
