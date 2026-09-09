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

theorem thetaFirstMode_refined_cell_lower_0_096 :
    (304224667353/25600000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/8:ℝ) (97/256:ℝ) (193/512:ℝ) (304224667353/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0577).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x) ≤ (76076421373/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/8:ℝ) (97/256:ℝ) (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_097 :
    (56497619/5000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (97/256:ℝ) (49/128:ℝ) (195/512:ℝ) (56497619/19531250000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0583).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x) ≤ (289346225107/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (97/256:ℝ) (49/128:ℝ) (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_098 :
    (274933345111/25600000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (49/128:ℝ) (99/256:ℝ) (197/512:ℝ) (274933345111/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0589).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x) ≤ (110003683783/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (49/128:ℝ) (99/256:ℝ) (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_099 :
    (65300267963/6400000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (99/256:ℝ) (25/64:ℝ) (199/512:ℝ) (65300267963/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0595).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x) ≤ (130637217921/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (99/256:ℝ) (25/64:ℝ) (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_100 :
    (248051188579/25600000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/64:ℝ) (101/256:ℝ) (201/512:ℝ) (248051188579/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0601).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x) ≤ (124061051789/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/64:ℝ) (101/256:ℝ) (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_101 :
    (235464298503/25600000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (101/256:ℝ) (51/128:ℝ) (203/512:ℝ) (235464298503/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0607).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x) ≤ (471065632121/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (101/256:ℝ) (51/128:ℝ) (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_102 :
    (223421410591/25600000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (51/128:ℝ) (103/256:ℝ) (205/512:ℝ) (223421410591/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0613).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x) ≤ (55871895597/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (51/128:ℝ) (103/256:ℝ) (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_103 :
    (211903940763/25600000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (103/256:ℝ) (13/32:ℝ) (207/512:ℝ) (211903940763/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0619).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x) ≤ (211967818561/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (103/256:ℝ) (13/32:ℝ) (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_104 :
    (6277928521/800000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/32:ℝ) (105/256:ℝ) (209/512:ℝ) (6277928521/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0625).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x) ≤ (401910696517/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/32:ℝ) (105/256:ℝ) (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_105 :
    (38074591613/5120000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (105/256:ℝ) (53/128:ℝ) (211/512:ℝ) (38074591613/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0631).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x) ≤ (47608100801/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (105/256:ℝ) (53/128:ℝ) (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_106 :
    (90162158371/12800000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (53/128:ℝ) (107/256:ℝ) (213/512:ℝ) (90162158371/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0637).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x) ≤ (90190811563/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (53/128:ℝ) (107/256:ℝ) (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_107 :
    (42682709031/6400000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (107/256:ℝ) (27/64:ℝ) (215/512:ℝ) (42682709031/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0643).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x) ≤ (170786055323/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (107/256:ℝ) (27/64:ℝ) (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_108 :
    (80787985213/12800000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/64:ℝ) (109/256:ℝ) (217/512:ℝ) (80787985213/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0649).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x) ≤ (323258307687/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/64:ℝ) (109/256:ℝ) (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_109 :
    (7642178973/1280000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (109/256:ℝ) (55/128:ℝ) (219/512:ℝ) (7642178973/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0655).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x) ≤ (76447389143/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (109/256:ℝ) (55/128:ℝ) (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_110 :
    (36129481767/6400000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (55/128:ℝ) (111/256:ℝ) (221/512:ℝ) (36129481767/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0661).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x) ≤ (289134384469/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (55/128:ℝ) (111/256:ℝ) (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_111 :
    (68291839601/12800000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (111/256:ℝ) (7/16:ℝ) (223/512:ℝ) (68291839601/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0667).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x) ≤ (273262122677/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (111/256:ℝ) (7/16:ℝ) (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_112 :
    (129025901651/25600000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/16:ℝ) (113/256:ℝ) (225/512:ℝ) (129025901651/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0673).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x) ≤ (258142902091/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/16:ℝ) (113/256:ℝ) (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_113 :
    (24366011489/5120000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (113/256:ℝ) (57/128:ℝ) (227/512:ℝ) (24366011489/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0679).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x) ≤ (121873824001/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (113/256:ℝ) (57/128:ℝ) (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_114 :
    (57491001961/12800000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (57/128:ℝ) (115/256:ℝ) (229/512:ℝ) (57491001961/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0685).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x) ≤ (230048074247/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (57/128:ℝ) (115/256:ℝ) (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_115 :
    (216935979/51200000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (115/256:ℝ) (29/64:ℝ) (231/512:ℝ) (216935979/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0691).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x) ≤ (217016676741/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (115/256:ℝ) (29/64:ℝ) (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_116 :
    (51137325069/12800000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/64:ℝ) (117/256:ℝ) (233/512:ℝ) (51137325069/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0697).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x) ≤ (102313363207/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/64:ℝ) (117/256:ℝ) (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_117 :
    (19277801103/5120000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (117/256:ℝ) (59/128:ℝ) (235/512:ℝ) (19277801103/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0703).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x) ≤ (96426130783/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (117/256:ℝ) (59/128:ℝ) (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_118 :
    (22699613733/6400000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (59/128:ℝ) (119/256:ℝ) (237/512:ℝ) (22699613733/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0709).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x) ≤ (90834039839/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (59/128:ℝ) (119/256:ℝ) (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_119 :
    (85490772961/25600000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (119/256:ℝ) (15/32:ℝ) (239/512:ℝ) (85490772961/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0715).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x) ≤ (42762432177/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (119/256:ℝ) (15/32:ℝ) (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_120 :
    (314273847/100000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/32:ℝ) (121/256:ℝ) (241/512:ℝ) (314273847/390625000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0721).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x) ≤ (40243374469/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/32:ℝ) (121/256:ℝ) (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_121 :
    (75676961597/25600000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (121/256:ℝ) (61/128:ℝ) (243/512:ℝ) (75676961597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0727).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x) ≤ (151416407987/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (121/256:ℝ) (61/128:ℝ) (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_122 :
    (35574107533/12800000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (61/128:ℝ) (123/256:ℝ) (245/512:ℝ) (35574107533/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0733).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x) ≤ (142356201309/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (61/128:ℝ) (123/256:ℝ) (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_123 :
    (4178568283/1600000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (123/256:ℝ) (31/64:ℝ) (247/512:ℝ) (4178568283/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0739).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x) ≤ (133771331027/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (123/256:ℝ) (31/64:ℝ) (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_124 :
    (62793171289/25600000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/64:ℝ) (125/256:ℝ) (249/512:ℝ) (62793171289/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0745).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x) ≤ (125640950309/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/64:ℝ) (125/256:ℝ) (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_125 :
    (58946373017/25600000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (125/256:ℝ) (63/128:ℝ) (251/512:ℝ) (58946373017/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0751).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x) ≤ (117944901003/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (125/256:ℝ) (63/128:ℝ) (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_126 :
    (27653478959/12800000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (63/128:ℝ) (127/256:ℝ) (253/512:ℝ) (27653478959/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0757).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x) ≤ (55331850999/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (63/128:ℝ) (127/256:ℝ) (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_127 :
    (51865518759/25600000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (127/256:ℝ) (1/2:ℝ) (255/512:ℝ) (51865518759/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0763).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x) ≤ (25944634317/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (127/256:ℝ) (1/2:ℝ) (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
