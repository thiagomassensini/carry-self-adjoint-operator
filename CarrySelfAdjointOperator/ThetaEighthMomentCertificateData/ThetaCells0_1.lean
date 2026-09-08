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

theorem thetaFirstMode_refined_cell_lower_0_032 :
    (3714040946007/25600000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/8:ℝ) (33/256:ℝ) (65/512:ℝ) (3714040946007/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0193).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x) ≤ (7428680162459/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/8:ℝ) (33/256:ℝ) (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_033 :
    (360496344351/2560000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (33/256:ℝ) (17/128:ℝ) (67/512:ℝ) (360496344351/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0199).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x) ≤ (7210519245287/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (33/256:ℝ) (17/128:ℝ) (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_034 :
    (3498217875589/25600000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/128:ℝ) (35/256:ℝ) (69/512:ℝ) (3498217875589/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0205).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x) ≤ (6997022080199/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/128:ℝ) (35/256:ℝ) (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_035 :
    (3393780950527/25600000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (35/256:ℝ) (9/64:ℝ) (71/512:ℝ) (3393780950527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0211).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x) ≤ (3394071043917/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (35/256:ℝ) (9/64:ℝ) (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_036 :
    (658325783107/5120000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/64:ℝ) (37/256:ℝ) (73/512:ℝ) (658325783107/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0217).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x) ≤ (658383176681/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/64:ℝ) (37/256:ℝ) (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_037 :
    (1595868786681/12800000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (37/256:ℝ) (19/128:ℝ) (75/512:ℝ) (1595868786681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0223).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x) ≤ (1596010681707/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (37/256:ℝ) (19/128:ℝ) (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_038 :
    (1547041149511/12800000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/128:ℝ) (39/256:ℝ) (77/512:ℝ) (1547041149511/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0229).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x) ≤ (386795357639/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/128:ℝ) (39/256:ℝ) (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_039 :
    (1499319028417/12800000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (39/256:ℝ) (5/32:ℝ) (79/512:ℝ) (1499319028417/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0235).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x) ≤ (1499457671489/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (39/256:ℝ) (5/32:ℝ) (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_040 :
    (2905379417603/25600000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/32:ℝ) (41/256:ℝ) (81/512:ℝ) (2905379417603/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0241).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x) ≤ (726413345503/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/32:ℝ) (41/256:ℝ) (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_041 :
    (175892536003/1600000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (41/256:ℝ) (21/128:ℝ) (83/512:ℝ) (175892536003/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0247).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x) ≤ (5629102350239/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (41/256:ℝ) (21/128:ℝ) (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_042 :
    (545063073663/5120000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/128:ℝ) (43/256:ℝ) (85/512:ℝ) (545063073663/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0253).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x) ≤ (5451165121373/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/128:ℝ) (43/256:ℝ) (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_043 :
    (2576618447/25000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (43/256:ℝ) (11/64:ℝ) (87/512:ℝ) (2576618447/97656250000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0259).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x) ≤ (1319360518141/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (43/256:ℝ) (11/64:ℝ) (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_044 :
    (319209939079/3200000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/64:ℝ) (45/256:ℝ) (89/512:ℝ) (319209939079/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0265).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x) ≤ (2553939776513/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/64:ℝ) (45/256:ℝ) (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_045 :
    (2470954904391/25600000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (45/256:ℝ) (23/128:ℝ) (91/512:ℝ) (2470954904391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0271).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x) ≤ (4942423302003/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (45/256:ℝ) (23/128:ℝ) (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_046 :
    (2390256045431/25600000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/128:ℝ) (47/256:ℝ) (93/512:ℝ) (2390256045431/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0277).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x) ≤ (4781018484927/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/128:ℝ) (47/256:ℝ) (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_047 :
    (92462209897/1024000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (47/256:ℝ) (3/16:ℝ) (95/512:ℝ) (92462209897/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0283).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x) ≤ (4623609729713/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (47/256:ℝ) (3/16:ℝ) (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_048 :
    (1117412285759/12800000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/16:ℝ) (49/256:ℝ) (97/512:ℝ) (1117412285759/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0289).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x) ≤ (447014116323/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/16:ℝ) (49/256:ℝ) (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_049 :
    (540008961651/6400000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (49/256:ℝ) (25/128:ℝ) (99/512:ℝ) (540008961651/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0295).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x) ≤ (2160278223933/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (49/256:ℝ) (25/128:ℝ) (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_050 :
    (2087160687639/25600000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/128:ℝ) (51/256:ℝ) (101/512:ℝ) (2087160687639/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0301).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x) ≤ (834959763623/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/128:ℝ) (51/256:ℝ) (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_051 :
    (504042628491/6400000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (51/256:ℝ) (13/64:ℝ) (103/512:ℝ) (504042628491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0307).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x) ≤ (4032811117257/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (51/256:ℝ) (13/64:ℝ) (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_052 :
    (194703656763/2560000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/64:ℝ) (53/256:ℝ) (105/512:ℝ) (194703656763/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0313).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x) ≤ (3894535833981/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/64:ℝ) (53/256:ℝ) (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_053 :
    (1879729931687/25600000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (53/256:ℝ) (27/128:ℝ) (107/512:ℝ) (1879729931687/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0319).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x) ≤ (1879957569477/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (53/256:ℝ) (27/128:ℝ) (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_054 :
    (1814221548443/25600000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/128:ℝ) (55/256:ℝ) (109/512:ℝ) (1814221548443/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0325).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x) ≤ (45361136517/640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/128:ℝ) (55/256:ℝ) (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_055 :
    (1750482237681/25600000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (55/256:ℝ) (7/32:ℝ) (111/512:ℝ) (1750482237681/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0331).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x) ≤ (1750702412641/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (55/256:ℝ) (7/32:ℝ) (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_056 :
    (1688482714757/25600000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/32:ℝ) (57/256:ℝ) (113/512:ℝ) (1688482714757/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0337).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x) ≤ (1688699142973/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/32:ℝ) (57/256:ℝ) (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_057 :
    (1628193608631/25600000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (57/256:ℝ) (29/128:ℝ) (115/512:ℝ) (1628193608631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0343).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x) ≤ (814203141443/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (57/256:ℝ) (29/128:ℝ) (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_058 :
    (12262386561/200000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/128:ℝ) (59/256:ℝ) (117/512:ℝ) (12262386561/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0349).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x) ≤ (1569794395099/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/128:ℝ) (59/256:ℝ) (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_059 :
    (189078604763/3200000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (59/256:ℝ) (15/64:ℝ) (119/512:ℝ) (189078604763/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0355).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x) ≤ (3025667983269/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (59/256:ℝ) (15/64:ℝ) (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_060 :
    (728647080143/12800000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/64:ℝ) (61/256:ℝ) (121/512:ℝ) (728647080143/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0361).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x) ≤ (291499110289/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/64:ℝ) (61/256:ℝ) (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_061 :
    (280710381513/5120000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (61/256:ℝ) (31/128:ℝ) (123/512:ℝ) (280710381513/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0367).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x) ≤ (14037495379/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (61/256:ℝ) (31/128:ℝ) (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_062 :
    (1351372542879/25600000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/128:ℝ) (63/256:ℝ) (125/512:ℝ) (1351372542879/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0373).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x) ≤ (2703132832157/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/128:ℝ) (63/256:ℝ) (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_063 :
    (162590818501/3200000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (63/256:ℝ) (1/4:ℝ) (127/512:ℝ) (162590818501/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0379).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x) ≤ (1300916669857/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (63/256:ℝ) (1/4:ℝ) (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
