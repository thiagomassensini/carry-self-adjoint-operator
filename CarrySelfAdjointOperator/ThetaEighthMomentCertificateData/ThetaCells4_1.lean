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

theorem thetaFirstMode_refined_cell_lower_4_032 :
    (4144321922057372569/109951162777600000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/8:ℝ) (33/256:ℝ) (1088630725/8572356096:ℝ) (742582132729/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0195).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^4*thetaFirstMode x) ≤ (124339669930249793887/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/8:ℝ) (33/256:ℝ) (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_033 :
    (22704619887412441479/549755813888000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (33/256:ℝ) (17/128:ℝ) (1266682235/9676847616:ℝ) (3603890185209/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0201).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x) ≤ (136238910190024164511/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (33/256:ℝ) (17/128:ℝ) (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_034 :
    (24782723084604308407/549755813888000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/128:ℝ) (35/256:ℝ) (489102015/3628262912:ℝ) (3497198115757/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0207).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^4*thetaFirstMode x) ≤ (49569599486506605221/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/128:ℝ) (35/256:ℝ) (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_035 :
    (13476757724303463671/274877906944000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (35/256:ℝ) (9/64:ℝ) (1692583555/12202446336:ℝ) (1696405728371/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0213).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x) ≤ (26955819156100809713/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (35/256:ℝ) (9/64:ℝ) (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_036 :
    (29214173566011742671/549755813888000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/64:ℝ) (37/256:ℝ) (1944720365/13636271616:ℝ) (3290706716691/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0219).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^4*thetaFirstMode x) ≤ (87650160830739913739/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/64:ℝ) (37/256:ℝ) (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_037 :
    (394518360725829439/6871947673600000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (37/256:ℝ) (19/128:ℝ) (742016625/5064300032:ℝ) (39885749149/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0225).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x) ≤ (15782137456199608677/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (37/256:ℝ) (19/128:ℝ) (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_038 :
    (33991783733332053861/549755813888000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/128:ℝ) (39/256:ℝ) (2539036885/16879151616:ℝ) (3093246686931/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0231).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^4*thetaFirstMode x) ≤ (8498716454847568969/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/128:ℝ) (39/256:ℝ) (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_039 :
    (36501129259196816709/549755813888000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (39/256:ℝ) (5/32:ℝ) (2886281195/18702030336:ℝ) (2997842134509/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0237).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x) ≤ (9126126093366913659/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (39/256:ℝ) (5/32:ℝ) (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_040 :
    (39085164212732761651/549755813888000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/32:ℝ) (41/256:ℝ) (1090173735/6889574912:ℝ) (2904621015451/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0243).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^4*thetaFirstMode x) ≤ (19544424809217577193/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/32:ℝ) (41/256:ℝ) (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_041 :
    (4173921537683007513/54975581388800000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (41/256:ℝ) (21/128:ℝ) (3694637515/22786607616:ℝ) (281355767823/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0249).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x) ≤ (16697291423920318521/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (41/256:ℝ) (21/128:ℝ) (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_042 :
    (8891659788886767379/109951162777600000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/128:ℝ) (43/256:ℝ) (4161656525/25063236096:ℝ) (544925219689/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0255).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^4*thetaFirstMode x) ≤ (88925315135074403143/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/128:ℝ) (43/256:ℝ) (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_043 :
    (47237142898769986419/549755813888000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (43/256:ℝ) (11/64:ℝ) (1558251345/9168783872:ℝ) (2637799898199/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0261).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x) ≤ (11810466188536832183/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (43/256:ℝ) (11/64:ℝ) (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_044 :
    (50070210237197313657/549755813888000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/64:ℝ) (45/256:ℝ) (5237258845/30123879936:ℝ) (2553052365357/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0267).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^4*thetaFirstMode x) ≤ (150225939591773245967/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/64:ℝ) (45/256:ℝ) (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_045 :
    (66189653639191941/687194767360000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (45/256:ℝ) (23/128:ℝ) (5852656355/32923931136:ℝ) (3087945591/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0273).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x) ≤ (317743349265366374459/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (45/256:ℝ) (23/128:ℝ) (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_046 :
    (22350274541430729/219902325555200000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/128:ℝ) (47/256:ℝ) (2174864055/11971599872:ℝ) (955873959/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0279).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^4*thetaFirstMode x) ≤ (22352642082249957273/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/128:ℝ) (47/256:ℝ) (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_047 :
    (2353436578878689029/21990232555520000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (47/256:ℝ) (3/16:ℝ) (7256875675/39104964096:ℝ) (92440401589/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0285).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x) ≤ (117684536026888224103/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (47/256:ℝ) (3/16:ℝ) (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_048 :
    (30913027492725887157/274877906944000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/16:ℝ) (49/256:ℝ) (8053483685/42503087616:ℝ) (1117152020997/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0291).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^4*thetaFirstMode x) ≤ (37099716534557795471/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/16:ℝ) (49/256:ℝ) (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_049 :
    (64839614989810743409/549755813888000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (49/256:ℝ) (25/128:ℝ) (2972854665/15372672512:ℝ) (2159538808159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0297).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x) ≤ (64846890749484308631/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (49/256:ℝ) (25/128:ℝ) (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_050 :
    (13573997326732344711/109951162777600000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/128:ℝ) (51/256:ℝ) (9856439005/49958785536:ℝ) (417337204461/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0303).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^4*thetaFirstMode x) ≤ (407266496989474057931/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/128:ℝ) (51/256:ℝ) (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_051 :
    (35455236399490532449/274877906944000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (51/256:ℝ) (13/64:ℝ) (10871609315/54034607616:ℝ) (1007858583829/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0309).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x) ≤ (28367495889703567371/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (51/256:ℝ) (13/64:ℝ) (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_052 :
    (18488578169495431733/137438953472000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/64:ℝ) (53/256:ℝ) (3989585775/19451628032:ℝ) (486650886353/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0315).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^4*thetaFirstMode x) ≤ (147926200537456831491/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/64:ℝ) (53/256:ℝ) (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_053 :
    (19248676785846702753/137438953472000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (53/256:ℝ) (27/128:ℝ) (13152750835/62929199616:ℝ) (469829073363/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0321).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x) ≤ (77004031597493040759/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (53/256:ℝ) (27/128:ℝ) (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_054 :
    (80024843815395513053/549755813888000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/128:ℝ) (55/256:ℝ) (14428646645/67767323136:ℝ) (1813826405003/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0327).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^4*thetaFirstMode x) ≤ (20008680217239542501/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/128:ℝ) (55/256:ℝ) (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_055 :
    (5189870108322574101/34359738368000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (55/256:ℝ) (7/32:ℝ) (5267231385/24293069312:ℝ) (109381546701/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0333).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x) ≤ (83048366604286295209/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (55/256:ℝ) (7/32:ℝ) (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_056 :
    (21506793884119528809/137438953472000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/32:ℝ) (57/256:ℝ) (17277338965/78274991616:ℝ) (422030519889/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0339).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^4*thetaFirstMode x) ≤ (258114608615648577239/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/32:ℝ) (57/256:ℝ) (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_057 :
    (88985899080643233939/549755813888000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (57/256:ℝ) (29/128:ℝ) (18861226475/83964996096:ℝ) (1627849072149/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0345).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x) ≤ (133496284352136387589/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (57/256:ℝ) (29/128:ℝ) (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_058 :
    (4595373419965099607/27487790694400000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/128:ℝ) (59/256:ℝ) (6853068495/29986575872:ℝ) (78462816197/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0351).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^4*thetaFirstMode x) ≤ (91919702048032144969/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/128:ℝ) (59/256:ℝ) (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_059 :
    (94785363942941397803/549755813888000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (59/256:ℝ) (15/64:ℝ) (22377331795/96269876736:ℝ) (1512314380703/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0357).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x) ≤ (37919288013090915807/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (59/256:ℝ) (15/64:ℝ) (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_060 :
    (97613192023939048793/549755813888000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/64:ℝ) (61/256:ℝ) (24321871805/102906318336:ℝ) (1456993752893/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0363).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^4*thetaFirstMode x) ≤ (58576009432688104697/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/64:ℝ) (61/256:ℝ) (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_061 :
    (25096176350414022513/137438953472000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (61/256:ℝ) (31/128:ℝ) (8799768705/36626703872:ℝ) (350816233323/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0369).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x) ≤ (5019942052266510893/27487790694400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (61/256:ℝ) (31/128:ℝ) (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_062 :
    (6443363934592615877/34359738368000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/128:ℝ) (63/256:ℝ) (28616333125/117202500096:ℝ) (84443650907/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0375).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^4*thetaFirstMode x) ≤ (206217228014155593127/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/128:ℝ) (63/256:ℝ) (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_063 :
    (21146929673553383159/109951162777600000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (63/256:ℝ) (1/4:ℝ) (30979872635/124884911616:ℝ) (260092941239/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0381).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x) ≤ (105750104042265691657/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (63/256:ℝ) (1/4:ℝ) (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
