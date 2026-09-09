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

theorem thetaFirstMode_refined_cell_lower_6_032 :
    (3065917113851268507023/5044031582654955520000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/8:ℝ) (33/256:ℝ) (2148278933255/16913827039232:ℝ) (371234625647/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0196).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^6*thetaFirstMode x) ≤ (35041873345314135690167/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/8:ℝ) (33/256:ℝ) (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_033 :
    (8922722249002409223139/12610078956637388800000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (33/256:ℝ) (17/128:ℝ) (2655697006585/20285249878016:ℝ) (900838553917/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0202).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^6*thetaFirstMode x) ≤ (285550559171257531129661/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (33/256:ℝ) (17/128:ℝ) (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_034 :
    (2582293059408801564087/3152519739159347200000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (17/128:ℝ) (35/256:ℝ) (3262570400103/24199058905088:ℝ) (218543051877/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0208).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^6*thetaFirstMode x) ≤ (9444605696098252427263/11529215046068469760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/128:ℝ) (35/256:ℝ) (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_035 :
    (9515387840174085183659/10088063165309911040000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (35/256:ℝ) (9/64:ℝ) (3984641617817/28722928068608:ℝ) (678465449279/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0214).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^6*thetaFirstMode x) ≤ (339864316646019771837/360287970189639680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (35/256:ℝ) (9/64:ℝ) (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_036 :
    (54511853252513382473081/50440315826549555200000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (9/64:ℝ) (37/256:ℝ) (4839586825255/33930676299776:ℝ) (3290246102813/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0220).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^6*thetaFirstMode x) ≤ (13629150972550040903329/12610078956637388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/64:ℝ) (37/256:ℝ) (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_037 :
    (31080616899599513881037/25220157913274777600000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (37/256:ℝ) (19/128:ℝ) (5847188792025/39902628780032:ℝ) (1595210775743/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0226).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^6*thetaFirstMode x) ≤ (248667035673315736155729/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (37/256:ℝ) (19/128:ℝ) (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_038 :
    (1764105291822026438001/1261007895663738880000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (19/128:ℝ) (39/256:ℝ) (7029519853895/46725988530176:ℝ) (77320732023/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0232).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^6*thetaFirstMode x) ≤ (282282432904300941946063/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/128:ℝ) (39/256:ℝ) (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_039 :
    (79758981677527337257907/50440315826549555200000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (39/256:ℝ) (5/32:ℝ) (8411135176633/54495218321408:ℝ) (2997444537467/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0238).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^6*thetaFirstMode x) ≤ (45580774249319899206199/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (39/256:ℝ) (5/32:ℝ) (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_040 :
    (89782537129841869879137/50440315826549555200000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/32:ℝ) (41/256:ℝ) (10019276603847/63312432908288:ℝ) (2904242146377/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0244).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^6*thetaFirstMode x) ≤ (359164004030157323431831/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/32:ℝ) (41/256:ℝ) (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_041 :
    (100670404927731951886611/50440315826549555200000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (41/256:ℝ) (21/128:ℝ) (11884087371065/73287801583616:ℝ) (2813196532533/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0250).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^6*thetaFirstMode x) ≤ (161088131650165827864193/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (41/256:ℝ) (21/128:ℝ) (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_042 :
    (112456382947201452896599/50440315826549555200000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (21/128:ℝ) (43/256:ℝ) (14038837968295/84539961055232:ℝ) (2724281740861/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0256).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^6*thetaFirstMode x) ≤ (899739246852351404552663/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/128:ℝ) (43/256:ℝ) (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_043 :
    (125172281542406029071943/50440315826549555200000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (43/256:ℝ) (11/64:ℝ) (16520163433305/97196438644736:ℝ) (2637471456499/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0262).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^6*thetaFirstMode x) ≤ (500739166251689444503391/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (43/256:ℝ) (11/64:ℝ) (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_044 :
    (69423835442352910338329/25220157913274777600000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (11/64:ℝ) (45/256:ℝ) (19368312357863/111394085808128:ℝ) (1276369512389/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0268).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^6*thetaFirstMode x) ≤ (34715454817918746462659/12610078956637388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/64:ℝ) (45/256:ℝ) (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_045 :
    (21929947975446092959819/7205759403792793600000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (45/256:ℝ) (23/128:ℝ) (22627407889177/127279521978368:ℝ) (2470057471063/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0274).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^6*thetaFirstMode x) ≤ (1228204669826507488344417/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (45/256:ℝ) (23/128:ℝ) (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_046 :
    (84591269962111618832647/25220157913274777600000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (23/128:ℝ) (47/256:ℝ) (26345721008775/145009588729856:ℝ) (1194699760201/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0280).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^6*thetaFirstMode x) ≤ (270720733657014056798577/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/128:ℝ) (47/256:ℝ) (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_047 :
    (185887800151698960991889/50440315826549555200000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (47/256:ℝ) (3/16:ℝ) (30575956371065/164751814264832:ℝ) (2310737617121/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0286).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^6*thetaFirstMode x) ≤ (1487262966755087374371383/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (47/256:ℝ) (3/16:ℝ) (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_048 :
    (203643673840118359052831/50440315826549555200000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/16:ℝ) (49/256:ℝ) (35375550983815/186684888221696:ℝ) (2234043944303/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0292).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^6*thetaFirstMode x) ≤ (162932870589139250520741/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/16:ℝ) (49/256:ℝ) (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_049 :
    (27808132397337762862437/6305039478318694400000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (49/256:ℝ) (25/128:ℝ) (40806986012793/210999146805248:ℝ) (269911305387/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0298).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^6*thetaFirstMode x) ≤ (889960076786263951600023/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (49/256:ℝ) (25/128:ℝ) (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_050 :
    (121181655314783698828063/25220157913274777600000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (25/128:ℝ) (51/256:ℝ) (46938111992807/237897068238848:ℝ) (1043224416013/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0304).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^6*thetaFirstMode x) ≤ (1939128227815505328052189/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/128:ℝ) (51/256:ℝ) (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_051 :
    (32918258804988581694113/6305039478318694400000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (51/256:ℝ) (13/64:ℝ) (53842487727385/267593778538496:ℝ) (251936328269/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0310).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^6*thetaFirstMode x) ≤ (421402829704913084700279/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (51/256:ℝ) (13/64:ℝ) (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_052 :
    (71354279339872023357579/12610078956637388800000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (13/64:ℝ) (53/256:ℝ) (61599733159335/300317567608832:ℝ) (486596789031/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0316).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^6*thetaFirstMode x) ≤ (2283608226853796287331391/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/64:ℝ) (53/256:ℝ) (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_053 :
    (308576233559956664582667/50440315826549555200000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (53/256:ℝ) (27/128:ℝ) (70295896494425/336310415661056:ℝ) (1879109587161/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0322).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^6*thetaFirstMode x) ≤ (617227200033460784269071/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (53/256:ℝ) (27/128:ℝ) (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_054 :
    (332819090624196593513997/50440315826549555200000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (27/128:ℝ) (55/256:ℝ) (80023835860423/375828529952768:ℝ) (1813628937867/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0328).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^6*thetaFirstMode x) ≤ (1331440659715688067085683/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/128:ℝ) (55/256:ℝ) (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_055 :
    (179068577692484528854339/25220157913274777600000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (55/256:ℝ) (7/32:ℝ) (90883615783737/419142891849728:ℝ) (874958049499/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0334).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^6*thetaFirstMode x) ≤ (14327287978903778860333/2017612633061982208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (55/256:ℝ) (7/32:ℝ) (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_056 :
    (384517616229676488280797/50440315826549555200000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (7/32:ℝ) (57/256:ℝ) (102982918765895/466539814209536:ℝ) (1687941852021/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0340).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^6*thetaFirstMode x) ≤ (192283450640173918548443/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/32:ℝ) (57/256:ℝ) (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_057 :
    (29424523600580281300893/3602879701896396800000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (57/256:ℝ) (29/128:ℝ) (116437472242105/518321509087232:ℝ) (813838443789/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0346).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^6*thetaFirstMode x) ≤ (1647988545956844147786841/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (57/256:ℝ) (29/128:ℝ) (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_058 :
    (440392792727881586430129/50440315826549555200000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (29/128:ℝ) (59/256:ℝ) (131371491204135/574806665762816:ℝ) (1569091823787/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0352).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^6*thetaFirstMode x) ≤ (440451408378845088781483/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/128:ℝ) (59/256:ℝ) (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_059 :
    (117460031474968762237109/12610078956637388800000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (59/256:ℝ) (15/64:ℝ) (147918136769753/636331039090688:ℝ) (378039306089/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0358).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^6*thetaFirstMode x) ≤ (3759230781339562136777943/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (59/256:ℝ) (15/64:ℝ) (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_060 :
    (500255092685565274879277/50440315826549555200000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (15/64:ℝ) (61/256:ℝ) (166219990980967/703248048171008:ℝ) (1456843616537/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0364).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^6*thetaFirstMode x) ≤ (400259379679224517869721/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/64:ℝ) (61/256:ℝ) (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_061 :
    (265801564928031148110093/25220157913274777600000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (61/256:ℝ) (31/128:ℝ) (186429548113305/775929385342976:ℝ) (701560754439/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0370).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^6*thetaFirstMode x) ≤ (106335596570322536287529/10088063165309911040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (61/256:ℝ) (31/128:ℝ) (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_062 :
    (80549343408374217945353/7205759403792793600000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (31/128:ℝ) (63/256:ℝ) (208709722778375/854765635500032:ℝ) (1350961408769/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0376).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^6*thetaFirstMode x) ≤ (4511410361195781060053627/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/128:ℝ) (63/256:ℝ) (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_063 :
    (596938887962743231662553/50440315826549555200000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (63/256:ℝ) (1/4:ℝ) (233234375101945/940166905726976:ℝ) (1300333839769/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0382).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x) ≤ (298513070175821744665007/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (63/256:ℝ) (1/4:ℝ) (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
