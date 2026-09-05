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

theorem thetaFirstMode_cell_lower_0_032 :
    (12275681449/128000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/4:ℝ) (33/128:ℝ) (65/256:ℝ) (12275681449/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_129).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_032 :
    (∫ x in (1/4:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x) ≤ (24566001379/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/4:ℝ) (33/128:ℝ) (12759714529/1000000000000:ℝ) (236125737/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_128).2 (thetaFirstMode_node_132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_033 :
    (11351157161/128000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (33/128:ℝ) (17/64:ℝ) (67/256:ℝ) (11351157161/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_133).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_033 :
    (∫ x in (33/128:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x) ≤ (5679091211/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (33/128:ℝ) (17/64:ℝ) (236125737/20000000000:ℝ) (5455038997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_132).2 (thetaFirstMode_node_136).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_034 :
    (5241341343/64000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/64:ℝ) (35/128:ℝ) (69/256:ℝ) (5241341343/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_137).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_034 :
    (∫ x in (17/64:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x) ≤ (20978832373/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/64:ℝ) (35/128:ℝ) (5455038997/500000000000:ℝ) (10068754379/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_136).2 (thetaFirstMode_node_140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_035 :
    (1933586749/25600000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (35/128:ℝ) (9/32:ℝ) (71/256:ℝ) (1933586749/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_141).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_035 :
    (∫ x in (35/128:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x) ≤ (3869751327/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (35/128:ℝ) (9/32:ℝ) (10068754379/1000000000000:ℝ) (580000141/62500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_140).2 (thetaFirstMode_node_144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_036 :
    (1780921661/25600000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/32:ℝ) (37/128:ℝ) (73/256:ℝ) (1780921661/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_145).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_036 :
    (∫ x in (9/32:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x) ≤ (8910767371/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/32:ℝ) (37/128:ℝ) (580000141/62500000000:ℝ) (4270766243/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_144).2 (thetaFirstMode_node_148).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_037 :
    (8190431269/128000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (37/128:ℝ) (19/64:ℝ) (75/256:ℝ) (8190431269/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_149).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_037 :
    (∫ x in (37/128:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x) ≤ (8196308801/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (37/128:ℝ) (19/64:ℝ) (4270766243/500000000000:ℝ) (1962771279/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_148).2 (thetaFirstMode_node_152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_038 :
    (3761579459/64000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/64:ℝ) (39/128:ℝ) (77/256:ℝ) (3761579459/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_153).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_038 :
    (∫ x in (19/64:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x) ≤ (7528759419/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/64:ℝ) (39/128:ℝ) (1962771279/250000000000:ℝ) (3603216861/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_152).2 (thetaFirstMode_node_156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_039 :
    (3450291571/64000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (39/128:ℝ) (5/16:ℝ) (79/256:ℝ) (3450291571/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_157).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_039 :
    (∫ x in (39/128:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x) ≤ (863238951/16000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (39/128:ℝ) (5/16:ℝ) (3603216861/500000000000:ℝ) (3302694747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_156).2 (thetaFirstMode_node_160).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_040 :
    (3160267699/64000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/16:ℝ) (41/128:ℝ) (81/256:ℝ) (3160267699/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_161).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_040 :
    (∫ x in (5/16:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x) ≤ (506047783/10240000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/16:ℝ) (41/128:ℝ) (3302694747/500000000000:ℝ) (6045805081/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_160).2 (thetaFirstMode_node_164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_041 :
    (5780890419/128000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (41/128:ℝ) (21/64:ℝ) (83/256:ℝ) (5780890419/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_165).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_041 :
    (∫ x in (41/128:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x) ≤ (289284581/6400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (41/128:ℝ) (21/64:ℝ) (6045805081/1000000000000:ℝ) (5525578159/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_164).2 (thetaFirstMode_node_168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_042 :
    (2639784823/64000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/64:ℝ) (43/128:ℝ) (85/256:ℝ) (2639784823/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_169).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_042 :
    (∫ x in (21/64:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x) ≤ (84545863/2048000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/64:ℝ) (43/128:ℝ) (5525578159/1000000000000:ℝ) (1260663679/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_168).2 (thetaFirstMode_node_172).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_043 :
    (4814544377/128000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (43/128:ℝ) (11/32:ℝ) (87/256:ℝ) (4814544377/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_173).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_043 :
    (∫ x in (43/128:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x) ≤ (9637686787/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (43/128:ℝ) (11/32:ℝ) (1260663679/250000000000:ℝ) (4595032071/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_172).2 (thetaFirstMode_node_176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_044 :
    (2191919313/64000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/32:ℝ) (45/128:ℝ) (89/256:ℝ) (2191919313/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_177).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_044 :
    (∫ x in (11/32:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x) ≤ (8775793643/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/32:ℝ) (45/128:ℝ) (4595032071/1000000000000:ℝ) (1045190393/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_176).2 (thetaFirstMode_node_180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_045 :
    (498191461/16000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (45/128:ℝ) (23/64:ℝ) (91/256:ℝ) (498191461/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_181).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_045 :
    (∫ x in (45/128:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x) ≤ (1994678151/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (45/128:ℝ) (23/64:ℝ) (1045190393/250000000000:ℝ) (474743879/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_180).2 (thetaFirstMode_node_184).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_046 :
    (1808880209/64000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/64:ℝ) (47/128:ℝ) (93/256:ℝ) (1808880209/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_185).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_046 :
    (∫ x in (23/64:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x) ≤ (1810679467/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/64:ℝ) (47/128:ℝ) (474743879/125000000000:ℝ) (861191709/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_184).2 (thetaFirstMode_node_188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_047 :
    (819680299/32000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (47/128:ℝ) (3/8:ℝ) (95/256:ℝ) (819680299/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_189).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_047 :
    (∫ x in (47/128:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x) ≤ (6564202609/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (47/128:ℝ) (3/8:ℝ) (861191709/250000000000:ℝ) (3119435773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_188).2 (thetaFirstMode_node_192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_048 :
    (1483335803/64000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/8:ℝ) (49/128:ℝ) (97/256:ℝ) (1483335803/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_193).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_048 :
    (∫ x in (3/8:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x) ≤ (5939682339/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/8:ℝ) (49/128:ℝ) (3119435773/1000000000000:ℝ) (1410123283/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_192).2 (thetaFirstMode_node_196).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_049 :
    (535986363/25600000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (49/128:ℝ) (25/64:ℝ) (99/256:ℝ) (535986363/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_197).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_049 :
    (∫ x in (49/128:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x) ≤ (5365797659/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (49/128:ℝ) (25/64:ℝ) (1410123283/500000000000:ℝ) (2545551093/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_196).2 (thetaFirstMode_node_200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_050 :
    (1208442829/64000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/64:ℝ) (51/128:ℝ) (101/256:ℝ) (1208442829/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_201).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_050 :
    (∫ x in (25/64:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x) ≤ (1209829109/64000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/64:ℝ) (51/128:ℝ) (2545551093/1000000000000:ℝ) (2293765343/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_200).2 (thetaFirstMode_node_204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_051 :
    (2175981439/128000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (51/128:ℝ) (13/32:ℝ) (103/256:ℝ) (2175981439/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_205).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_051 :
    (∫ x in (51/128:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x) ≤ (4357135409/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (51/128:ℝ) (13/32:ℝ) (2293765343/1000000000000:ℝ) (1031685033/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_204).2 (thetaFirstMode_node_208).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_052 :
    (1955732457/128000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/32:ℝ) (53/128:ℝ) (105/256:ℝ) (1955732457/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_209).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_052 :
    (∫ x in (13/32:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x) ≤ (3916281231/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/32:ℝ) (53/128:ℝ) (1031685033/500000000000:ℝ) (370582233/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_208).2 (thetaFirstMode_node_212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_053 :
    (1754717249/128000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (53/128:ℝ) (27/64:ℝ) (107/256:ℝ) (1754717249/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_213).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_053 :
    (∫ x in (53/128:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x) ≤ (1756955487/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (53/128:ℝ) (27/64:ℝ) (370582233/200000000000:ℝ) (1660999809/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_212).2 (thetaFirstMode_node_216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_054 :
    (314315917/25600000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/64:ℝ) (55/128:ℝ) (109/256:ℝ) (314315917/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_217).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_054 :
    (∫ x in (27/64:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x) ≤ (3147312107/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/64:ℝ) (55/128:ℝ) (1660999809/1000000000000:ℝ) (743156149/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_216).2 (thetaFirstMode_node_220).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_055 :
    (702514101/64000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (55/128:ℝ) (7/16:ℝ) (111/256:ℝ) (702514101/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_221).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_055 :
    (∫ x in (55/128:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x) ≤ (1406950989/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (55/128:ℝ) (7/16:ℝ) (743156149/500000000000:ℝ) (16594871/12500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_220).2 (thetaFirstMode_node_224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_056 :
    (1253836309/128000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/16:ℝ) (57/128:ℝ) (113/256:ℝ) (1253836309/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_225).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_056 :
    (∫ x in (7/16:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x) ≤ (2511226819/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/16:ℝ) (57/128:ℝ) (16594871/12500000000:ℝ) (1183637139/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_224).2 (thetaFirstMode_node_228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_057 :
    (1116840861/128000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (57/128:ℝ) (29/64:ℝ) (115/256:ℝ) (1116840861/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_229).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_057 :
    (∫ x in (57/128:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x) ≤ (2236960303/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (57/128:ℝ) (29/64:ℝ) (1183637139/1000000000000:ℝ) (263330791/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_228).2 (thetaFirstMode_node_232).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_058 :
    (992941623/128000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/64:ℝ) (59/128:ℝ) (117/256:ℝ) (992941623/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_233).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_058 :
    (∫ x in (29/64:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x) ≤ (24861271/3200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/64:ℝ) (59/128:ℝ) (263330791/250000000000:ℝ) (233894629/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_232).2 (thetaFirstMode_node_236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_059 :
    (881100049/128000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (59/128:ℝ) (15/32:ℝ) (119/256:ℝ) (881100049/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_237).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_059 :
    (∫ x in (59/128:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x) ≤ (882486761/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (59/128:ℝ) (15/32:ℝ) (233894629/250000000000:ℝ) (414697503/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_236).2 (thetaFirstMode_node_240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_060 :
    (195084491/32000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/32:ℝ) (61/128:ℝ) (121/256:ℝ) (195084491/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_241).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_060 :
    (∫ x in (15/32:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x) ≤ (1563219113/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/32:ℝ) (61/128:ℝ) (414697503/500000000000:ℝ) (733824107/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_240).2 (thetaFirstMode_node_244).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_061 :
    (689736103/128000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (61/128:ℝ) (31/64:ℝ) (123/256:ℝ) (689736103/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_245).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_061 :
    (∫ x in (61/128:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x) ≤ (1381799511/256000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (61/128:ℝ) (31/64:ℝ) (733824107/1000000000000:ℝ) (161993851/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_244).2 (thetaFirstMode_node_248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_062 :
    (608432483/128000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/64:ℝ) (63/128:ℝ) (125/256:ℝ) (608432483/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_249).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_062 :
    (∫ x in (31/64:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x) ≤ (243798063/51200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/64:ℝ) (63/128:ℝ) (161993851/250000000000:ℝ) (571014911/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_248).2 (thetaFirstMode_node_252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_0_063 :
    (66952583/16000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (63/128:ℝ) (1/2:ℝ) (127/256:ℝ) (66952583/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_253).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_0_063 :
    (∫ x in (63/128:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x) ≤ (42927127/10240000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (63/128:ℝ) (1/2:ℝ) (571014911/1000000000000:ℝ) (7846301/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_252).2 (thetaFirstMode_node_256).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
