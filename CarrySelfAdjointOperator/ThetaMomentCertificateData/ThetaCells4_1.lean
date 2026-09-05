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

theorem thetaFirstMode_cell_lower_4_032 :
    (34227782742307493/85899345920000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/4:ℝ) (33/128:ℝ) (1088630725/4286178048:ℝ) (6132955013/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_131).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_032 :
    (∫ x in (1/4:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x) ≤ (410978346541404587/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/4:ℝ) (33/128:ℝ) (12759714529/1000000000000:ℝ) (236125737/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_128).2 (thetaFirstMode_node_132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_033 :
    (35728251315916007/85899345920000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (33/128:ℝ) (17/64:ℝ) (1266682235/4838423808:ℝ) (5671123097/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_135).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_033 :
    (∫ x in (33/128:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x) ≤ (107251107514709767/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (33/128:ℝ) (17/64:ℝ) (236125737/20000000000:ℝ) (5455038997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_132).2 (thetaFirstMode_node_136).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_034 :
    (37113727363375547/85899345920000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/64:ℝ) (35/128:ℝ) (489102015/1814131456:ℝ) (5237279897/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_139).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_034 :
    (∫ x in (17/64:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x) ≤ (148550293810879183/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/64:ℝ) (35/128:ℝ) (5455038997/500000000000:ℝ) (10068754379/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_136).2 (thetaFirstMode_node_140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_035 :
    (76746180772843549/171798691840000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (35/128:ℝ) (9/32:ℝ) (1692583555/6101223168:ℝ) (9660532849/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_143).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_035 :
    (∫ x in (35/128:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x) ≤ (460784119225142039/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (35/128:ℝ) (9/32:ℝ) (10068754379/1000000000000:ℝ) (580000141/62500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_140).2 (thetaFirstMode_node_144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_036 :
    (78993332144500037/171798691840000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/32:ℝ) (37/128:ℝ) (1944720365/6818135808:ℝ) (8897868977/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_147).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_036 :
    (∫ x in (9/32:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x) ≤ (79047985086789581/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/32:ℝ) (37/128:ℝ) (580000141/62500000000:ℝ) (4270766243/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_144).2 (thetaFirstMode_node_148).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_037 :
    (8095262008638387/17179869184000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (37/128:ℝ) (19/64:ℝ) (742016625/2532150016:ℝ) (818429817/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_151).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_037 :
    (∫ x in (37/128:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x) ≤ (81010729448025011/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (37/128:ℝ) (19/64:ℝ) (4270766243/500000000000:ℝ) (1962771279/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_148).2 (thetaFirstMode_node_152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_038 :
    (82610934071599641/171798691840000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/64:ℝ) (39/128:ℝ) (2539036885/8439575808:ℝ) (7517581311/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_155).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_038 :
    (∫ x in (19/64:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x) ≤ (82672450976568113/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/64:ℝ) (39/128:ℝ) (1962771279/250000000000:ℝ) (3603216861/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_152).2 (thetaFirstMode_node_156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_039 :
    (20989602940044013/42949672960000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (39/128:ℝ) (5/16:ℝ) (2886281195/9351015168:ℝ) (1723878613/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_159).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_039 :
    (∫ x in (39/128:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x) ≤ (21005815598221101/42949672960000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (39/128:ℝ) (5/16:ℝ) (3603216861/500000000000:ℝ) (3302694747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_156).2 (thetaFirstMode_node_160).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_040 :
    (42494230912226621/85899345920000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/16:ℝ) (41/128:ℝ) (1090173735/3444787456:ℝ) (3157966421/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_163).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_040 :
    (∫ x in (5/16:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x) ≤ (170113094884713073/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/16:ℝ) (41/128:ℝ) (3302694747/500000000000:ℝ) (6045805081/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_160).2 (thetaFirstMode_node_164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_041 :
    (21424435294483677/42949672960000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (41/128:ℝ) (21/64:ℝ) (3694637515/11393303808:ℝ) (1444178667/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_167).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_041 :
    (∫ x in (41/128:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x) ≤ (10721117314831321/21474836480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (41/128:ℝ) (21/64:ℝ) (6045805081/1000000000000:ℝ) (5525578159/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_164).2 (thetaFirstMode_node_168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_042 :
    (86086089252325353/171798691840000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/64:ℝ) (43/128:ℝ) (4161656525/12531618048:ℝ) (5275784523/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_171).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_042 :
    (∫ x in (21/64:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x) ≤ (34464100477991661/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/64:ℝ) (43/128:ℝ) (5525578159/1000000000000:ℝ) (1260663679/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_168).2 (thetaFirstMode_node_172).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_043 :
    (21539105555842807/42949672960000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (43/128:ℝ) (11/32:ℝ) (1558251345/4584391936:ℝ) (1202779147/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_175).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_043 :
    (∫ x in (43/128:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x) ≤ (172466757569646937/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (43/128:ℝ) (11/32:ℝ) (1260663679/250000000000:ℝ) (4595032071/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_172).2 (thetaFirstMode_node_176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_044 :
    (10739323838265091/21474836480000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/32:ℝ) (45/128:ℝ) (5237258845/15061939968:ℝ) (547592191/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_179).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_044 :
    (∫ x in (11/32:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x) ≤ (515964900892018307/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/32:ℝ) (45/128:ℝ) (4595032071/1000000000000:ℝ) (1045190393/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_176).2 (thetaFirstMode_node_180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_045 :
    (85369204253123123/171798691840000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (45/128:ℝ) (23/64:ℝ) (5852656355/16461965568:ℝ) (3982729073/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_183).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_045 :
    (∫ x in (45/128:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x) ≤ (128176731934267183/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (45/128:ℝ) (23/64:ℝ) (1045190393/250000000000:ℝ) (474743879/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_180).2 (thetaFirstMode_node_184).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_046 :
    (84531427250705703/171798691840000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/64:ℝ) (47/128:ℝ) (2174864055/5985799936:ℝ) (3615230313/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_187).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_046 :
    (∫ x in (23/64:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x) ≤ (42307769065122049/85899345920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/64:ℝ) (47/128:ℝ) (474743879/125000000000:ℝ) (861191709/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_184).2 (thetaFirstMode_node_188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_047 :
    (41707375194198967/85899345920000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (47/128:ℝ) (3/8:ℝ) (7256875675/19552482048:ℝ) (1638219847/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_191).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_047 :
    (∫ x in (47/128:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x) ≤ (501004648075874977/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (47/128:ℝ) (3/8:ℝ) (861191709/250000000000:ℝ) (3119435773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_188).2 (thetaFirstMode_node_192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_048 :
    (41017370909167631/85899345920000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/8:ℝ) (49/128:ℝ) (8053483685/21251543808:ℝ) (1482308351/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_195).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_048 :
    (∫ x in (3/8:ℝ)..(49/128:ℝ), x^4*thetaFirstMode x) ≤ (492734508004703579/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/8:ℝ) (49/128:ℝ) (3119435773/1000000000000:ℝ) (1410123283/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_192).2 (thetaFirstMode_node_196).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_049 :
    (80408783128842513/171798691840000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (49/128:ℝ) (25/64:ℝ) (2972854665/7686336256:ℝ) (2678083263/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_199).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_049 :
    (∫ x in (49/128:ℝ)..(25/64:ℝ), x^4*thetaFirstMode x) ≤ (160995674852996441/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (49/128:ℝ) (25/64:ℝ) (1410123283/500000000000:ℝ) (2545551093/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_196).2 (thetaFirstMode_node_200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_050 :
    (78555794044859087/171798691840000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/64:ℝ) (51/128:ℝ) (9856439005/24979392768:ℝ) (2415224837/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_203).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_050 :
    (∫ x in (25/64:ℝ)..(51/128:ℝ), x^4*thetaFirstMode x) ≤ (117968914321923077/257698037760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/64:ℝ) (51/128:ℝ) (2545551093/1000000000000:ℝ) (2293765343/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_200).2 (thetaFirstMode_node_204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_051 :
    (76495950801769411/171798691840000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (51/128:ℝ) (13/32:ℝ) (10871609315/27017303808:ℝ) (2174491231/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_207).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_051 :
    (∫ x in (51/128:ℝ)..(13/32:ℝ), x^4*thetaFirstMode x) ≤ (91904284059764233/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (51/128:ℝ) (13/32:ℝ) (2293765343/1000000000000:ℝ) (1031685033/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_204).2 (thetaFirstMode_node_208).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_052 :
    (74250402608847157/171798691840000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/32:ℝ) (53/128:ℝ) (3989585775/9725814016:ℝ) (1954397137/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_211).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_052 :
    (∫ x in (13/32:ℝ)..(53/128:ℝ), x^4*thetaFirstMode x) ≤ (148683726592493121/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/32:ℝ) (53/128:ℝ) (1031685033/500000000000:ℝ) (370582233/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_208).2 (thetaFirstMode_node_212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_053 :
    (71840989465634249/171798691840000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (53/128:ℝ) (27/64:ℝ) (13152750835/31464599808:ℝ) (1753522379/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_215).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_053 :
    (∫ x in (53/128:ℝ)..(27/64:ℝ), x^4*thetaFirstMode x) ≤ (71932660626933813/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (53/128:ℝ) (27/64:ℝ) (370582233/200000000000:ℝ) (1660999809/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_212).2 (thetaFirstMode_node_216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_054 :
    (69289966604044569/171798691840000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/64:ℝ) (55/128:ℝ) (14428646645/33883661568:ℝ) (1570511919/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_219).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_054 :
    (∫ x in (27/64:ℝ)..(55/128:ℝ), x^4*thetaFirstMode x) ≤ (416289306644290123/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/64:ℝ) (55/128:ℝ) (1660999809/1000000000000:ℝ) (743156149/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_216).2 (thetaFirstMode_node_220).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_055 :
    (66619737980068199/171798691840000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (55/128:ℝ) (7/16:ℝ) (5267231385/12146534656:ℝ) (1404075599/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_223).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_055 :
    (∫ x in (55/128:ℝ)..(7/16:ℝ), x^4*thetaFirstMode x) ≤ (66710941815824523/171798691840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (55/128:ℝ) (7/16:ℝ) (743156149/500000000000:ℝ) (16594871/12500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_220).2 (thetaFirstMode_node_224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_056 :
    (15963150708862553/42949672960000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/16:ℝ) (57/128:ℝ) (17277338965/39137495808:ℝ) (313246913/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_227).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_056 :
    (∫ x in (7/16:ℝ)..(57/128:ℝ), x^4*thetaFirstMode x) ≤ (383658824991011471/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/16:ℝ) (57/128:ℝ) (16594871/12500000000:ℝ) (1183637139/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_224).2 (thetaFirstMode_node_228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_057 :
    (61010517383857647/171798691840000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (57/128:ℝ) (29/64:ℝ) (18861226475/41982498048:ℝ) (1116085977/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_231).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_057 :
    (∫ x in (57/128:ℝ)..(29/64:ℝ), x^4*thetaFirstMode x) ≤ (366600615122911799/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (57/128:ℝ) (29/64:ℝ) (1183637139/1000000000000:ℝ) (263330791/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_228).2 (thetaFirstMode_node_232).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_058 :
    (58114875379190289/171798691840000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/64:ℝ) (59/128:ℝ) (6853068495/14993287936:ℝ) (992271219/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_235).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_058 :
    (∫ x in (29/64:ℝ)..(59/128:ℝ), x^4*thetaFirstMode x) ≤ (7275405111819101/21474836480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/64:ℝ) (59/128:ℝ) (263330791/250000000000:ℝ) (233894629/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_232).2 (thetaFirstMode_node_236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_059 :
    (27593154048051119/85899345920000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (59/128:ℝ) (15/32:ℝ) (22377331795/48134938368:ℝ) (440252819/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_239).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_059 :
    (∫ x in (59/128:ℝ)..(15/32:ℝ), x^4*thetaFirstMode x) ≤ (165819589307289193/515396075520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (59/128:ℝ) (15/32:ℝ) (233894629/250000000000:ℝ) (414697503/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_236).2 (thetaFirstMode_node_240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_060 :
    (52244506947103713/171798691840000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/32:ℝ) (61/128:ℝ) (24321871805/51453159168:ℝ) (779811813/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_243).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_060 :
    (∫ x in (15/32:ℝ)..(61/128:ℝ), x^4*thetaFirstMode x) ≤ (313978048900689781/1030792151040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/32:ℝ) (61/128:ℝ) (414697503/500000000000:ℝ) (733824107/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_240).2 (thetaFirstMode_node_244).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_061 :
    (49308068205501677/171798691840000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (61/128:ℝ) (31/64:ℝ) (8799768705/18313351936:ℝ) (689271167/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_247).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_061 :
    (∫ x in (61/128:ℝ)..(31/64:ℝ), x^4*thetaFirstMode x) ≤ (19756515431383953/68719476736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (61/128:ℝ) (31/64:ℝ) (733824107/1000000000000:ℝ) (161993851/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_244).2 (thetaFirstMode_node_248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_062 :
    (46394362362674249/171798691840000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/64:ℝ) (63/128:ℝ) (28616333125/58601250048:ℝ) (608022359/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_251).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_062 :
    (∫ x in (31/64:ℝ)..(63/128:ℝ), x^4*thetaFirstMode x) ≤ (55770511015803479/206158430208000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/64:ℝ) (63/128:ℝ) (161993851/250000000000:ℝ) (571014911/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_248).2 (thetaFirstMode_node_252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_4_063 :
    (2719964186400601/10737418240000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (63/128:ℝ) (1/2:ℝ) (30979872635/62442455808:ℝ) (33453721/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_255).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_4_063 :
    (∫ x in (63/128:ℝ)..(1/2:ℝ), x^4*thetaFirstMode x) ≤ (87196286502387049/343597383680000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (63/128:ℝ) (1/2:ℝ) (571014911/1000000000000:ℝ) (7846301/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_252).2 (thetaFirstMode_node_256).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
