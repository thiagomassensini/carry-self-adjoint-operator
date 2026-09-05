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

theorem thetaFirstMode_cell_lower_2_032 :
    (4860768168673/786432000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/4:ℝ) (33/128:ℝ) (412035/1622528:ℝ) (1533849217/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_130).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_032 :
    (∫ x in (1/4:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x) ≤ (51879114646989/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/4:ℝ) (33/128:ℝ) (12759714529/1000000000000:ℝ) (236125737/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_128).2 (thetaFirstMode_node_132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_033 :
    (19102169325421/3145728000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (33/128:ℝ) (17/64:ℝ) (451245/1723904:ℝ) (5673349963/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_134).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_033 :
    (∫ x in (33/128:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x) ≤ (1592832863189/262144000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (33/128:ℝ) (17/64:ℝ) (236125737/20000000000:ℝ) (5455038997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_132).2 (thetaFirstMode_node_136).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_034 :
    (2494610064437/419430400000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/64:ℝ) (35/128:ℝ) (492867/1828352:ℝ) (2095723941/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_138).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_034 :
    (∫ x in (17/64:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x) ≤ (149772769478531/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/64:ℝ) (35/128:ℝ) (5455038997/500000000000:ℝ) (10068754379/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_136).2 (thetaFirstMode_node_140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_035 :
    (18270230493913/3145728000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (35/128:ℝ) (9/32:ℝ) (536973/1935872:ℝ) (4832115973/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_142).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_035 :
    (∫ x in (35/128:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x) ≤ (146259296273137/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (35/128:ℝ) (9/32:ℝ) (10068754379/1000000000000:ℝ) (580000141/62500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_140).2 (thetaFirstMode_node_144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_036 :
    (741213460659/131072000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/32:ℝ) (37/128:ℝ) (583635/2046464:ℝ) (556327341/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_146).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_036 :
    (∫ x in (9/32:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x) ≤ (71205720217169/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/32:ℝ) (37/128:ℝ) (580000141/62500000000:ℝ) (4270766243/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_144).2 (thetaFirstMode_node_148).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_037 :
    (8635621837261/1572864000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (37/128:ℝ) (19/64:ℝ) (632925/2160128:ℝ) (2046840919/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_150).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_037 :
    (∫ x in (37/128:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x) ≤ (69134561886463/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (37/128:ℝ) (19/64:ℝ) (4270766243/500000000000:ℝ) (1962771279/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_148).2 (thetaFirstMode_node_152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_038 :
    (6688616362033/1258291200000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/64:ℝ) (39/128:ℝ) (684915/2276864:ℝ) (1504073839/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_154).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_038 :
    (∫ x in (19/64:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x) ≤ (22311989064639/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/64:ℝ) (39/128:ℝ) (1962771279/250000000000:ℝ) (3603216861/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_152).2 (thetaFirstMode_node_156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_039 :
    (16144881311233/3145728000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (39/128:ℝ) (5/16:ℝ) (739677/2396672:ℝ) (3449023993/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_158).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_039 :
    (∫ x in (39/128:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x) ≤ (2154313440903/419430400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (39/128:ℝ) (5/16:ℝ) (3603216861/500000000000:ℝ) (3302694747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_156).2 (thetaFirstMode_node_160).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_040 :
    (6218405317201/1258291200000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/16:ℝ) (41/128:ℝ) (797283/2519552:ℝ) (1263646681/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_162).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_040 :
    (∫ x in (5/16:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x) ≤ (124467730669697/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/16:ℝ) (41/128:ℝ) (3302694747/500000000000:ℝ) (6045805081/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_160).2 (thetaFirstMode_node_164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_041 :
    (1244127894971/262144000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (41/128:ℝ) (21/64:ℝ) (857805/2645504:ℝ) (722350239/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_166).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_041 :
    (∫ x in (41/128:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x) ≤ (59767747783817/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (41/128:ℝ) (21/64:ℝ) (6045805081/1000000000000:ℝ) (5525578159/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_164).2 (thetaFirstMode_node_168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_042 :
    (14299864547197/3145728000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/64:ℝ) (43/128:ℝ) (921315/2774528:ℝ) (2638838263/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_170).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_042 :
    (∫ x in (21/64:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x) ≤ (22899491881319/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/64:ℝ) (43/128:ℝ) (5525578159/1000000000000:ℝ) (1260663679/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_168).2 (thetaFirstMode_node_172).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_043 :
    (27322435858907/6291456000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (43/128:ℝ) (11/32:ℝ) (987885/2906624:ℝ) (4812829991/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_174).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_043 :
    (∫ x in (43/128:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x) ≤ (109387352609483/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (43/128:ℝ) (11/32:ℝ) (1260663679/250000000000:ℝ) (4595032071/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_172).2 (thetaFirstMode_node_176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_044 :
    (13017585440561/3145728000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/32:ℝ) (45/128:ℝ) (1057587/3041792:ℝ) (2191143821/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_178).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_044 :
    (∫ x in (11/32:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x) ≤ (20847421998343/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/32:ℝ) (45/128:ℝ) (4595032071/1000000000000:ℝ) (1045190393/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_176).2 (thetaFirstMode_node_180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_045 :
    (4949086279789/1258291200000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (45/128:ℝ) (23/64:ℝ) (1130493/3180032:ℝ) (796825999/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_182).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_045 :
    (∫ x in (45/128:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x) ≤ (24769183051937/6291456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (45/128:ℝ) (23/64:ℝ) (1045190393/250000000000:ℝ) (474743879/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_180).2 (thetaFirstMode_node_184).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_046 :
    (938408129087/251658240000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/64:ℝ) (47/128:ℝ) (1206675/3321344:ℝ) (144659801/40000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_186).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_046 :
    (∫ x in (23/64:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x) ≤ (23483543872301/6291456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/64:ℝ) (47/128:ℝ) (474743879/125000000000:ℝ) (861191709/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_184).2 (thetaFirstMode_node_188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_047 :
    (1386621249671/393216000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (47/128:ℝ) (3/8:ℝ) (1286205/3465728:ℝ) (204848759/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_190).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_047 :
    (∫ x in (47/128:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x) ≤ (88835268469657/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (47/128:ℝ) (3/8:ℝ) (861191709/250000000000:ℝ) (3119435773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_188).2 (thetaFirstMode_node_192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_048 :
    (1308034307351/393216000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/8:ℝ) (49/128:ℝ) (1369155/3613184:ℝ) (185352743/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_194).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_048 :
    (∫ x in (3/8:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x) ≤ (83803655179567/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/8:ℝ) (49/128:ℝ) (3119435773/1000000000000:ℝ) (1410123283/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_192).2 (thetaFirstMode_node_196).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_049 :
    (1312892179937/419430400000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (49/128:ℝ) (25/64:ℝ) (1455597/3763712:ℝ) (535801461/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_198).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_049 :
    (∫ x in (49/128:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x) ≤ (78860762330791/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (49/128:ℝ) (25/64:ℝ) (1410123283/500000000000:ℝ) (2545551093/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_196).2 (thetaFirstMode_node_200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_050 :
    (4813863831/1638400000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/64:ℝ) (51/128:ℝ) (1545603/3917312:ℝ) (1887543/781250000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_202).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_050 :
    (∫ x in (25/64:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x) ≤ (37012894871461/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/64:ℝ) (51/128:ℝ) (2545551093/1000000000000:ℝ) (2293765343/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_200).2 (thetaFirstMode_node_204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_051 :
    (17308354069421/6291456000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (51/128:ℝ) (13/32:ℝ) (1639245/4073984:ℝ) (2175236153/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_206).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_051 :
    (∫ x in (51/128:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x) ≤ (13863144437059/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (51/128:ℝ) (13/32:ℝ) (2293765343/1000000000000:ℝ) (1031685033/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_204).2 (thetaFirstMode_node_208).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_052 :
    (1347202456257/524288000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/32:ℝ) (53/128:ℝ) (1736595/4233728:ℝ) (488766159/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_210).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_052 :
    (∫ x in (13/32:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x) ≤ (21581786937891/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/32:ℝ) (53/128:ℝ) (1031685033/500000000000:ℝ) (370582233/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_208).2 (thetaFirstMode_node_212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_053 :
    (1882828202933/786432000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (53/128:ℝ) (27/64:ℝ) (1837725/4396544:ℝ) (219264959/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_214).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_053 :
    (∫ x in (53/128:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x) ≤ (314205065377/131072000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (53/128:ℝ) (27/64:ℝ) (370582233/200000000000:ℝ) (1660999809/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_212).2 (thetaFirstMode_node_216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_054 :
    (6999793786643/3145728000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/64:ℝ) (55/128:ℝ) (1942707/4562432:ℝ) (785522813/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_218).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_054 :
    (∫ x in (27/64:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x) ≤ (3738157028817/1677721600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/64:ℝ) (55/128:ℝ) (1660999809/1000000000000:ℝ) (743156149/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_216).2 (thetaFirstMode_node_220).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_055 :
    (432648769713/209715200000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (55/128:ℝ) (7/16:ℝ) (2051613/4731392:ℝ) (140455179/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_222).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_055 :
    (∫ x in (55/128:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x) ≤ (8664819691133/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (55/128:ℝ) (7/16:ℝ) (743156149/500000000000:ℝ) (16594871/12500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_220).2 (thetaFirstMode_node_224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_056 :
    (4001308534497/2097152000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/16:ℝ) (57/128:ℝ) (2164515/4903424:ℝ) (1253411883/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_226).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_056 :
    (∫ x in (7/16:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x) ≤ (16027923951331/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/16:ℝ) (57/128:ℝ) (16594871/12500000000:ℝ) (1183637139/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_224).2 (thetaFirstMode_node_228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_057 :
    (11074199800027/6291456000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (57/128:ℝ) (29/64:ℝ) (2281485/5078528:ℝ) (1116463333/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_230).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_057 :
    (∫ x in (57/128:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x) ≤ (14787277461263/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (57/128:ℝ) (29/64:ℝ) (1183637139/1000000000000:ℝ) (263330791/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_228).2 (thetaFirstMode_node_232).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_058 :
    (1698514892397/1048576000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/64:ℝ) (59/128:ℝ) (2402595/5256704:ℝ) (496303173/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_234).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_058 :
    (∫ x in (29/64:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x) ≤ (5103291371663/3145728000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/64:ℝ) (59/128:ℝ) (263330791/250000000000:ℝ) (233894629/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_232).2 (thetaFirstMode_node_236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_059 :
    (1559167717523/1048576000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (59/128:ℝ) (15/32:ℝ) (2527917/5437952:ℝ) (440401389/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_238).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_059 :
    (∫ x in (59/128:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x) ≤ (6246488619439/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (59/128:ℝ) (15/32:ℝ) (233894629/250000000000:ℝ) (414697503/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_236).2 (thetaFirstMode_node_240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_060 :
    (8566001719211/6291456000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/32:ℝ) (61/128:ℝ) (2657523/5622272:ℝ) (780074831/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_242).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_060 :
    (∫ x in (15/32:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x) ≤ (11439951360309/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/32:ℝ) (61/128:ℝ) (414697503/500000000000:ℝ) (733824107/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_240).2 (thetaFirstMode_node_244).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_061 :
    (81497887163/65536000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (61/128:ℝ) (31/64:ℝ) (2791485/5809664:ℝ) (21546987/31250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_246).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_061 :
    (∫ x in (61/128:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x) ≤ (2089866580811/1677721600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (61/128:ℝ) (31/64:ℝ) (733824107/1000000000000:ℝ) (161993851/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_244).2 (thetaFirstMode_node_248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_062 :
    (2375938877021/2097152000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/64:ℝ) (63/128:ℝ) (2929875/6000128:ℝ) (608227377/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_250).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_062 :
    (∫ x in (31/64:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x) ≤ (5712214988269/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/64:ℝ) (63/128:ℝ) (161993851/250000000000:ℝ) (571014911/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_248).2 (thetaFirstMode_node_252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_063 :
    (6477218417917/6291456000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (63/128:ℝ) (1/2:ℝ) (3072765/6193664:ℝ) (535440061/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_254).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_063 :
    (∫ x in (63/128:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x) ≤ (25955728606781/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (63/128:ℝ) (1/2:ℝ) (571014911/1000000000000:ℝ) (7846301/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_252).2 (thetaFirstMode_node_256).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator
