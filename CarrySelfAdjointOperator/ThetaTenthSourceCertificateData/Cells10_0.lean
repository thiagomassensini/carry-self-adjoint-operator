import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature0

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^10*thetaFirstMode x) ≤ (1/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (0/1:ℝ) (1/256:ℝ)
    (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ) (882017793809669459/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^10*thetaFirstMode x) ≤ (1/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/256:ℝ) (1/128:ℝ)
    (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_001 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^10*thetaFirstMode x) ≤ (1/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/128:ℝ) (3/256:ℝ)
    (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (176197573183638029/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_002 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^10*thetaFirstMode x) ≤ (47/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/256:ℝ) (1/64:ℝ)
    (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_003 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^10*thetaFirstMode x) ≤ (509/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/64:ℝ) (5/256:ℝ)
    (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ) (351573408933338897/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_004 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^10*thetaFirstMode x) ≤ (1749/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/256:ℝ) (3/128:ℝ)
    (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ) (219381292635168023/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_005 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^10*thetaFirstMode x) ≤ (4393/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/128:ℝ) (7/256:ℝ)
    (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_006 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^10*thetaFirstMode x) ≤ (5623/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/256:ℝ) (1/32:ℝ)
    (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_007 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^10*thetaFirstMode x) ≤ (236531/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/32:ℝ) (9/256:ℝ)
    (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_008 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^10*thetaFirstMode x) ≤ (695141/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/256:ℝ) (5/128:ℝ)
    (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_009 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^10*thetaFirstMode x) ≤ (73281/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/128:ℝ) (11/256:ℝ)
    (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ) (433367564585813153/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_010 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^10*thetaFirstMode x) ≤ (8829441/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/256:ℝ) (3/64:ℝ)
    (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_011 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^10*thetaFirstMode x) ≤ (19741931/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/64:ℝ) (13/256:ℝ)
    (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ) (430353464465377497/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_012 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^10*thetaFirstMode x) ≤ (20712229/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/256:ℝ) (7/128:ℝ)
    (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_013 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^10*thetaFirstMode x) ≤ (41151969/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/128:ℝ) (15/256:ℝ)
    (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_014 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^10*thetaFirstMode x) ≤ (155955029/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/256:ℝ) (1/16:ℝ)
    (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_015 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^10*thetaFirstMode x) ≤ (17717939/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/16:ℝ) (17/256:ℝ)
    (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_016 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^10*thetaFirstMode x) ≤ (496727381/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/256:ℝ) (9/128:ℝ)
    (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_017 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^10*thetaFirstMode x) ≤ (21059293/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/128:ℝ) (19/256:ℝ)
    (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_018 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^10*thetaFirstMode x) ≤ (27745697/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (19/256:ℝ) (5/64:ℝ)
    (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_019 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^10*thetaFirstMode x) ≤ (2225149739/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/64:ℝ) (21/256:ℝ)
    (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_020 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^10*thetaFirstMode x) ≤ (3484670987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (21/256:ℝ) (11/128:ℝ)
    (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (12846388361106899/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_021 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^10*thetaFirstMode x) ≤ (5339545729/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/128:ℝ) (23/256:ℝ)
    (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (326719829522905161/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_022 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^10*thetaFirstMode x) ≤ (2005104387/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/256:ℝ) (3/32:ℝ)
    (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_023 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^10*thetaFirstMode x) ≤ (5914513817/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/32:ℝ) (25/256:ℝ)
    (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ) (805453755869069143/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_024 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^10*thetaFirstMode x) ≤ (17154771677/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/256:ℝ) (13/128:ℝ)
    (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_025 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^10*thetaFirstMode x) ≤ (24493860653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/128:ℝ) (27/256:ℝ)
    (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_026 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^10*thetaFirstMode x) ≤ (34471268553/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/256:ℝ) (7/64:ℝ)
    (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_027 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^10*thetaFirstMode x) ≤ (47865630177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/64:ℝ) (29/256:ℝ)
    (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ) (97556613961683183/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_028 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^10*thetaFirstMode x) ≤ (65637227263/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/256:ℝ) (15/128:ℝ)
    (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_029 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^10*thetaFirstMode x) ≤ (88959171619/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/128:ℝ) (31/256:ℝ)
    (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_030 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^10*thetaFirstMode x) ≤ (7453241229/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/256:ℝ) (1/8:ℝ)
    (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_031 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
