import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature0

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_000 :
    (333813059263875362423/1000000000000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (0/1:ℝ) (1/256:ℝ)
    (1/512:ℝ) (8545502162793/100000000000000:ℝ) (882017793809669459/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_000
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0001).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^0*thetaFirstMode x) ≤ (166906847367862918827/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (0/1:ℝ) (1/256:ℝ)
    (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ) (882017793809669459/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_001 :
    (163146915618854629353/500000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/256:ℝ) (1/128:ℝ)
    (3/512:ℝ) (1044126246807/12500000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_001
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0007).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^0*thetaFirstMode x) ≤ (81573615560813339397/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/256:ℝ) (1/128:ℝ)
    (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_001 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_002 :
    (318882105575785373599/1000000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/128:ℝ) (3/256:ℝ)
    (5/512:ℝ) (408163493967/5000000000000:ℝ) (176197573183638029/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_002
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0013).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^0*thetaFirstMode x) ≤ (159441366030210720151/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/128:ℝ) (3/256:ℝ)
    (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (176197573183638029/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_002 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_003 :
    (311577809158651992019/1000000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/256:ℝ) (1/64:ℝ)
    (7/512:ℝ) (7976280005461/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_003
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0019).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^0*thetaFirstMode x) ≤ (311578431069707734711/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/256:ℝ) (1/64:ℝ)
    (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_003 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_004 :
    (76095209453552835667/250000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/64:ℝ) (5/256:ℝ)
    (9/512:ℝ) (7792037685867/100000000000000:ℝ) (351573408933338897/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_004
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0025).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^0*thetaFirstMode x) ≤ (304381455099292158413/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/64:ℝ) (5/256:ℝ)
    (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ) (351573408933338897/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_004 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_005 :
    (297291056446703878403/1000000000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/256:ℝ) (3/128:ℝ)
    (11/512:ℝ) (380526973097/5000000000000:ℝ) (219381292635168023/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_005
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0031).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^0*thetaFirstMode x) ≤ (148645834527456277847/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/256:ℝ) (3/128:ℝ)
    (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ) (219381292635168023/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_005 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_006 :
    (290308299191668717633/1000000000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/128:ℝ) (7/256:ℝ)
    (13/512:ℝ) (7431781087363/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_006
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0037).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^0*thetaFirstMode x) ≤ (290308907071643033483/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/128:ℝ) (7/256:ℝ)
    (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_006 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_007 :
    (141716184792130780773/500000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/256:ℝ) (1/32:ℝ)
    (15/512:ℝ) (7255757532429/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_007
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0043).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^0*thetaFirstMode x) ≤ (70858243171306719227/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/256:ℝ) (1/32:ℝ)
    (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_007 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_008 :
    (17291440046874835023/62500000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/32:ℝ) (9/256:ℝ)
    (17/512:ℝ) (1770615747231/25000000000000:ℝ) (871793499300891957/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_008
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0049).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^0*thetaFirstMode x) ≤ (69165909755694679191/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/32:ℝ) (9/256:ℝ)
    (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_008 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_009 :
    (16875003475999670939/62500000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (9/256:ℝ) (5/128:ℝ)
    (19/512:ℝ) (1382378175107/20000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_009
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0055).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^0*thetaFirstMode x) ≤ (270000649011643342451/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/256:ℝ) (5/128:ℝ)
    (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_009 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_010 :
    (263443127138433948091/1000000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/128:ℝ) (11/256:ℝ)
    (21/512:ℝ) (6744033843673/100000000000000:ℝ) (433367564585813153/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_010
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0061).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^0*thetaFirstMode x) ≤ (65860928902194158767/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/128:ℝ) (11/256:ℝ)
    (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ) (433367564585813153/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_010 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_011 :
    (256991938548841977927/1000000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (11/256:ℝ) (3/64:ℝ)
    (23/512:ℝ) (3289441891889/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_011
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0067).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^0*thetaFirstMode x) ≤ (128496261024087709573/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/256:ℝ) (3/64:ℝ)
    (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_011 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_012 :
    (62661535906089940313/250000000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/64:ℝ) (13/256:ℝ)
    (25/512:ℝ) (3208215916119/50000000000000:ℝ) (430353464465377497/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_012
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0073).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^0*thetaFirstMode x) ≤ (50129344421166251749/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/64:ℝ) (13/256:ℝ)
    (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ) (430353464465377497/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_012 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_013 :
    (244405366968204673587/1000000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (13/256:ℝ) (7/128:ℝ)
    (27/512:ℝ) (6256668378569/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_013
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0079).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^0*thetaFirstMode x) ≤ (9776237615479563613/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/256:ℝ) (7/128:ℝ)
    (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_013 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_014 :
    (29783650539787138251/125000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/128:ℝ) (15/256:ℝ)
    (29/512:ℝ) (1524895768329/25000000000000:ℝ) (106716101744309517/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_014
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0085).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^0*thetaFirstMode x) ≤ (14891860789412080499/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/128:ℝ) (15/256:ℝ)
    (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_014 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_015 :
    (232237222868617576877/1000000000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (15/256:ℝ) (1/16:ℝ)
    (31/512:ℝ) (148629120907/2500000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_015
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0091).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^0*thetaFirstMode x) ≤ (58059446507619922499/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/256:ℝ) (1/16:ℝ)
    (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_015 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_016 :
    (226308961606621399427/1000000000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/16:ℝ) (17/256:ℝ)
    (33/512:ℝ) (1448350466289/25000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_016
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0097).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^0*thetaFirstMode x) ≤ (45261903915335815229/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/16:ℝ) (17/256:ℝ)
    (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_016 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_017 :
    (220483931678814794193/1000000000000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (17/256:ℝ) (9/128:ℝ)
    (35/512:ℝ) (1411070411223/25000000000000:ℝ) (841530099567674249/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_017
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0103).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^0*thetaFirstMode x) ≤ (220484484415007130363/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/256:ℝ) (9/128:ℝ)
    (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_017 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_018 :
    (26845202095214981919/125000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (9/128:ℝ) (19/256:ℝ)
    (37/512:ℝ) (2748895478593/50000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_018
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0109).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^0*thetaFirstMode x) ≤ (42952432844784714109/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/128:ℝ) (19/256:ℝ)
    (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_018 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_019 :
    (209141473458270232393/1000000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (19/256:ℝ) (5/64:ℝ)
    (39/512:ℝ) (2676957945317/50000000000000:ℝ) (832280181221222783/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_019
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0115).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^0*thetaFirstMode x) ≤ (52285503902129532241/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/256:ℝ) (5/64:ℝ)
    (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_019 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_020 :
    (101811465856281599053/500000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/64:ℝ) (21/256:ℝ)
    (41/512:ℝ) (1303160462837/25000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_020
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0121).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^0*thetaFirstMode x) ≤ (203623468512490791287/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/64:ℝ) (21/256:ℝ)
    (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_020 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_021 :
    (198205395234770147609/1000000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (21/256:ℝ) (11/128:ℝ)
    (43/512:ℝ) (2536976786917/50000000000000:ℝ) (12846388361106899/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_021
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0127).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^0*thetaFirstMode x) ≤ (99102963323667352391/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/256:ℝ) (11/128:ℝ)
    (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (12846388361106899/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_021 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_022 :
    (192888241948777039363/1000000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (11/128:ℝ) (23/256:ℝ)
    (45/512:ℝ) (1234458783113/25000000000000:ℝ) (326719829522905161/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_022
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0133).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^0*thetaFirstMode x) ≤ (96444383969308898137/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/128:ℝ) (23/256:ℝ)
    (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (326719829522905161/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_022 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_023 :
    (18767082445463216739/100000000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (23/256:ℝ) (3/32:ℝ)
    (47/512:ℝ) (960853990651/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_023
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0139).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^0*thetaFirstMode x) ≤ (187671344987415352719/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/256:ℝ) (3/32:ℝ)
    (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_023 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_024 :
    (36510494101143255501/200000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/32:ℝ) (25/256:ℝ)
    (49/512:ℝ) (934648165241/20000000000000:ℝ) (805453755869069143/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_024
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0145).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^0*thetaFirstMode x) ≤ (182552985548059632489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/32:ℝ) (25/256:ℝ)
    (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ) (805453755869069143/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_024 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_025 :
    (22191560437921995053/125000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (25/256:ℝ) (13/128:ℝ)
    (51/512:ℝ) (1136182479459/25000000000000:ℝ) (799485594891087013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_025
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0151).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^0*thetaFirstMode x) ≤ (177532993023306672901/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/256:ℝ) (13/128:ℝ)
    (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_025 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_026 :
    (43152535751521291511/250000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (13/128:ℝ) (27/256:ℝ)
    (53/512:ℝ) (4418718784289/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_026
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0157).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^0*thetaFirstMode x) ≤ (86305323486561318331/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/128:ℝ) (27/256:ℝ)
    (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_026 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_027 :
    (33556941050744967397/200000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (27/256:ℝ) (7/64:ℝ)
    (55/512:ℝ) (2147594192367/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_027
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0163).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^0*thetaFirstMode x) ≤ (167785203638429232279/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/256:ℝ) (7/64:ℝ)
    (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_027 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_028 :
    (163055403705023679859/1000000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/64:ℝ) (29/256:ℝ)
    (57/512:ℝ) (4174119095129/100000000000000:ℝ) (97556613961683183/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_028
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0169).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^0*thetaFirstMode x) ≤ (163055896480030765281/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/64:ℝ) (29/256:ℝ)
    (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ) (97556613961683183/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_028 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_029 :
    (79210724796309393307/500000000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (29/256:ℝ) (15/128:ℝ)
    (59/512:ℝ) (405549072243/10000000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_029
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0175).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^0*thetaFirstMode x) ≤ (9901371045666304017/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/256:ℝ) (15/128:ℝ)
    (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_029 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_030 :
    (153882032485767896903/1000000000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (15/128:ℝ) (31/256:ℝ)
    (61/512:ℝ) (3939282518997/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_030
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0181).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^0*thetaFirstMode x) ≤ (153882513961686862443/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/128:ℝ) (31/256:ℝ)
    (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_030 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_031 :
    (14943632087220387631/100000000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (31/256:ℝ) (1/8:ℝ)
    (63/512:ℝ) (382547319749/10000000000000:ℝ) (759825734717146723/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_031
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0187).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^0*thetaFirstMode x) ≤ (14943679666236959113/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/256:ℝ) (1/8:ℝ)
    (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_031 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator
