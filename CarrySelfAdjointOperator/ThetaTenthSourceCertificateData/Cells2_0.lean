import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature0

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_000 :
    (337647259395917/200000000000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (0/1:ℝ) (1/256:ℝ)
    (3/1024:ℝ) (8497121034577/100000000000000:ℝ) (882017793809669459/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_000
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0002).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^2*thetaFirstMode x) ≤ (1688239139773553/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (0/1:ℝ) (1/256:ℝ)
    (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ) (882017793809669459/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_000 (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_001 :
    (11588840192743381/1000000000000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/256:ℝ) (1/128:ℝ)
    (45/7168:ℝ) (8332549067823/100000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_001
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0008).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x) ≤ (2897215534815037/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/256:ℝ) (1/128:ℝ)
    (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ) (1763262794674044371/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_001 (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_002 :
    (7692417767389567/250000000000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/128:ℝ) (3/256:ℝ)
    (195/19456:ℝ) (1630176684579/20000000000000:ℝ) (176197573183638029/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_002
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0014).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^2*thetaFirstMode x) ≤ (7692432763383861/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/128:ℝ) (3/256:ℝ)
    (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ) (176197573183638029/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_002 (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_003 :
    (14642958765046133/250000000000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/256:ℝ) (1/64:ℝ)
    (525/37888:ℝ) (7967503963091/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_003
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0020).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x) ≤ (5857195150258313/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/256:ℝ) (1/64:ℝ)
    (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ) (176017638148269469/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_003 (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_004 :
    (18871215366600819/200000000000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/64:ℝ) (5/256:ℝ)
    (1107/62464:ℝ) (3892647180663/50000000000000:ℝ) (351573408933338897/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_004
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0026).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^2*thetaFirstMode x) ≤ (94356267715189109/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/64:ℝ) (5/256:ℝ)
    (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ) (351573408933338897/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_004 (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_005 :
    (5500109349015457/40000000000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (5/256:ℝ) (3/128:ℝ)
    (2013/93184:ℝ) (950637162347/12500000000000:ℝ) (219381292635168023/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_005
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0032).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x) ≤ (2148484634149363/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/256:ℝ) (3/128:ℝ)
    (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ) (219381292635168023/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_005 (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_006 :
    (93705837873739249/500000000000000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/128:ℝ) (7/256:ℝ)
    (3315/130048:ℝ) (7427242473407/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_006
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0038).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^2*thetaFirstMode x) ≤ (93706033836214277/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/128:ℝ) (7/256:ℝ)
    (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ) (875864604429554181/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_006 (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_007 :
    (60875557909901969/250000000000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (7/256:ℝ) (1/32:ℝ)
    (5085/173056:ℝ) (7251882656567/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_007
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0044).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x) ≤ (30437843656831947/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/256:ℝ) (1/32:ℝ)
    (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ) (873953451803742743/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_007 (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_008 :
    (1220852404447081/4000000000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/32:ℝ) (9/256:ℝ)
    (7395/222208:ℝ) (3539548088001/50000000000000:ℝ) (871793499300891957/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_008
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0050).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^2*thetaFirstMode x) ≤ (305213760573758983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/32:ℝ) (9/256:ℝ)
    (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ) (871793499300891957/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_008 (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_009 :
    (186001126709726777/500000000000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (9/256:ℝ) (5/128:ℝ)
    (10317/277504:ℝ) (6908925377109/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_009
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0056).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x) ≤ (93000767602185197/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (9/256:ℝ) (5/128:ℝ)
    (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ) (1738773382538984943/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_009 (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_010 :
    (443346812437319589/1000000000000000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (5/128:ℝ) (11/256:ℝ)
    (13923/338944:ℝ) (52667135073/781250000000:ℝ) (433367564585813153/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_010
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0062).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^2*thetaFirstMode x) ≤ (88669560429671233/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/128:ℝ) (11/256:ℝ)
    (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ) (433367564585813153/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_010 (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_011 :
    (518742928401171089/1000000000000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (11/256:ℝ) (3/64:ℝ)
    (18285/406528:ℝ) (6576511656381/100000000000000:ℝ) (107980133847500327/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_011
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0068).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x) ≤ (259372052768758227/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (11/256:ℝ) (3/64:ℝ)
    (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ) (107980133847500327/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_011 (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_012 :
    (298852818263060337/500000000000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/64:ℝ) (13/256:ℝ)
    (23475/480256:ℝ) (6414285135459/100000000000000:ℝ) (430353464465377497/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_012
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0074).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^2*thetaFirstMode x) ≤ (597707015290318489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/64:ℝ) (13/256:ℝ)
    (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ) (430353464465377497/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_012 (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_013 :
    (135953740540995497/200000000000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (13/256:ℝ) (7/128:ℝ)
    (29565/560128:ℝ) (3127356820939/50000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_013
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0080).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x) ≤ (339885148395027721/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (13/256:ℝ) (7/128:ℝ)
    (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ) (1714670540522423867/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_013 (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_014 :
    (191121114127418707/250000000000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (7/128:ℝ) (15/256:ℝ)
    (36627/646144:ℝ) (3048896865167/50000000000000:ℝ) (106716101744309517/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_014
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0086).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^2*thetaFirstMode x) ≤ (764486279095942323/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/128:ℝ) (15/256:ℝ)
    (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ) (106716101744309517/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_014 (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_015 :
    (851423611744636787/1000000000000000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (15/256:ℝ) (1/16:ℝ)
    (44733/738304:ℝ) (594351944671/10000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_015
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0092).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x) ≤ (85142567549466749/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (15/256:ℝ) (1/16:ℝ)
    (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ) (1699780859421808009/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_015 (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_016 :
    (58760942175971291/62500000000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/16:ℝ) (17/256:ℝ)
    (53955/836608:ℝ) (2895941437237/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_016
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0098).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^2*thetaFirstMode x) ≤ (470088695931399953/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/16:ℝ) (17/256:ℝ)
    (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ) (1691646272594122039/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_016 (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_017 :
    (8049576102880319/7812500000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (17/256:ℝ) (9/128:ℝ)
    (64365/941056:ℝ) (2821437248783/50000000000000:ℝ) (841530099567674249/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_017
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0104).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x) ≤ (515174161555193577/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (17/256:ℝ) (9/128:ℝ)
    (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ) (841530099567674249/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_017 (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_018 :
    (560780140043008157/500000000000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (9/128:ℝ) (19/256:ℝ)
    (76035/1051648:ℝ) (2748241724611/50000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_018
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0110).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^2*thetaFirstMode x) ≤ (140195392248687519/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (9/128:ℝ) (19/256:ℝ)
    (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ) (1674029260262033759/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_018 (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_019 :
    (48538436327167479/40000000000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (19/256:ℝ) (5/64:ℝ)
    (89037/1168384:ℝ) (107053953759/2000000000000:ℝ) (832280181221222783/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_019
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0116).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x) ≤ (1213464052567466087/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (19/256:ℝ) (5/64:ℝ)
    (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ) (832280181221222783/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_019 (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_020 :
    (1305707151835474531/1000000000000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (5/64:ℝ) (21/256:ℝ)
    (103443/1291264:ℝ) (1302876031333/25000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_020
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0122).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^2*thetaFirstMode x) ≤ (652855296342558409/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/64:ℝ) (21/256:ℝ)
    (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ) (1654660691937798839/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_020 (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_021 :
    (698987799499412901/500000000000000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (21/256:ℝ) (11/128:ℝ)
    (119325/1420288:ℝ) (507288872169/10000000000000:ℝ) (12846388361106899/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_021
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0128).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x) ≤ (1397979345727460693/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (21/256:ℝ) (11/128:ℝ)
    (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ) (12846388361106899/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_021 (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_022 :
    (1489959640569555129/1000000000000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (11/128:ℝ) (23/256:ℝ)
    (136755/1555456:ℝ) (4936836559503/100000000000000:ℝ) (326719829522905161/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_022
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0134).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^2*thetaFirstMode x) ≤ (93122731378195769/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (11/128:ℝ) (23/256:ℝ)
    (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ) (326719829522905161/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_022 (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_023 :
    (9883557511655157/6250000000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (23/256:ℝ) (3/32:ℝ)
    (155805/1696768:ℝ) (2401665950807/50000000000000:ℝ) (64898119919301951/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_023
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0140).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x) ≤ (1581373586410745193/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (23/256:ℝ) (3/32:ℝ)
    (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ) (64898119919301951/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_023 (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_024 :
    (334386092879815867/200000000000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/32:ℝ) (25/256:ℝ)
    (176547/1844224:ℝ) (584044779791/12500000000000:ℝ) (805453755869069143/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_024
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0146).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^2*thetaFirstMode x) ≤ (1671935179759376737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/32:ℝ) (25/256:ℝ)
    (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ) (805453755869069143/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_024 (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_025 :
    (880692789228187269/500000000000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (25/256:ℝ) (13/128:ℝ)
    (199053/1997824:ℝ) (2271949163419/50000000000000:ℝ) (799485594891087013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_025
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0152).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x) ≤ (880695315908048709/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (25/256:ℝ) (13/128:ℝ)
    (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ) (799485594891087013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_025 (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_026 :
    (924746183387883881/500000000000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (13/128:ℝ) (27/256:ℝ)
    (223395/2157568:ℝ) (2208967112453/50000000000000:ℝ) (793326388093261413/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_026
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0158).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^2*thetaFirstMode x) ≤ (115593610297690079/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (13/128:ℝ) (27/256:ℝ)
    (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ) (793326388093261413/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_026 (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_027 :
    (1936024019815073419/1000000000000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (27/256:ℝ) (7/64:ℝ)
    (249645/2323456:ℝ) (4294447320513/100000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_027
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0164).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x) ≤ (387205953696731499/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (27/256:ℝ) (7/64:ℝ)
    (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ) (1573961251251712099/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_027 (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_028 :
    (505192195730449863/250000000000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (7/64:ℝ) (29/256:ℝ)
    (277875/2495488:ℝ) (4173418358361/100000000000000:ℝ) (97556613961683183/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_028
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0170).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^2*thetaFirstMode x) ≤ (1010387443880014249/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/64:ℝ) (29/256:ℝ)
    (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ) (97556613961683183/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_028 (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_029 :
    (3365647417428617/1600000000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (29/256:ℝ) (15/128:ℝ)
    (308157/2673664:ℝ) (4054827464193/100000000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_029
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0176).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x) ≤ (1051768050915837381/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (29/256:ℝ) (15/128:ℝ)
    (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ) (1547495922062128387/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_029 (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_030 :
    (68253873918081631/31250000000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (15/128:ℝ) (31/256:ℝ)
    (340563/2857984:ℝ) (3938654167541/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_030
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0182).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^2*thetaFirstMode x) ≤ (17063521849746227/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (15/128:ℝ) (31/256:ℝ)
    (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ) (1533741188904293299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_030 (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_031 :
    (70699475951359731/31250000000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (31/256:ℝ) (1/8:ℝ)
    (375165/3048448:ℝ) (3824877423089/100000000000000:ℝ) (759825734717146723/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_031
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0188).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x) ≤ (2262390431069108013/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (31/256:ℝ) (1/8:ℝ)
    (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ) (759825734717146723/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_031 (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator
