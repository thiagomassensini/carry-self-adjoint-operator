import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature07
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative10
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative11
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative12

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_8_224 :
    (873198443030871/250000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(225/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-943925578829165495396607/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (7/16:ℝ) (225/512:ℝ)-(225/512:ℝ)*thetaPowerMass 8 (7/16:ℝ) (225/512:ℝ)) ≤
      thetaFirstModeFirst (225/512:ℝ)*(thetaPowerMass 9 (7/16:ℝ) (225/512:ℝ)-(225/512:ℝ)*thetaPowerMass 8 (7/16:ℝ) (225/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0341.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (7/16:ℝ) (225/512:ℝ)
    (225/512:ℝ) (129025901651/100000000000000:ℝ) (-943925578829165495396607/50000000000000000000000000:ℝ) (237174929639550312532283/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_224
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0673).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_224 :
    (∫ x in (7/16:ℝ)..(225/512:ℝ), x^8*thetaFirstMode x) ≤ (54575096257989/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/16:ℝ) (225/512:ℝ)
    (132758967949/100000000000000:ℝ) (64513106191/50000000000000:ℝ) (237174929639550312532283/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_224 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0673).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_225 :
    (3517248357945653/1000000000000000000000000:ℝ) ≤ ∫ x in (225/512:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-94365371407892756058245556247/5000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (225/512:ℝ) (113/256:ℝ)-(51969452684042517525/118253148433449738752:ℝ)*thetaPowerMass 8 (225/512:ℝ) (113/256:ℝ)) ≤
      thetaFirstModeFirst (51969452684042517525/118253148433449738752:ℝ)*(thetaPowerMass 9 (225/512:ℝ) (113/256:ℝ)-(51969452684042517525/118253148433449738752:ℝ)*thetaPowerMass 8 (225/512:ℝ) (113/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0342.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (225/512:ℝ) (113/256:ℝ)
    (51969452684042517525/118253148433449738752:ℝ) (64491106081/50000000000000:ℝ) (-94365371407892756058245556247/5000000000000000000000000000000:ℝ) (232508578518001713709071/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_225
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0677).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_225 :
    (∫ x in (225/512:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x) ≤ (3517264916876127/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (225/512:ℝ) (113/256:ℝ)
    (64513106191/50000000000000:ℝ) (62691967071/50000000000000:ℝ) (232508578518001713709071/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_225 (thetaFirstMode_refined_node_0673).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_226 :
    (885228857150829/250000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(227/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-179702326974830601052599/10000000000000000000000000:ℝ)*(thetaPowerMass 9 (113/256:ℝ) (227/512:ℝ)-(227/512:ℝ)*thetaPowerMass 8 (113/256:ℝ) (227/512:ℝ)) ≤
      thetaFirstModeFirst (227/512:ℝ)*(thetaPowerMass 9 (113/256:ℝ) (227/512:ℝ)-(227/512:ℝ)*thetaPowerMass 8 (113/256:ℝ) (227/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0344.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (113/256:ℝ) (227/512:ℝ)
    (227/512:ℝ) (24366011489/20000000000000:ℝ) (-179702326974830601052599/10000000000000000000000000:ℝ) (45581315990209583114587/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_226
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0679).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_226 :
    (∫ x in (113/256:ℝ)..(227/512:ℝ), x^8*thetaFirstMode x) ≤ (354092817571347/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (113/256:ℝ) (227/512:ℝ)
    (62691967071/50000000000000:ℝ) (121830353147/100000000000000:ℝ) (45581315990209583114587/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_226 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0679).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_227 :
    (890940964694613/250000000000000000000000:ℝ) ≤ ∫ x in (227/512:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-17965054216304165945756025099/1000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (227/512:ℝ) (57/128:ℝ)-(281388531776708917143/634640852921264412160:ℝ)*thetaPowerMass 8 (227/512:ℝ) (57/128:ℝ)) ≤
      thetaFirstModeFirst (281388531776708917143/634640852921264412160:ℝ)*(thetaPowerMass 9 (227/512:ℝ) (57/128:ℝ)-(281388531776708917143/634640852921264412160:ℝ)*thetaPowerMass 8 (227/512:ℝ) (57/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0345.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (227/512:ℝ) (57/128:ℝ)
    (281388531776708917143/634640852921264412160:ℝ) (60894418137/50000000000000:ℝ) (-17965054216304165945756025099/1000000000000000000000000000000:ℝ) (223368662450383723085043/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_227
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0683).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_227 :
    (∫ x in (227/512:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x) ≤ (3563780950006411/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (227/512:ℝ) (57/128:ℝ)
    (121830353147/100000000000000:ℝ) (5918185693/5000000000000:ℝ) (223368662450383723085043/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_227 (thetaFirstMode_refined_node_0679).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_228 :
    (896448927021937/250000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(229/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-213720712388148706378597/12500000000000000000000000:ℝ)*(thetaPowerMass 9 (57/128:ℝ) (229/512:ℝ)-(229/512:ℝ)*thetaPowerMass 8 (57/128:ℝ) (229/512:ℝ)) ≤
      thetaFirstModeFirst (229/512:ℝ)*(thetaPowerMass 9 (57/128:ℝ) (229/512:ℝ)-(229/512:ℝ)*thetaPowerMass 8 (57/128:ℝ) (229/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0347.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (57/128:ℝ) (229/512:ℝ)
    (229/512:ℝ) (57491001961/50000000000000:ℝ) (-213720712388148706378597/12500000000000000000000000:ℝ) (21889454228660761080593/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_228
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0685).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_228 :
    (∫ x in (57/128:ℝ)..(229/512:ℝ), x^8*thetaFirstMode x) ≤ (358580881109163/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (57/128:ℝ) (229/512:ℝ)
    (5918185693/5000000000000:ℝ) (114982285191/100000000000000:ℝ) (21889454228660761080593/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_228 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0685).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_229 :
    (28855842239911/8000000000000000000000:ℝ) ≤ ∫ x in (229/512:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-85463635028459610616058971189/5000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (229/512:ℝ) (115/256:ℝ)-(304502779430409389841/680775093154008808960:ℝ)*thetaPowerMass 8 (229/512:ℝ) (115/256:ℝ)) ≤
      thetaFirstModeFirst (304502779430409389841/680775093154008808960:ℝ)*(thetaPowerMass 9 (229/512:ℝ) (115/256:ℝ)-(304502779430409389841/680775093154008808960:ℝ)*thetaPowerMass 8 (229/512:ℝ) (115/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0348.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (229/512:ℝ) (115/256:ℝ)
    (304502779430409389841/680775093154008808960:ℝ) (114943126783/100000000000000:ℝ) (-85463635028459610616058971189/5000000000000000000000000000000:ℝ) (107241961863557872347559/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_229
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0689).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_229 :
    (∫ x in (229/512:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x) ≤ (1803498951419681/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (229/512:ℝ) (115/256:ℝ)
    (114982285191/100000000000000:ℝ) (111684360387/100000000000000:ℝ) (107241961863557872347559/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_229 (thetaFirstMode_refined_node_0685).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_230 :
    (3627321499712473/1000000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(231/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-812989385087173261617/50000000000000000000000:ℝ)*(thetaPowerMass 9 (115/256:ℝ) (231/512:ℝ)-(231/512:ℝ)*thetaPowerMass 8 (115/256:ℝ) (231/512:ℝ)) ≤
      thetaFirstModeFirst (231/512:ℝ)*(thetaPowerMass 9 (115/256:ℝ) (231/512:ℝ)-(231/512:ℝ)*thetaPowerMass 8 (115/256:ℝ) (231/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0350.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (115/256:ℝ) (231/512:ℝ)
    (231/512:ℝ) (216935979/200000000000:ℝ) (-812989385087173261617/50000000000000000000000:ℝ) (210136499300608906084773/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_230
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0691).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_230 :
    (∫ x in (115/256:ℝ)..(231/512:ℝ), x^8*thetaFirstMode x) ≤ (3627334955057503/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (115/256:ℝ) (231/512:ℝ)
    (111684360387/100000000000000:ℝ) (27117064229/25000000000000:ℝ) (210136499300608906084773/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_230 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0691).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_231 :
    (911697285852897/250000000000000000000000:ℝ) ≤ ∫ x in (231/512:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4063774053669450540689679429/250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (231/512:ℝ) (29/64:ℝ)-(329289608647804933359/729817555912400028160:ℝ)*thetaPowerMass 8 (231/512:ℝ) (29/64:ℝ)) ≤
      thetaFirstModeFirst (329289608647804933359/729817555912400028160:ℝ)*(thetaPowerMass 9 (231/512:ℝ) (29/64:ℝ)-(329289608647804933359/729817555912400028160:ℝ)*thetaPowerMass 8 (231/512:ℝ) (29/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0351.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (231/512:ℝ) (29/64:ℝ)
    (329289608647804933359/729817555912400028160:ℝ) (54215668789/50000000000000:ℝ) (-4063774053669450540689679429/250000000000000000000000000000:ℝ) (102925975026324974068149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_231
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0695).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_231 :
    (∫ x in (231/512:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x) ≤ (3646807296321909/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (231/512:ℝ) (29/64:ℝ)
    (27117064229/25000000000000:ℝ) (52666158177/50000000000000:ℝ) (102925975026324974068149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_231 (thetaFirstMode_refined_node_0691).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_232 :
    (366538906279079/100000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(233/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-386390937390506654765493/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (29/64:ℝ) (233/512:ℝ)-(233/512:ℝ)*thetaPowerMass 8 (29/64:ℝ) (233/512:ℝ)) ≤
      thetaFirstModeFirst (233/512:ℝ)*(thetaPowerMass 9 (29/64:ℝ) (233/512:ℝ)-(233/512:ℝ)*thetaPowerMass 8 (29/64:ℝ) (233/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0353.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (29/64:ℝ) (233/512:ℝ)
    (233/512:ℝ) (51137325069/50000000000000:ℝ) (-386390937390506654765493/25000000000000000000000000:ℝ) (20162994579908353988699/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_232
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0697).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_232 :
    (∫ x in (29/64:ℝ)..(233/512:ℝ), x^8*thetaFirstMode x) ≤ (3665402866182281/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/64:ℝ) (233/512:ℝ)
    (52666158177/50000000000000:ℝ) (102274904263/100000000000000:ℝ) (20162994579908353988699/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_232 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0697).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_233 :
    (3683091546126349/1000000000000000000000000:ℝ) ≤ ∫ x in (233/512:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-193139685293226991086776294873/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (233/512:ℝ) (117/256:ℝ)-(355853979535385553057/781923988453504668160:ℝ)*thetaPowerMass 8 (233/512:ℝ) (117/256:ℝ)) ≤
      thetaFirstModeFirst (355853979535385553057/781923988453504668160:ℝ)*(thetaPowerMass 9 (233/512:ℝ) (117/256:ℝ)-(355853979535385553057/781923988453504668160:ℝ)*thetaPowerMass 8 (233/512:ℝ) (117/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0354.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (233/512:ℝ) (117/256:ℝ)
    (355853979535385553057/781923988453504668160:ℝ) (25560027471/25000000000000:ℝ) (-193139685293226991086776294873/12500000000000000000000000000000:ℝ) (49367536345676385970299/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_233
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0701).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_233 :
    (∫ x in (233/512:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x) ≤ (920777556629923/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (233/512:ℝ) (117/256:ℝ)
    (102274904263/100000000000000:ℝ) (4964720503/5000000000000:ℝ) (49367536345676385970299/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_233 (thetaFirstMode_refined_node_0697).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_234 :
    (3699904425878969/1000000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(235/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-146842291782352977581067/10000000000000000000000000:ℝ)*(thetaPowerMass 9 (117/256:ℝ) (235/512:ℝ)-(235/512:ℝ)*thetaPowerMass 8 (117/256:ℝ) (235/512:ℝ)) ≤
      thetaFirstModeFirst (235/512:ℝ)*(thetaPowerMass 9 (117/256:ℝ) (235/512:ℝ)-(235/512:ℝ)*thetaPowerMass 8 (117/256:ℝ) (235/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0356.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (117/256:ℝ) (235/512:ℝ)
    (235/512:ℝ) (19277801103/20000000000000:ℝ) (-146842291782352977581067/10000000000000000000000000:ℝ) (96686098471378599211639/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_234
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0703).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_234 :
    (∫ x in (117/256:ℝ)..(235/512:ℝ), x^8*thetaFirstMode x) ≤ (1849959286151251/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (117/256:ℝ) (235/512:ℝ)
    (4964720503/5000000000000:ℝ) (96389246893/100000000000000:ℝ) (96686098471378599211639/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_234 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0703).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_235 :
    (464474817184181/125000000000000000000000:ℝ) ≤ ∫ x in (235/512:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-366999648611183604840449837287/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (235/512:ℝ) (59/128:ℝ)-(76861289619680304915/167451405549299389952:ℝ)*thetaPowerMass 8 (235/512:ℝ) (59/128:ℝ)) ≤
      thetaFirstModeFirst (76861289619680304915/167451405549299389952:ℝ)*(thetaPowerMass 9 (235/512:ℝ) (59/128:ℝ)-(76861289619680304915/167451405549299389952:ℝ)*thetaPowerMass 8 (235/512:ℝ) (59/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0357.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (235/512:ℝ) (59/128:ℝ)
    (76861289619680304915/167451405549299389952:ℝ) (96356468443/100000000000000:ℝ) (-366999648611183604840449837287/25000000000000000000000000000000:ℝ) (189335738165537923296437/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_235
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0707).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_235 :
    (∫ x in (235/512:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x) ≤ (148632709668363/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (235/512:ℝ) (59/128:ℝ)
    (96389246893/100000000000000:ℝ) (46778925753/50000000000000:ℝ) (189335738165537923296437/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_235 (thetaFirstMode_refined_node_0703).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_236 :
    (186539187074519/50000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(237/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-34861490949517743873141/2500000000000000000000000:ℝ)*(thetaPowerMass 9 (59/128:ℝ) (237/512:ℝ)-(237/512:ℝ)*thetaPowerMass 8 (59/128:ℝ) (237/512:ℝ)) ≤
      thetaFirstModeFirst (237/512:ℝ)*(thetaPowerMass 9 (59/128:ℝ) (237/512:ℝ)-(237/512:ℝ)*thetaPowerMass 8 (59/128:ℝ) (237/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0359.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (59/128:ℝ) (237/512:ℝ)
    (237/512:ℝ) (22699613733/25000000000000:ℝ) (-34861490949517743873141/2500000000000000000000000:ℝ) (23170049570396535778647/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_236
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0709).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_236 :
    (∫ x in (59/128:ℝ)..(237/512:ℝ), x^8*thetaFirstMode x) ≤ (1865399112650061/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (59/128:ℝ) (237/512:ℝ)
    (46778925753/50000000000000:ℝ) (18159736819/20000000000000:ℝ) (23170049570396535778647/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_236 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0709).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_237 :
    (46810393139249/12500000000000000000000:ℝ) ≤ ∫ x in (237/512:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-10891065241194907652113405457/781250000000000000000000000000:ℝ)*(thetaPowerMass 9 (237/512:ℝ) (119/256:ℝ)-(414763412687601229593/895986442171253532160:ℝ)*thetaPowerMass 8 (237/512:ℝ) (119/256:ℝ)) ≤
      thetaFirstModeFirst (414763412687601229593/895986442171253532160:ℝ)*(thetaPowerMass 9 (237/512:ℝ) (119/256:ℝ)-(414763412687601229593/895986442171253532160:ℝ)*thetaPowerMass 8 (237/512:ℝ) (119/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0360.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (237/512:ℝ) (119/256:ℝ)
    (414763412687601229593/895986442171253532160:ℝ) (90767817427/100000000000000:ℝ) (-10891065241194907652113405457/781250000000000000000000000000:ℝ) (7257831589058902139443/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_237
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0713).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_237 :
    (∫ x in (237/512:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x) ≤ (14628324900663/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (237/512:ℝ) (119/256:ℝ)
    (18159736819/20000000000000:ℝ) (22027557043/25000000000000:ℝ) (7257831589058902139443/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_237 (thetaFirstMode_refined_node_0709).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_238 :
    (1878976797601731/500000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(239/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-330894605224092513857847/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (119/256:ℝ) (239/512:ℝ)-(239/512:ℝ)*thetaPowerMass 8 (119/256:ℝ) (239/512:ℝ)) ≤
      thetaFirstModeFirst (239/512:ℝ)*(thetaPowerMass 9 (119/256:ℝ) (239/512:ℝ)-(239/512:ℝ)*thetaPowerMass 8 (119/256:ℝ) (239/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0362.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (119/256:ℝ) (239/512:ℝ)
    (239/512:ℝ) (85490772961/100000000000000:ℝ) (-330894605224092513857847/25000000000000000000000000:ℝ) (277486758742776341103/1562500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_238
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0715).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_238 :
    (∫ x in (119/256:ℝ)..(239/512:ℝ), x^8*thetaFirstMode x) ≤ (3757968409889019/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (119/256:ℝ) (239/512:ℝ)
    (22027557043/25000000000000:ℝ) (4274549521/5000000000000:ℝ) (277486758742776341103/1562500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_238 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0715).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_239 :
    (3770122190489889/1000000000000000000000000:ℝ) ≤ ∫ x in (239/512:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x := by
  have hd : (-330798822964787710104386273439/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (239/512:ℝ) (15/32:ℝ)-(447347369053687618791/958289379521344821760:ℝ)*thetaPowerMass 8 (239/512:ℝ) (15/32:ℝ)) ≤
      thetaFirstModeFirst (447347369053687618791/958289379521344821760:ℝ)*(thetaPowerMass 9 (239/512:ℝ) (15/32:ℝ)-(447347369053687618791/958289379521344821760:ℝ)*thetaPowerMass 8 (239/512:ℝ) (15/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0363.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (239/512:ℝ) (15/32:ℝ)
    (447347369053687618791/958289379521344821760:ℝ) (85461936087/100000000000000:ℝ) (-330798822964787710104386273439/25000000000000000000000000000000:ℝ) (173797202727257609725889/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_239
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0719).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_239 :
    (∫ x in (239/512:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x) ≤ (3770142427417647/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (239/512:ℝ) (15/32:ℝ)
    (4274549521/5000000000000:ℝ) (10367437567/12500000000000:ℝ) (173797202727257609725889/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_239 (thetaFirstMode_refined_node_0715).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_240 :
    (3781351266883621/1000000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(241/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1226254870253133830691/97656250000000000000000:ℝ)*(thetaPowerMass 9 (15/32:ℝ) (241/512:ℝ)-(241/512:ℝ)*thetaPowerMass 8 (15/32:ℝ) (241/512:ℝ)) ≤
      thetaFirstModeFirst (241/512:ℝ)*(thetaPowerMass 9 (15/32:ℝ) (241/512:ℝ)-(241/512:ℝ)*thetaPowerMass 8 (15/32:ℝ) (241/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0365.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (15/32:ℝ) (241/512:ℝ)
    (241/512:ℝ) (314273847/390625000000:ℝ) (-1226254870253133830691/97656250000000000000000:ℝ) (21257801320656550687273/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_240
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0721).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_240 :
    (∫ x in (15/32:ℝ)..(241/512:ℝ), x^8*thetaFirstMode x) ≤ (945341601336303/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/32:ℝ) (241/512:ℝ)
    (10367437567/12500000000000:ℝ) (20113577771/25000000000000:ℝ) (21257801320656550687273/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_240 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0721).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_241 :
    (473951683250347/125000000000000000000000:ℝ) ≤ ∫ x in (241/512:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-78457572921199105839656228361/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (241/512:ℝ) (121/256:ℝ)-(482187174233040082809/1024350621420112591360:ℝ)*thetaPowerMass 8 (241/512:ℝ) (121/256:ℝ)) ≤
      thetaFirstModeFirst (482187174233040082809/1024350621420112591360:ℝ)*(thetaPowerMass 9 (241/512:ℝ) (121/256:ℝ)-(482187174233040082809/1024350621420112591360:ℝ)*thetaPowerMass 8 (241/512:ℝ) (121/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0366.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (241/512:ℝ) (121/256:ℝ)
    (482187174233040082809/1024350621420112591360:ℝ) (16085394831/20000000000000:ℝ) (-78457572921199105839656228361/6250000000000000000000000000000:ℝ) (166386729706384735163781/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_241
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0725).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_241 :
    (∫ x in (241/512:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x) ≤ (75832684191367/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (241/512:ℝ) (121/256:ℝ)
    (20113577771/25000000000000:ℝ) (3901699867/5000000000000:ℝ) (166386729706384735163781/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_241 (thetaFirstMode_refined_node_0721).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_242 :
    (3800924943900799/1000000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(243/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-595343162852680226866949/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (121/256:ℝ) (243/512:ℝ)-(243/512:ℝ)*thetaPowerMass 8 (121/256:ℝ) (243/512:ℝ)) ≤
      thetaFirstModeFirst (243/512:ℝ)*(thetaPowerMass 9 (121/256:ℝ) (243/512:ℝ)-(243/512:ℝ)*thetaPowerMass 8 (121/256:ℝ) (243/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0368.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (121/256:ℝ) (243/512:ℝ)
    (243/512:ℝ) (75676961597/100000000000000:ℝ) (-595343162852680226866949/50000000000000000000000000:ℝ) (162769732164439016177603/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_242
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0727).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_242 :
    (∫ x in (121/256:ℝ)..(243/512:ℝ), x^8*thetaFirstMode x) ≤ (1900470199150513/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (121/256:ℝ) (243/512:ℝ)
    (3901699867/5000000000000:ℝ) (605417257/800000000000:ℝ) (162769732164439016177603/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_242 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0727).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_243 :
    (1904629491749501/500000000000000000000000:ℝ) ≤ ∫ x in (243/512:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2975852481562964065820771911/250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (243/512:ℝ) (61/128:ℝ)-(519418319492085968007/1094362844259452700160:ℝ)*thetaPowerMass 8 (243/512:ℝ) (61/128:ℝ)) ≤
      thetaFirstModeFirst (519418319492085968007/1094362844259452700160:ℝ)*(thetaPowerMass 9 (243/512:ℝ) (61/128:ℝ)-(519418319492085968007/1094362844259452700160:ℝ)*thetaPowerMass 8 (243/512:ℝ) (61/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0369.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (243/512:ℝ) (61/128:ℝ)
    (519418319492085968007/1094362844259452700160:ℝ) (15130289401/20000000000000:ℝ) (-2975852481562964065820771911/250000000000000000000000000000:ℝ) (79605490829785045476271/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_243
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0731).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_243 :
    (∫ x in (243/512:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x) ≤ (3809280225974309/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (243/512:ℝ) (61/128:ℝ)
    (605417257/800000000000:ℝ) (73382410647/100000000000000:ℝ) (79605490829785045476271/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_243 (thetaFirstMode_refined_node_0727).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_244 :
    (3816633884786537/1000000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(245/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-141061343663011776349139/12500000000000000000000000:ℝ)*(thetaPowerMass 9 (61/128:ℝ) (245/512:ℝ)-(245/512:ℝ)*thetaPowerMass 8 (61/128:ℝ) (245/512:ℝ)) ≤
      thetaFirstModeFirst (245/512:ℝ)*(thetaPowerMass 9 (61/128:ℝ) (245/512:ℝ)-(245/512:ℝ)*thetaPowerMass 8 (61/128:ℝ) (245/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0371.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (61/128:ℝ) (245/512:ℝ)
    (245/512:ℝ) (35574107533/50000000000000:ℝ) (-141061343663011776349139/12500000000000000000000000:ℝ) (77855016929602072670317/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_244
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0733).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_244 :
    (∫ x in (61/128:ℝ)..(245/512:ℝ), x^8*thetaFirstMode x) ≤ (3816649646510827/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (61/128:ℝ) (245/512:ℝ)
    (73382410647/100000000000000:ℝ) (35574200167/50000000000000:ℝ) (77855016929602072670317/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_244 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0733).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_245 :
    (1911511791594557/500000000000000000000000:ℝ) ≤ ∫ x in (245/512:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-35255097177004543258948341059/3125000000000000000000000000000:ℝ)*(thetaPowerMass 9 (245/512:ℝ) (123/256:ℝ)-(111836642512315217805/233705377354370135552:ℝ)*thetaPowerMass 8 (245/512:ℝ) (123/256:ℝ)) ≤
      thetaFirstModeFirst (111836642512315217805/233705377354370135552:ℝ)*(thetaPowerMass 9 (245/512:ℝ) (123/256:ℝ)-(111836642512315217805/233705377354370135552:ℝ)*thetaPowerMass 8 (245/512:ℝ) (123/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0372.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (245/512:ℝ) (123/256:ℝ)
    (111836642512315217805/233705377354370135552:ℝ) (35562115301/50000000000000:ℝ) (-35255097177004543258948341059/3125000000000000000000000000000:ℝ) (152266436672900064453399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_245
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0737).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_245 :
    (∫ x in (245/512:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x) ≤ (3823045315625803/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (245/512:ℝ) (123/256:ℝ)
    (35574200167/50000000000000:ℝ) (34486895331/50000000000000:ℝ) (152266436672900064453399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_245 (thetaFirstMode_refined_node_0733).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_246 :
    (765689706526671/200000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(247/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-33406498318277440238159/3125000000000000000000000:ℝ)*(thetaPowerMass 9 (123/256:ℝ) (247/512:ℝ)-(247/512:ℝ)*thetaPowerMass 8 (123/256:ℝ) (247/512:ℝ)) ≤
      thetaFirstModeFirst (247/512:ℝ)*(thetaPowerMass 9 (123/256:ℝ) (247/512:ℝ)-(247/512:ℝ)*thetaPowerMass 8 (123/256:ℝ) (247/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0374.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (123/256:ℝ) (247/512:ℝ)
    (247/512:ℝ) (4178568283/6250000000000:ℝ) (-33406498318277440238159/3125000000000000000000000:ℝ) (9304983157038940266393/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_246
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0739).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_246 :
    (∫ x in (123/256:ℝ)..(247/512:ℝ), x^8*thetaFirstMode x) ≤ (15313858369877/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (123/256:ℝ) (247/512:ℝ)
    (34486895331/50000000000000:ℝ) (66857267987/100000000000000:ℝ) (9304983157038940266393/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_246 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0739).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_247 :
    (766576665604891/200000000000000000000000:ℝ) ≤ ∫ x in (247/512:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-534348616500886473995341410837/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (247/512:ℝ) (31/64:ℝ)-(601631469395921364543/1247052024347146908160:ℝ)*thetaPowerMass 8 (247/512:ℝ) (31/64:ℝ)) ≤
      thetaFirstModeFirst (601631469395921364543/1247052024347146908160:ℝ)*(thetaPowerMass 9 (247/512:ℝ) (31/64:ℝ)-(601631469395921364543/1247052024347146908160:ℝ)*thetaPowerMass 8 (247/512:ℝ) (31/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0375.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (247/512:ℝ) (31/64:ℝ)
    (601631469395921364543/1247052024347146908160:ℝ) (66834556229/100000000000000:ℝ) (-534348616500886473995341410837/50000000000000000000000000000000:ℝ) (2910988971182741418701/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_247
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0743).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_247 :
    (∫ x in (247/512:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x) ≤ (1916452770213713/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (247/512:ℝ) (31/64:ℝ)
    (66857267987/100000000000000:ℝ) (12959508073/20000000000000:ℝ) (2910988971182741418701/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_247 (thetaFirstMode_refined_node_0739).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_248 :
    (3836350578953873/1000000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(249/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-50607451439833887584677/5000000000000000000000000:ℝ)*(thetaPowerMass 9 (31/64:ℝ) (249/512:ℝ)-(249/512:ℝ)*thetaPowerMass 8 (31/64:ℝ) (249/512:ℝ)) ≤
      thetaFirstModeFirst (249/512:ℝ)*(thetaPowerMass 9 (31/64:ℝ) (249/512:ℝ)-(249/512:ℝ)*thetaPowerMass 8 (31/64:ℝ) (249/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0377.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (31/64:ℝ) (249/512:ℝ)
    (249/512:ℝ) (62793171289/100000000000000:ℝ) (-50607451439833887584677/5000000000000000000000000:ℝ) (17784389630349450598609/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_248
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0745).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_248 :
    (∫ x in (31/64:ℝ)..(249/512:ℝ), x^8*thetaFirstMode x) ≤ (3836366927070271/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/64:ℝ) (249/512:ℝ)
    (12959508073/20000000000000:ℝ) (1962291793/3125000000000:ℝ) (17784389630349450598609/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_248 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0745).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_249 :
    (119963298190011/31250000000000000000000:ℝ) ≤ ∫ x in (249/512:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-252963625329233178543728596101/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (249/512:ℝ) (125/256:ℝ)-(646920215696683136241/1330156250206437122560:ℝ)*thetaPowerMass 8 (249/512:ℝ) (125/256:ℝ)) ≤
      thetaFirstModeFirst (646920215696683136241/1330156250206437122560:ℝ)*(thetaPowerMass 9 (249/512:ℝ) (125/256:ℝ)-(646920215696683136241/1330156250206437122560:ℝ)*thetaPowerMass 8 (249/512:ℝ) (125/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0378.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (249/512:ℝ) (125/256:ℝ)
    (646920215696683136241/1330156250206437122560:ℝ) (1961625157/3125000000000:ℝ) (-252963625329233178543728596101/25000000000000000000000000000000:ℝ) (139056255501134619079639/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_249
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0749).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_249 :
    (∫ x in (249/512:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x) ≤ (383884822346983/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (249/512:ℝ) (125/256:ℝ)
    (1962291793/3125000000000:ℝ) (7605426243/12500000000000:ℝ) (139056255501134619079639/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_249 (thetaFirstMode_refined_node_0745).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_250 :
    (1920166488422697/500000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(251/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-239456644729528612562491/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (125/256:ℝ) (251/512:ℝ)-(251/512:ℝ)*thetaPowerMass 8 (125/256:ℝ) (251/512:ℝ)) ≤
      thetaFirstModeFirst (251/512:ℝ)*(thetaPowerMass 9 (125/256:ℝ) (251/512:ℝ)-(251/512:ℝ)*thetaPowerMass 8 (125/256:ℝ) (251/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0380.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (125/256:ℝ) (251/512:ℝ)
    (251/512:ℝ) (58946373017/100000000000000:ℝ) (-239456644729528612562491/25000000000000000000000000:ℝ) (67946188525127259059713/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_250
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0751).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_250 :
    (∫ x in (125/256:ℝ)..(251/512:ℝ), x^8*thetaFirstMode x) ≤ (76806992052721/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (125/256:ℝ) (251/512:ℝ)
    (7605426243/12500000000000:ℝ) (7368316269/12500000000000:ℝ) (67946188525127259059713/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_250 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0751).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_251 :
    (1920424399500899/500000000000000000000000:ℝ) ≤ ∫ x in (251/512:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2992336006242376887270835629/312500000000000000000000000000:ℝ)*(thetaPowerMass 9 (251/512:ℝ) (63/128:ℝ)-(695214398443277823759/1418066563546442882560:ℝ)*thetaPowerMass 8 (251/512:ℝ) (63/128:ℝ)) ≤
      thetaFirstModeFirst (695214398443277823759/1418066563546442882560:ℝ)*(thetaPowerMass 9 (251/512:ℝ) (63/128:ℝ)-(695214398443277823759/1418066563546442882560:ℝ)*thetaPowerMass 8 (251/512:ℝ) (63/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0381.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (251/512:ℝ) (63/128:ℝ)
    (695214398443277823759/1418066563546442882560:ℝ) (920726599/1562500000000:ℝ) (-2992336006242376887270835629/312500000000000000000000000000:ℝ) (33195747165900068609343/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_251
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0755).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_251 :
    (∫ x in (251/512:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x) ≤ (768174387448457/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (251/512:ℝ) (63/128:ℝ)
    (7368316269/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (33195747165900068609343/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_251 (thetaFirstMode_refined_node_0751).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_252 :
    (3840399904242079/1000000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(253/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-113244336178864022174619/12500000000000000000000000:ℝ)*(thetaPowerMass 9 (63/128:ℝ) (253/512:ℝ)-(253/512:ℝ)*thetaPowerMass 8 (63/128:ℝ) (253/512:ℝ)) ≤
      thetaFirstModeFirst (253/512:ℝ)*(thetaPowerMass 9 (63/128:ℝ) (253/512:ℝ)-(253/512:ℝ)*thetaPowerMass 8 (63/128:ℝ) (253/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0383.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (63/128:ℝ) (253/512:ℝ)
    (253/512:ℝ) (27653478959/50000000000000:ℝ) (-113244336178864022174619/12500000000000000000000000:ℝ) (64863795709352060631953/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_252
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0757).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_252 :
    (∫ x in (63/128:ℝ)..(253/512:ℝ), x^8*thetaFirstMode x) ≤ (240026049782149/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (63/128:ℝ) (253/512:ℝ)
    (57101491059/100000000000000:ℝ) (13826776627/25000000000000:ℝ) (64863795709352060631953/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_252 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0757).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_253 :
    (383896286030113/100000000000000000000000:ℝ) ≤ ∫ x in (253/512:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-226422603241849660277050912761/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (253/512:ℝ) (127/256:ℝ)-(746687107677957320457/1511019264768615708160:ℝ)*thetaPowerMass 8 (253/512:ℝ) (127/256:ℝ)) ≤
      thetaFirstModeFirst (746687107677957320457/1511019264768615708160:ℝ)*(thetaPowerMass 9 (253/512:ℝ) (127/256:ℝ)-(746687107677957320457/1511019264768615708160:ℝ)*thetaPowerMass 8 (253/512:ℝ) (127/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0384.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (253/512:ℝ) (127/256:ℝ)
    (746687107677957320457/1511019264768615708160:ℝ) (55288311903/100000000000000:ℝ) (-226422603241849660277050912761/25000000000000000000000000000000:ℝ) (316814201967971705613/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_253
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0761).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_253 :
    (∫ x in (253/512:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x) ≤ (3838986442376989/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (253/512:ℝ) (127/256:ℝ)
    (13826776627/25000000000000:ℝ) (53562210939/100000000000000:ℝ) (316814201967971705613/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_253 (thetaFirstMode_refined_node_0757).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_254 :
    (959141669515127/250000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(255/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-428224501401092725678359/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (127/256:ℝ) (255/512:ℝ)-(255/512:ℝ)*thetaPowerMass 8 (127/256:ℝ) (255/512:ℝ)) ≤
      thetaFirstModeFirst (255/512:ℝ)*(thetaPowerMass 9 (127/256:ℝ) (255/512:ℝ)-(255/512:ℝ)*thetaPowerMass 8 (127/256:ℝ) (255/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0386.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (127/256:ℝ) (255/512:ℝ)
    (255/512:ℝ) (51865518759/100000000000000:ℝ) (-428224501401092725678359/50000000000000000000000000:ℝ) (24755349375981761440733/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_254
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0763).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_254 :
    (∫ x in (127/256:ℝ)..(255/512:ℝ), x^8*thetaFirstMode x) ≤ (3836583824966909/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (127/256:ℝ) (255/512:ℝ)
    (53562210939/100000000000000:ℝ) (12966414799/25000000000000:ℝ) (24755349375981761440733/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_254 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0763).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_255 :
    (3833188565407919/1000000000000000000000000:ℝ) ≤ ∫ x in (255/512:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x := by
  have hd : (-428099420546085749331760911113/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (255/512:ℝ) (1/2:ℝ)-(160303981759231989195/321852051581633495552:ℝ)*thetaPowerMass 8 (255/512:ℝ) (1/2:ℝ)) ≤
      thetaFirstModeFirst (160303981759231989195/321852051581633495552:ℝ)*(thetaPowerMass 9 (255/512:ℝ) (1/2:ℝ)-(160303981759231989195/321852051581633495552:ℝ)*thetaPowerMass 8 (255/512:ℝ) (1/2:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0387.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (255/512:ℝ) (1/2:ℝ)
    (160303981759231989195/321852051581633495552:ℝ) (12962007471/25000000000000:ℝ) (-428099420546085749331760911113/50000000000000000000000000000000:ℝ) (60440137359506429916117/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_255
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0767).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_255 :
    (∫ x in (255/512:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x) ≤ (383321257716861/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (255/512:ℝ) (1/2:ℝ)
    (12966414799/25000000000000:ℝ) (50216326329/100000000000000:ℝ) (60440137359506429916117/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_255 (thetaFirstMode_refined_node_0763).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator
