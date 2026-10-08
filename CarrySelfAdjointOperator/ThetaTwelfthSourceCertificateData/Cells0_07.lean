import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature07
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative10
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative11
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative12

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_224 :
    (127816827299270389/50000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(225/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-60457519887145650152732491861/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/16:ℝ) (225/512:ℝ)-(7/16:ℝ)*thetaPowerMass 0 (7/16:ℝ) (225/512:ℝ)) ≤
      thetaFirstModeFirst (7/16:ℝ)*(thetaPowerMass 1 (7/16:ℝ) (225/512:ℝ)-(7/16:ℝ)*thetaPowerMass 0 (7/16:ℝ) (225/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0340.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/16:ℝ) (225/512:ℝ)
    (7/16:ℝ) (5310345979/4000000000000:ℝ) (-60457519887145650152732491861/3125000000000000000000000000000:ℝ) (237174929639550312532283/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_224
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0672).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_224 :
    (∫ x in (7/16:ℝ)..(225/512:ℝ), x^0*thetaFirstMode x) ≤ (102253945763700711/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/16:ℝ) (225/512:ℝ)
    (132758967949/100000000000000:ℝ) (64513106191/50000000000000:ℝ) (237174929639550312532283/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_224 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0673).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_225 :
    (2484318064905022581/1000000000000000000000000:ℝ) ≤ ∫ x in (225/512:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-94365371407892756058245556247/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (225/512:ℝ) (113/256:ℝ)-(51969452684042517525/118253148433449738752:ℝ)*thetaPowerMass 0 (225/512:ℝ) (113/256:ℝ)) ≤
      thetaFirstModeFirst (51969452684042517525/118253148433449738752:ℝ)*(thetaPowerMass 1 (225/512:ℝ) (113/256:ℝ)-(51969452684042517525/118253148433449738752:ℝ)*thetaPowerMass 0 (225/512:ℝ) (113/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0342.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (225/512:ℝ) (113/256:ℝ)
    (51969452684042517525/118253148433449738752:ℝ) (64491106081/50000000000000:ℝ) (-94365371407892756058245556247/5000000000000000000000000000000:ℝ) (232508578518001713709071/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_225
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0677).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_225 :
    (∫ x in (225/512:ℝ)..(113/256:ℝ), x^0*thetaFirstMode x) ≤ (31054121585289089/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (225/512:ℝ) (113/256:ℝ)
    (64513106191/50000000000000:ℝ) (62691967071/50000000000000:ℝ) (232508578518001713709071/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_225 (thetaFirstMode_refined_node_0673).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_226 :
    (1207024441669623863/500000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(227/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-115124357449800737986177245663/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (113/256:ℝ) (227/512:ℝ)-(113/256:ℝ)*thetaPowerMass 0 (113/256:ℝ) (227/512:ℝ)) ≤
      thetaFirstModeFirst (113/256:ℝ)*(thetaPowerMass 1 (113/256:ℝ) (227/512:ℝ)-(113/256:ℝ)*thetaPowerMass 0 (113/256:ℝ) (227/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0343.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (113/256:ℝ) (227/512:ℝ)
    (113/256:ℝ) (62691815501/50000000000000:ℝ) (-115124357449800737986177245663/6250000000000000000000000000000:ℝ) (45581315990209583114587/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_226
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0678).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_226 :
    (∫ x in (113/256:ℝ)..(227/512:ℝ), x^0*thetaFirstMode x) ≤ (2414060521278099413/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (113/256:ℝ) (227/512:ℝ)
    (62691967071/50000000000000:ℝ) (121830353147/100000000000000:ℝ) (45581315990209583114587/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_226 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0679).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_227 :
    (1172747642159424183/500000000000000000000000:ℝ) ≤ ∫ x in (227/512:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17965054216304165945756025099/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (227/512:ℝ) (57/128:ℝ)-(281388531776708917143/634640852921264412160:ℝ)*thetaPowerMass 0 (227/512:ℝ) (57/128:ℝ)) ≤
      thetaFirstModeFirst (281388531776708917143/634640852921264412160:ℝ)*(thetaPowerMass 1 (227/512:ℝ) (57/128:ℝ)-(281388531776708917143/634640852921264412160:ℝ)*thetaPowerMass 0 (227/512:ℝ) (57/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0345.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (227/512:ℝ) (57/128:ℝ)
    (281388531776708917143/634640852921264412160:ℝ) (60894418137/50000000000000:ℝ) (-17965054216304165945756025099/1000000000000000000000000000000:ℝ) (223368662450383723085043/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_227
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0683).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_227 :
    (∫ x in (227/512:ℝ)..(57/128:ℝ), x^0*thetaFirstMode x) ≤ (4581067383001367/1953125000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (227/512:ℝ) (57/128:ℝ)
    (121830353147/100000000000000:ℝ) (5918185693/5000000000000:ℝ) (223368662450383723085043/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_227 (thetaFirstMode_refined_node_0679).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_228 :
    (1139311211687033489/500000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(229/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-43823982347429205657163122317/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (57/128:ℝ) (229/512:ℝ)-(57/128:ℝ)*thetaPowerMass 0 (57/128:ℝ) (229/512:ℝ)) ≤
      thetaFirstModeFirst (57/128:ℝ)*(thetaPowerMass 1 (57/128:ℝ) (229/512:ℝ)-(57/128:ℝ)*thetaPowerMass 0 (57/128:ℝ) (229/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0346.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (57/128:ℝ) (229/512:ℝ)
    (57/128:ℝ) (118363425447/100000000000000:ℝ) (-43823982347429205657163122317/2500000000000000000000000000000:ℝ) (21889454228660761080593/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_228
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0684).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_228 :
    (∫ x in (57/128:ℝ)..(229/512:ℝ), x^0*thetaFirstMode x) ≤ (455726722872658823/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/128:ℝ) (229/512:ℝ)
    (5918185693/5000000000000:ℝ) (114982285191/100000000000000:ℝ) (21889454228660761080593/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_228 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0685).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_229 :
    (2213397509079459273/1000000000000000000000000:ℝ) ≤ ∫ x in (229/512:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-85463635028459610616058971189/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (229/512:ℝ) (115/256:ℝ)-(304502779430409389841/680775093154008808960:ℝ)*thetaPowerMass 0 (229/512:ℝ) (115/256:ℝ)) ≤
      thetaFirstModeFirst (304502779430409389841/680775093154008808960:ℝ)*(thetaPowerMass 1 (229/512:ℝ) (115/256:ℝ)-(304502779430409389841/680775093154008808960:ℝ)*thetaPowerMass 0 (229/512:ℝ) (115/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0348.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (229/512:ℝ) (115/256:ℝ)
    (304502779430409389841/680775093154008808960:ℝ) (114943126783/100000000000000:ℝ) (-85463635028459610616058971189/5000000000000000000000000000000:ℝ) (107241961863557872347559/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_229
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0689).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_229 :
    (∫ x in (229/512:ℝ)..(115/256:ℝ), x^0*thetaFirstMode x) ≤ (2213408291575950139/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (229/512:ℝ) (115/256:ℝ)
    (114982285191/100000000000000:ℝ) (111684360387/100000000000000:ℝ) (107241961863557872347559/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_229 (thetaFirstMode_refined_node_0685).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_230 :
    (537446669115250677/250000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(231/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-416862310404649482099641688699/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (115/256:ℝ) (231/512:ℝ)-(115/256:ℝ)*thetaPowerMass 0 (115/256:ℝ) (231/512:ℝ)) ≤
      thetaFirstModeFirst (115/256:ℝ)*(thetaPowerMass 1 (115/256:ℝ) (231/512:ℝ)-(115/256:ℝ)*thetaPowerMass 0 (115/256:ℝ) (231/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0349.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (115/256:ℝ) (231/512:ℝ)
    (115/256:ℝ) (27921021529/25000000000000:ℝ) (-416862310404649482099641688699/25000000000000000000000000000000:ℝ) (210136499300608906084773/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_230
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0690).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_230 :
    (∫ x in (115/256:ℝ)..(231/512:ℝ), x^0*thetaFirstMode x) ≤ (1074898716719621579/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (115/256:ℝ) (231/512:ℝ)
    (111684360387/100000000000000:ℝ) (27117064229/25000000000000:ℝ) (210136499300608906084773/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_230 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0691).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_231 :
    (521939512925785089/250000000000000000000000:ℝ) ≤ ∫ x in (231/512:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4063774053669450540689679429/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (231/512:ℝ) (29/64:ℝ)-(329289608647804933359/729817555912400028160:ℝ)*thetaPowerMass 0 (231/512:ℝ) (29/64:ℝ)) ≤
      thetaFirstModeFirst (329289608647804933359/729817555912400028160:ℝ)*(thetaPowerMass 1 (231/512:ℝ) (29/64:ℝ)-(329289608647804933359/729817555912400028160:ℝ)*thetaPowerMass 0 (231/512:ℝ) (29/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0351.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (231/512:ℝ) (29/64:ℝ)
    (329289608647804933359/729817555912400028160:ℝ) (54215668789/50000000000000:ℝ) (-4063774053669450540689679429/250000000000000000000000000000:ℝ) (102925975026324974068149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_231
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0695).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_231 :
    (∫ x in (231/512:ℝ)..(29/64:ℝ), x^0*thetaFirstMode x) ≤ (41755368272555373/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (231/512:ℝ) (29/64:ℝ)
    (27117064229/25000000000000:ℝ) (52666158177/50000000000000:ℝ) (102925975026324974068149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_231 (thetaFirstMode_refined_node_0691).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_232 :
    (81091149589291739/40000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(233/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-99085021786989147418756438851/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (29/64:ℝ) (233/512:ℝ)-(29/64:ℝ)*thetaPowerMass 0 (29/64:ℝ) (233/512:ℝ)) ≤
      thetaFirstModeFirst (29/64:ℝ)*(thetaPowerMass 1 (29/64:ℝ) (233/512:ℝ)-(29/64:ℝ)*thetaPowerMass 0 (29/64:ℝ) (233/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0352.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (29/64:ℝ) (233/512:ℝ)
    (29/64:ℝ) (105332055653/100000000000000:ℝ) (-99085021786989147418756438851/6250000000000000000000000000000:ℝ) (20162994579908353988699/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_232
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0696).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_232 :
    (∫ x in (29/64:ℝ)..(233/512:ℝ), x^0*thetaFirstMode x) ≤ (2027289075491063171/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/64:ℝ) (233/512:ℝ)
    (52666158177/50000000000000:ℝ) (102274904263/100000000000000:ℝ) (20162994579908353988699/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_232 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0697).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_233 :
    (196831777574411211/100000000000000000000000:ℝ) ≤ ∫ x in (233/512:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-193139685293226991086776294873/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (233/512:ℝ) (117/256:ℝ)-(355853979535385553057/781923988453504668160:ℝ)*thetaPowerMass 0 (233/512:ℝ) (117/256:ℝ)) ≤
      thetaFirstModeFirst (355853979535385553057/781923988453504668160:ℝ)*(thetaPowerMass 1 (233/512:ℝ) (117/256:ℝ)-(355853979535385553057/781923988453504668160:ℝ)*thetaPowerMass 0 (233/512:ℝ) (117/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0354.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (233/512:ℝ) (117/256:ℝ)
    (355853979535385553057/781923988453504668160:ℝ) (25560027471/25000000000000:ℝ) (-193139685293226991086776294873/12500000000000000000000000000000:ℝ) (49367536345676385970299/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_233
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0701).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_233 :
    (∫ x in (233/512:ℝ)..(117/256:ℝ), x^0*thetaFirstMode x) ≤ (984163864791370933/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (233/512:ℝ) (117/256:ℝ)
    (102274904263/100000000000000:ℝ) (4964720503/5000000000000:ℝ) (49367536345676385970299/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_233 (thetaFirstMode_refined_node_0697).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_234 :
    (1910843224109776927/1000000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(235/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1883242974414735225476845621/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (117/256:ℝ) (235/512:ℝ)-(117/256:ℝ)*thetaPowerMass 0 (117/256:ℝ) (235/512:ℝ)) ≤
      thetaFirstModeFirst (117/256:ℝ)*(thetaPowerMass 1 (117/256:ℝ) (235/512:ℝ)-(117/256:ℝ)*thetaPowerMass 0 (117/256:ℝ) (235/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0355.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (117/256:ℝ) (235/512:ℝ)
    (117/256:ℝ) (794353299/800000000000:ℝ) (-1883242974414735225476845621/125000000000000000000000000000:ℝ) (96686098471378599211639/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_234
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0702).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_234 :
    (∫ x in (117/256:ℝ)..(235/512:ℝ), x^0*thetaFirstMode x) ≤ (477713287792524193/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (117/256:ℝ) (235/512:ℝ)
    (4964720503/5000000000000:ℝ) (96389246893/100000000000000:ℝ) (96686098471378599211639/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_234 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0703).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_235 :
    (57963281865783277/31250000000000000000000:ℝ) ≤ ∫ x in (235/512:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-366999648611183604840449837287/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (235/512:ℝ) (59/128:ℝ)-(76861289619680304915/167451405549299389952:ℝ)*thetaPowerMass 0 (235/512:ℝ) (59/128:ℝ)) ≤
      thetaFirstModeFirst (76861289619680304915/167451405549299389952:ℝ)*(thetaPowerMass 1 (235/512:ℝ) (59/128:ℝ)-(76861289619680304915/167451405549299389952:ℝ)*thetaPowerMass 0 (235/512:ℝ) (59/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0357.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (235/512:ℝ) (59/128:ℝ)
    (76861289619680304915/167451405549299389952:ℝ) (96356468443/100000000000000:ℝ) (-366999648611183604840449837287/25000000000000000000000000000000:ℝ) (189335738165537923296437/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_235
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0707).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_235 :
    (∫ x in (235/512:ℝ)..(59/128:ℝ), x^0*thetaFirstMode x) ≤ (927417288852322171/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (235/512:ℝ) (59/128:ℝ)
    (96389246893/100000000000000:ℝ) (46778925753/50000000000000:ℝ) (189335738165537923296437/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_235 (thetaFirstMode_refined_node_0703).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_236 :
    (1800232175400232541/1000000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(237/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-178881768465942041020652479551/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (59/128:ℝ) (237/512:ℝ)-(59/128:ℝ)*thetaPowerMass 0 (59/128:ℝ) (237/512:ℝ)) ≤
      thetaFirstModeFirst (59/128:ℝ)*(thetaPowerMass 1 (59/128:ℝ) (237/512:ℝ)-(59/128:ℝ)*thetaPowerMass 0 (59/128:ℝ) (237/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0358.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (59/128:ℝ) (237/512:ℝ)
    (59/128:ℝ) (935576163/1000000000000:ℝ) (-178881768465942041020652479551/12500000000000000000000000000000:ℝ) (23170049570396535778647/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_236
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0708).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_236 :
    (∫ x in (59/128:ℝ)..(237/512:ℝ), x^0*thetaFirstMode x) ≤ (900120853048671493/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/128:ℝ) (237/512:ℝ)
    (46778925753/50000000000000:ℝ) (18159736819/20000000000000:ℝ) (23170049570396535778647/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_236 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0709).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_237 :
    (873517757888785651/500000000000000000000000:ℝ) ≤ ∫ x in (237/512:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10891065241194907652113405457/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (237/512:ℝ) (119/256:ℝ)-(414763412687601229593/895986442171253532160:ℝ)*thetaPowerMass 0 (237/512:ℝ) (119/256:ℝ)) ≤
      thetaFirstModeFirst (414763412687601229593/895986442171253532160:ℝ)*(thetaPowerMass 1 (237/512:ℝ) (119/256:ℝ)-(414763412687601229593/895986442171253532160:ℝ)*thetaPowerMass 0 (237/512:ℝ) (119/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0360.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (237/512:ℝ) (119/256:ℝ)
    (414763412687601229593/895986442171253532160:ℝ) (90767817427/100000000000000:ℝ) (-10891065241194907652113405457/781250000000000000000000000000:ℝ) (7257831589058902139443/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_237
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0713).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_237 :
    (∫ x in (237/512:ℝ)..(119/256:ℝ), x^0*thetaFirstMode x) ≤ (1747044689984061077/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (237/512:ℝ) (119/256:ℝ)
    (18159736819/20000000000000:ℝ) (22027557043/25000000000000:ℝ) (7257831589058902139443/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_237 (thetaFirstMode_refined_node_0709).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_238 :
    (847602495283544323/500000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(239/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-169830447754646471233032881257/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (119/256:ℝ) (239/512:ℝ)-(119/256:ℝ)*thetaPowerMass 0 (119/256:ℝ) (239/512:ℝ)) ≤
      thetaFirstModeFirst (119/256:ℝ)*(thetaPowerMass 1 (119/256:ℝ) (239/512:ℝ)-(119/256:ℝ)*thetaPowerMass 0 (119/256:ℝ) (239/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0361.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (119/256:ℝ) (239/512:ℝ)
    (119/256:ℝ) (3524400197/4000000000000:ℝ) (-169830447754646471233032881257/12500000000000000000000000000000:ℝ) (277486758742776341103/1562500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_238
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0714).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_238 :
    (∫ x in (119/256:ℝ)..(239/512:ℝ), x^0*thetaFirstMode x) ≤ (26487720890332319/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (119/256:ℝ) (239/512:ℝ)
    (22027557043/25000000000000:ℝ) (4274549521/5000000000000:ℝ) (277486758742776341103/1562500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_238 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0715).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_239 :
    (822356151748219707/500000000000000000000000:ℝ) ≤ ∫ x in (239/512:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-330798822964787710104386273439/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (239/512:ℝ) (15/32:ℝ)-(447347369053687618791/958289379521344821760:ℝ)*thetaPowerMass 0 (239/512:ℝ) (15/32:ℝ)) ≤
      thetaFirstModeFirst (447347369053687618791/958289379521344821760:ℝ)*(thetaPowerMass 1 (239/512:ℝ) (15/32:ℝ)-(447347369053687618791/958289379521344821760:ℝ)*thetaPowerMass 0 (239/512:ℝ) (15/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0363.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (239/512:ℝ) (15/32:ℝ)
    (447347369053687618791/958289379521344821760:ℝ) (85461936087/100000000000000:ℝ) (-330798822964787710104386273439/25000000000000000000000000000000:ℝ) (173797202727257609725889/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_239
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0719).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_239 :
    (∫ x in (239/512:ℝ)..(15/32:ℝ), x^0*thetaFirstMode x) ≤ (1644721105736650889/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (239/512:ℝ) (15/32:ℝ)
    (4274549521/5000000000000:ℝ) (10367437567/12500000000000:ℝ) (173797202727257609725889/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_239 (thetaFirstMode_refined_node_0715).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_240 :
    (319105665785805069/200000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(241/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-80579236909443204678527524553/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/32:ℝ) (241/512:ℝ)-(15/32:ℝ)*thetaPowerMass 0 (15/32:ℝ) (241/512:ℝ)) ≤
      thetaFirstModeFirst (15/32:ℝ)*(thetaPowerMass 1 (15/32:ℝ) (241/512:ℝ)-(15/32:ℝ)*thetaPowerMass 0 (15/32:ℝ) (241/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0364.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/32:ℝ) (241/512:ℝ)
    (15/32:ℝ) (82939288741/100000000000000:ℝ) (-80579236909443204678527524553/6250000000000000000000000000000:ℝ) (21257801320656550687273/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_240
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0720).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_240 :
    (∫ x in (15/32:ℝ)..(241/512:ℝ), x^0*thetaFirstMode x) ≤ (159553710296019387/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/32:ℝ) (241/512:ℝ)
    (10367437567/12500000000000:ℝ) (20113577771/25000000000000:ℝ) (21257801320656550687273/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_240 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0721).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_241 :
    (1547625638637391287/1000000000000000000000000:ℝ) ≤ ∫ x in (241/512:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-78457572921199105839656228361/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (241/512:ℝ) (121/256:ℝ)-(482187174233040082809/1024350621420112591360:ℝ)*thetaPowerMass 0 (241/512:ℝ) (121/256:ℝ)) ≤
      thetaFirstModeFirst (482187174233040082809/1024350621420112591360:ℝ)*(thetaPowerMass 1 (241/512:ℝ) (121/256:ℝ)-(482187174233040082809/1024350621420112591360:ℝ)*thetaPowerMass 0 (241/512:ℝ) (121/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0366.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (241/512:ℝ) (121/256:ℝ)
    (482187174233040082809/1024350621420112591360:ℝ) (16085394831/20000000000000:ℝ) (-78457572921199105839656228361/6250000000000000000000000000000:ℝ) (166386729706384735163781/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_241
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0725).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_241 :
    (∫ x in (241/512:ℝ)..(121/256:ℝ), x^0*thetaFirstMode x) ≤ (1547634080474797001/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (241/512:ℝ) (121/256:ℝ)
    (20113577771/25000000000000:ℝ) (3901699867/5000000000000:ℝ) (166386729706384735163781/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_241 (thetaFirstMode_refined_node_0721).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_242 :
    (750488009388364853/500000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(243/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3821353502405362147008368181/312500000000000000000000000000:ℝ)*(thetaPowerMass 1 (121/256:ℝ) (243/512:ℝ)-(121/256:ℝ)*thetaPowerMass 0 (121/256:ℝ) (243/512:ℝ)) ≤
      thetaFirstModeFirst (121/256:ℝ)*(thetaPowerMass 1 (121/256:ℝ) (243/512:ℝ)-(121/256:ℝ)*thetaPowerMass 0 (121/256:ℝ) (243/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0367.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (121/256:ℝ) (243/512:ℝ)
    (121/256:ℝ) (7803379651/10000000000000:ℝ) (-3821353502405362147008368181/312500000000000000000000000000:ℝ) (162769732164439016177603/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_242
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0726).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_242 :
    (∫ x in (121/256:ℝ)..(243/512:ℝ), x^0*thetaFirstMode x) ≤ (1500984432071579721/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (121/256:ℝ) (243/512:ℝ)
    (3901699867/5000000000000:ℝ) (605417257/800000000000:ℝ) (162769732164439016177603/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_242 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0727).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_243 :
    (145555289747586701/100000000000000000000000:ℝ) ≤ ∫ x in (243/512:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2975852481562964065820771911/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (243/512:ℝ) (61/128:ℝ)-(519418319492085968007/1094362844259452700160:ℝ)*thetaPowerMass 0 (243/512:ℝ) (61/128:ℝ)) ≤
      thetaFirstModeFirst (519418319492085968007/1094362844259452700160:ℝ)*(thetaPowerMass 1 (243/512:ℝ) (61/128:ℝ)-(519418319492085968007/1094362844259452700160:ℝ)*thetaPowerMass 0 (243/512:ℝ) (61/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0369.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (243/512:ℝ) (61/128:ℝ)
    (519418319492085968007/1094362844259452700160:ℝ) (15130289401/20000000000000:ℝ) (-2975852481562964065820771911/250000000000000000000000000000:ℝ) (79605490829785045476271/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_243
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0731).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_243 :
    (∫ x in (243/512:ℝ)..(61/128:ℝ), x^0*thetaFirstMode x) ≤ (291112198067174667/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (243/512:ℝ) (61/128:ℝ)
    (605417257/800000000000:ℝ) (73382410647/100000000000000:ℝ) (79605490829785045476271/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_243 (thetaFirstMode_refined_node_0727).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_244 :
    (141132895945784949/100000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(245/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-579623608370171277095778169029/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (61/128:ℝ) (245/512:ℝ)-(61/128:ℝ)*thetaPowerMass 0 (61/128:ℝ) (245/512:ℝ)) ≤
      thetaFirstModeFirst (61/128:ℝ)*(thetaPowerMass 1 (61/128:ℝ) (245/512:ℝ)-(61/128:ℝ)*thetaPowerMass 0 (61/128:ℝ) (245/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0370.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (61/128:ℝ) (245/512:ℝ)
    (61/128:ℝ) (73382220307/100000000000000:ℝ) (-579623608370171277095778169029/50000000000000000000000000000000:ℝ) (77855016929602072670317/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_244
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0732).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_244 :
    (∫ x in (61/128:ℝ)..(245/512:ℝ), x^0*thetaFirstMode x) ≤ (705668511736621657/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/128:ℝ) (245/512:ℝ)
    (73382410647/100000000000000:ℝ) (35574200167/50000000000000:ℝ) (77855016929602072670317/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_244 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0733).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_245 :
    (171034809621853951/125000000000000000000000:ℝ) ≤ ∫ x in (245/512:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-35255097177004543258948341059/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (245/512:ℝ) (123/256:ℝ)-(111836642512315217805/233705377354370135552:ℝ)*thetaPowerMass 0 (245/512:ℝ) (123/256:ℝ)) ≤
      thetaFirstModeFirst (111836642512315217805/233705377354370135552:ℝ)*(thetaPowerMass 1 (245/512:ℝ) (123/256:ℝ)-(111836642512315217805/233705377354370135552:ℝ)*thetaPowerMass 0 (245/512:ℝ) (123/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0372.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (245/512:ℝ) (123/256:ℝ)
    (111836642512315217805/233705377354370135552:ℝ) (35562115301/50000000000000:ℝ) (-35255097177004543258948341059/3125000000000000000000000000000:ℝ) (152266436672900064453399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_245
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0737).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_245 :
    (∫ x in (245/512:ℝ)..(123/256:ℝ), x^0*thetaFirstMode x) ≤ (1368286231998759347/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (245/512:ℝ) (123/256:ℝ)
    (35574200167/50000000000000:ℝ) (34486895331/50000000000000:ℝ) (152266436672900064453399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_245 (thetaFirstMode_refined_node_0733).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_246 :
    (1326375019469452523/1000000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(247/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-8581399004098045042086090411/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (123/256:ℝ) (247/512:ℝ)-(123/256:ℝ)*thetaPowerMass 0 (123/256:ℝ) (247/512:ℝ)) ≤
      thetaFirstModeFirst (123/256:ℝ)*(thetaPowerMass 1 (123/256:ℝ) (247/512:ℝ)-(123/256:ℝ)*thetaPowerMass 0 (123/256:ℝ) (247/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0373.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (123/256:ℝ) (247/512:ℝ)
    (123/256:ℝ) (34486805177/50000000000000:ℝ) (-8581399004098045042086090411/781250000000000000000000000000:ℝ) (9304983157038940266393/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_246
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0738).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_246 :
    (∫ x in (123/256:ℝ)..(247/512:ℝ), x^0*thetaFirstMode x) ≤ (663191372708260621/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (123/256:ℝ) (247/512:ℝ)
    (34486895331/50000000000000:ℝ) (66857267987/100000000000000:ℝ) (9304983157038940266393/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_246 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0739).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_247 :
    (642796845351897779/500000000000000000000000:ℝ) ≤ ∫ x in (247/512:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-534348616500886473995341410837/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (247/512:ℝ) (31/64:ℝ)-(601631469395921364543/1247052024347146908160:ℝ)*thetaPowerMass 0 (247/512:ℝ) (31/64:ℝ)) ≤
      thetaFirstModeFirst (601631469395921364543/1247052024347146908160:ℝ)*(thetaPowerMass 1 (247/512:ℝ) (31/64:ℝ)-(601631469395921364543/1247052024347146908160:ℝ)*thetaPowerMass 0 (247/512:ℝ) (31/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0375.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (247/512:ℝ) (31/64:ℝ)
    (601631469395921364543/1247052024347146908160:ℝ) (66834556229/100000000000000:ℝ) (-534348616500886473995341410837/50000000000000000000000000000000:ℝ) (2910988971182741418701/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_247
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0743).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_247 :
    (∫ x in (247/512:ℝ)..(31/64:ℝ), x^0*thetaFirstMode x) ≤ (321400279705264007/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (247/512:ℝ) (31/64:ℝ)
    (66857267987/100000000000000:ℝ) (12959508073/20000000000000:ℝ) (2910988971182741418701/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_247 (thetaFirstMode_refined_node_0739).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_248 :
    (1245908930528417377/1000000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(249/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6501619265776154069913746739/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (31/64:ℝ) (249/512:ℝ)-(31/64:ℝ)*thetaPowerMass 0 (31/64:ℝ) (249/512:ℝ)) ≤
      thetaFirstModeFirst (31/64:ℝ)*(thetaPowerMass 1 (31/64:ℝ) (249/512:ℝ)-(31/64:ℝ)*thetaPowerMass 0 (31/64:ℝ) (249/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0376.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (31/64:ℝ) (249/512:ℝ)
    (31/64:ℝ) (12959473929/20000000000000:ℝ) (-6501619265776154069913746739/625000000000000000000000000000:ℝ) (17784389630349450598609/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_248
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0744).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_248 :
    (∫ x in (31/64:ℝ)..(249/512:ℝ), x^0*thetaFirstMode x) ≤ (311479082355145279/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/64:ℝ) (249/512:ℝ)
    (12959508073/20000000000000:ℝ) (1962291793/3125000000000:ℝ) (17784389630349450598609/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_248 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0745).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_249 :
    (603648330558162827/500000000000000000000000:ℝ) ≤ ∫ x in (249/512:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-252963625329233178543728596101/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (249/512:ℝ) (125/256:ℝ)-(646920215696683136241/1330156250206437122560:ℝ)*thetaPowerMass 0 (249/512:ℝ) (125/256:ℝ)) ≤
      thetaFirstModeFirst (646920215696683136241/1330156250206437122560:ℝ)*(thetaPowerMass 1 (249/512:ℝ) (125/256:ℝ)-(646920215696683136241/1330156250206437122560:ℝ)*thetaPowerMass 0 (249/512:ℝ) (125/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0378.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (249/512:ℝ) (125/256:ℝ)
    (646920215696683136241/1330156250206437122560:ℝ) (1961625157/3125000000000:ℝ) (-252963625329233178543728596101/25000000000000000000000000000000:ℝ) (139056255501134619079639/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_249
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0749).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_249 :
    (∫ x in (249/512:ℝ)..(125/256:ℝ), x^0*thetaFirstMode x) ≤ (150912971632535233/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (249/512:ℝ) (125/256:ℝ)
    (1962291793/3125000000000:ℝ) (7605426243/12500000000000:ℝ) (139056255501134619079639/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_249 (thetaFirstMode_refined_node_0745).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_250 :
    (116973217807653187/100000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(251/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2461697720663337879859799991/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (125/256:ℝ) (251/512:ℝ)-(125/256:ℝ)*thetaPowerMass 0 (125/256:ℝ) (251/512:ℝ)) ≤
      thetaFirstModeFirst (125/256:ℝ)*(thetaPowerMass 1 (125/256:ℝ) (251/512:ℝ)-(125/256:ℝ)*thetaPowerMass 0 (125/256:ℝ) (251/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0379.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (125/256:ℝ) (251/512:ℝ)
    (125/256:ℝ) (12168649677/20000000000000:ℝ) (-2461697720663337879859799991/250000000000000000000000000000:ℝ) (67946188525127259059713/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_250
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0750).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_250 :
    (∫ x in (125/256:ℝ)..(251/512:ℝ), x^0*thetaFirstMode x) ≤ (29243481516442249/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (125/256:ℝ) (251/512:ℝ)
    (7605426243/12500000000000:ℝ) (7368316269/12500000000000:ℝ) (67946188525127259059713/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_250 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0751).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_251 :
    (1133192208360234197/1000000000000000000000000:ℝ) ≤ ∫ x in (251/512:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2992336006242376887270835629/312500000000000000000000000000:ℝ)*(thetaPowerMass 1 (251/512:ℝ) (63/128:ℝ)-(695214398443277823759/1418066563546442882560:ℝ)*thetaPowerMass 0 (251/512:ℝ) (63/128:ℝ)) ≤
      thetaFirstModeFirst (695214398443277823759/1418066563546442882560:ℝ)*(thetaPowerMass 1 (251/512:ℝ) (63/128:ℝ)-(695214398443277823759/1418066563546442882560:ℝ)*thetaPowerMass 0 (251/512:ℝ) (63/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0381.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (251/512:ℝ) (63/128:ℝ)
    (695214398443277823759/1418066563546442882560:ℝ) (920726599/1562500000000:ℝ) (-2992336006242376887270835629/312500000000000000000000000000:ℝ) (33195747165900068609343/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_251
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0755).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_251 :
    (∫ x in (251/512:ℝ)..(63/128:ℝ), x^0*thetaFirstMode x) ≤ (1133199014608760327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (251/512:ℝ) (63/128:ℝ)
    (7368316269/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (33195747165900068609343/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_251 (thetaFirstMode_refined_node_0751).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_252 :
    (137206611036611401/125000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(253/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-93159242193065396254763328273/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (63/128:ℝ) (253/512:ℝ)-(63/128:ℝ)*thetaPowerMass 0 (63/128:ℝ) (253/512:ℝ)) ≤
      thetaFirstModeFirst (63/128:ℝ)*(thetaPowerMass 1 (63/128:ℝ) (253/512:ℝ)-(63/128:ℝ)*thetaPowerMass 0 (63/128:ℝ) (253/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0382.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (63/128:ℝ) (253/512:ℝ)
    (63/128:ℝ) (57101338247/100000000000000:ℝ) (-93159242193065396254763328273/10000000000000000000000000000000:ℝ) (64863795709352060631953/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_252
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0756).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_252 :
    (∫ x in (63/128:ℝ)..(253/512:ℝ), x^0*thetaFirstMode x) ≤ (548829832562804277/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/128:ℝ) (253/512:ℝ)
    (57101491059/100000000000000:ℝ) (13826776627/25000000000000:ℝ) (64863795709352060631953/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_252 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0757).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_253 :
    (53154586783933579/50000000000000000000000:ℝ) ≤ ∫ x in (253/512:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-226422603241849660277050912761/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (253/512:ℝ) (127/256:ℝ)-(746687107677957320457/1511019264768615708160:ℝ)*thetaPowerMass 0 (253/512:ℝ) (127/256:ℝ)) ≤
      thetaFirstModeFirst (746687107677957320457/1511019264768615708160:ℝ)*(thetaPowerMass 1 (253/512:ℝ) (127/256:ℝ)-(746687107677957320457/1511019264768615708160:ℝ)*thetaPowerMass 0 (253/512:ℝ) (127/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0384.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (253/512:ℝ) (127/256:ℝ)
    (746687107677957320457/1511019264768615708160:ℝ) (55288311903/100000000000000:ℝ) (-226422603241849660277050912761/25000000000000000000000000000000:ℝ) (316814201967971705613/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_253
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0761).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_253 :
    (∫ x in (253/512:ℝ)..(127/256:ℝ), x^0*thetaFirstMode x) ≤ (13288728081689487/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (253/512:ℝ) (127/256:ℝ)
    (13826776627/25000000000000:ℝ) (53562210939/100000000000000:ℝ) (316814201967971705613/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_253 (thetaFirstMode_refined_node_0757).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_254 :
    (4021428563062967/3906250000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(255/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-110114243309089027794124816047/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (127/256:ℝ) (255/512:ℝ)-(127/256:ℝ)*thetaPowerMass 0 (127/256:ℝ) (255/512:ℝ)) ≤
      thetaFirstModeFirst (127/256:ℝ)*(thetaPowerMass 1 (127/256:ℝ) (255/512:ℝ)-(127/256:ℝ)*thetaPowerMass 0 (127/256:ℝ) (255/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0385.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (127/256:ℝ) (255/512:ℝ)
    (127/256:ℝ) (26781033237/50000000000000:ℝ) (-110114243309089027794124816047/12500000000000000000000000000000:ℝ) (24755349375981761440733/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_254
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0762).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_254 :
    (∫ x in (127/256:ℝ)..(255/512:ℝ), x^0*thetaFirstMode x) ≤ (257373048392013723/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (127/256:ℝ) (255/512:ℝ)
    (53562210939/100000000000000:ℝ) (12966414799/25000000000000:ℝ) (24755349375981761440733/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_254 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0763).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_255 :
    (996813112028202021/1000000000000000000000000:ℝ) ≤ ∫ x in (255/512:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x := by
  have hd : (-428099420546085749331760911113/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (255/512:ℝ) (1/2:ℝ)-(160303981759231989195/321852051581633495552:ℝ)*thetaPowerMass 0 (255/512:ℝ) (1/2:ℝ)) ≤
      thetaFirstModeFirst (160303981759231989195/321852051581633495552:ℝ)*(thetaPowerMass 1 (255/512:ℝ) (1/2:ℝ)-(160303981759231989195/321852051581633495552:ℝ)*thetaPowerMass 0 (255/512:ℝ) (1/2:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0387.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (255/512:ℝ) (1/2:ℝ)
    (160303981759231989195/321852051581633495552:ℝ) (12962007471/25000000000000:ℝ) (-428099420546085749331760911113/50000000000000000000000000000000:ℝ) (60440137359506429916117/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_255
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0767).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_255 :
    (∫ x in (255/512:ℝ)..(1/2:ℝ), x^0*thetaFirstMode x) ≤ (498409668770065217/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (255/512:ℝ) (1/2:ℝ)
    (12966414799/25000000000000:ℝ) (50216326329/100000000000000:ℝ) (60440137359506429916117/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_255 (thetaFirstMode_refined_node_0763).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator
