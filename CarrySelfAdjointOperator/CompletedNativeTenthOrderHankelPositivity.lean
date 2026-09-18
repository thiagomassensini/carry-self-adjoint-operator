import CarrySelfAdjointOperator.ThetaTenthMomentCertificateData.CompletedNativeThetaTenthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeTenthOrderHankelMomentForm
import Mathlib.Tactic

namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192

/- The following six theta bounds are conservative: the lower side uses only
the already-proved first-mode lower estimate, while the upper side uses the
two-mode/certified-exterior replay. -/
theorem completedNativeThetaTailMoment_0_tenth_certified_bounds :
    (11516544931740/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 0 ∧
      completedNativeThetaTailMoment 0 ≤ (11517046272860/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 0
  have hfirstlo := thetaTenth_first_integral_lower_0
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    0 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_0
  have hsecondhi := thetaTenth_second_integral_upper_0
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeThetaTailMoment_2_tenth_certified_bounds :
    (247316428382/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 2 ∧
      completedNativeThetaTailMoment 2 ≤ (247328041335/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 2
  have hfirstlo := thetaTenth_first_integral_lower_2
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    2 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_2
  have hsecondhi := thetaTenth_second_integral_upper_2
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeThetaTailMoment_4_tenth_certified_bounds :
    (20000021893/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 4 ∧
      completedNativeThetaTailMoment 4 ≤ (20001454250/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 4
  have hfirstlo := thetaTenth_first_integral_lower_4
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    4 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_4
  have hsecondhi := thetaTenth_second_integral_upper_4
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeThetaTailMoment_6_tenth_certified_bounds :
    (2876933922/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 6 ∧
      completedNativeThetaTailMoment 6 ≤ (2877230214/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 6
  have hfirstlo := thetaTenth_first_integral_lower_6
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    6 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_6
  have hsecondhi := thetaTenth_second_integral_upper_6
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeThetaTailMoment_8_tenth_certified_bounds :
    (589716911/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 8 ∧
      completedNativeThetaTailMoment 8 ≤ (589803742/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 8
  have hfirstlo := thetaTenth_first_integral_lower_8
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    8 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_8
  have hsecondhi := thetaTenth_second_integral_upper_8
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeThetaTailMoment_10_tenth_certified_bounds :
    (155192558/1000000000000000:ℝ) ≤ completedNativeThetaTailMoment 10 ∧
      completedNativeThetaTailMoment 10 ≤ (155227863/1000000000000000:ℝ) := by
  have hlow := completedNativeThetaTailMoment_finite_lower 10
  have hfirstlo := thetaTenth_first_integral_lower_10
  have hupper := completedNativeThetaTailMoment_finite_upper_refined_two_mode
    10 (by norm_num)
  have hfirsthi := thetaTenth_first_integral_upper_10
  have hsecondhi := thetaTenth_second_integral_upper_10
  have hrem := mul_le_mul_of_nonneg_left hfirsthi
    (by norm_num : (0:ℝ) ≤ 1 / (12300 * 12299 : ℝ))
  constructor
  · linarith
  · linarith

theorem completedNativeXiCosineMoment_zero_tenth_certified_bounds :
    (497120738431785/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 0 ∧
      completedNativeXiCosineMoment 0 ≤ (497120863767065/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments]
  have h := completedNativeThetaTailMoment_0_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_one_tenth_certified_bounds :
    (22971257853146/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 1 ∧
      completedNativeXiCosineMoment 1 ≤ (22972263438625/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_one_eq_thetaTailMoments]
  have h0 := completedNativeThetaTailMoment_0_tenth_certified_bounds
  have h2 := completedNativeThetaTailMoment_2_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_two_tenth_certified_bounds :
    (2962796777021/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 2 ∧
      completedNativeXiCosineMoment 2 ≤ (2962936490547/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_two_eq_thetaTailMoments]
  have h2 := completedNativeThetaTailMoment_2_tenth_certified_bounds
  have h4 := completedNativeThetaTailMoment_4_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_three_tenth_certified_bounds :
    (599281349236/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 3 ∧
      completedNativeXiCosineMoment 3 ≤ (599324394020/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_three_eq_thetaTailMoments]
  have h4 := completedNativeThetaTailMoment_4_tenth_certified_bounds
  have h6 := completedNativeThetaTailMoment_6_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_four_tenth_certified_bounds :
    (160960848696/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 4 ∧
      completedNativeXiCosineMoment 4 ≤ (160977462757/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_four_eq_thetaTailMoments]
  have h6 := completedNativeThetaTailMoment_6_tenth_certified_bounds
  have h8 := completedNativeThetaTailMoment_8_tenth_certified_bounds
  constructor <;> linarith

theorem completedNativeXiCosineMoment_five_tenth_certified_bounds :
    (53035715024/1000000000000000:ℝ) ≤ completedNativeXiCosineMoment 5 ∧
      completedNativeXiCosineMoment 5 ≤ (53043538641/1000000000000000:ℝ) := by
  rw [completedNativeXiCosineMoment_five_eq_thetaTailMoments]
  have h8 := completedNativeThetaTailMoment_8_tenth_certified_bounds
  have h10 := completedNativeThetaTailMoment_10_tenth_certified_bounds
  constructor <;> linarith

private def tenthN10Center0 : ℝ := (19884832043977/40000000000000:ℝ)
private def tenthN10Center1 : ℝ := (45943521291771/2000000000000000:ℝ)
private def tenthN10Center2 : ℝ := (370358329223/125000000000000:ℝ)
private def tenthN10Center3 : ℝ := (149825717907/250000000000000:ℝ)
private def tenthN10Center4 : ℝ := (321938311453/2000000000000000:ℝ)
private def tenthN10Center5 : ℝ := (21215850733/400000000000000:ℝ)
private def tenthN10Radius0 : ℝ := (1566691/25000000000000:ℝ)
private def tenthN10Radius1 : ℝ := (1005585479/2000000000000000:ℝ)
private def tenthN10Radius2 : ℝ := (69856763/1000000000000000:ℝ)
private def tenthN10Radius3 : ℝ := (2690299/125000000000000:ℝ)
private def tenthN10Radius4 : ℝ := (16614061/2000000000000000:ℝ)
private def tenthN10Radius5 : ℝ := (7823617/2000000000000000:ℝ)
private def tenthN10Center : ℝ :=
  canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
    tenthN10Center0 tenthN10Center1 tenthN10Center2
    tenthN10Center3 tenthN10Center4 tenthN10Center5

private def tenthN10DeviationTerms (m0 m1 m2 m3 m4 m5 : ℝ) : Fin 119 → ℝ :=
  ![
    (1197618739263578735296259865922655847981561187378499/200000000000000000000000000000000000000000000000000000000:ℝ) * (m5 - tenthN10Center5)^1,
    (-161141220249109063486944877269723649966513449927319197/20000000000000000000000000000000000000000000000000000000000:ℝ) * (m4 - tenthN10Center4)^1,
    (-163497321344516168555057458537462465585731/160000000000000000000000000000000000000000:ℝ) * (m4 - tenthN10Center4)^2,
    (5591960529337495713526223704486694990759777534004666849/1600000000000000000000000000000000000000000000000000000000000:ℝ) * (m3 - tenthN10Center3)^1,
    (381493749803871059961800736587412419700039/640000000000000000000000000000000000000000:ℝ) * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1,
    (40535344631561766137737381312587113381591463/32000000000000000000000000000000000000000000:ℝ) * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-70805295411083506272286557107637991000196751/100000000000000000000000000000000000000000000:ℝ) * (m3 - tenthN10Center3)^2,
    (-523122859586921884220794947867/800000000000000000000000000:ℝ) * (m3 - tenthN10Center3)^3,
    (-363711561105527216880782739218240735967991518108562357/640000000000000000000000000000000000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1,
    (-2398869250343383674238871313599903981417803/6400000000000000000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (-30216599707686131314079542782645889548073563/320000000000000000000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (3389220660710790476807042086021092374465841/10000000000000000000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (24910612361281994486704521327/40000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (1208665287415574013042642152241/4000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^2,
    (-4313059665313366988290430340345604423591957/80000000000000000000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^2,
    (-2767845817920221609633835703/32000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^2 * (m5 - tenthN10Center5)^1,
    (-172666469630796287577520307463/1600000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^2 * (m4 - tenthN10Center4)^1,
    (-4265534542077004380855321427119/80000000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^2 * (m3 - tenthN10Center3)^1,
    (-437951107757998916398232433/100000000000000000000000000:ℝ) * (m2 - tenthN10Center2)^3,
    (-2923070310464619/400000000000:ℝ) * (m2 - tenthN10Center2)^3 * (m3 - tenthN10Center3)^1,
    (2985314741299662365466063600885725670559729391413401/100000000000000000000000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1,
    (20431187346508012732356968382967598369037/400000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m5 - tenthN10Center5)^1,
    (-385081030572012341879903541997385633919297/20000000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^1,
    (-3558658908754570640957788761/80000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^2,
    (-3613661052332159064777980024597592781278897/200000000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1,
    (8303537453760664828901507109/320000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1,
    (-402888429138524671014214050747/8000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-843947672220392397194324784843/50000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^2,
    (2588551895804464805582680460056430031726117/320000000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1,
    (19185163292310698619724478607/1600000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (-863574606923981995001623714659/160000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (13605832179980255973008856969/625000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (26307632794181571/2000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^2,
    (-5962919412384104093709593409/40000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^2,
    (-3758233256311653/800000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^2 * (m4 - tenthN10Center4)^1,
    (20261092889671011/20000000000000:ℝ) * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^2 * (m3 - tenthN10Center3)^1,
    (-2225442873710923155425538034663613855433/6250000000000000000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^2,
    (154654776626433169385037291/200000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m5 - tenthN10Center5)^1,
    (11187105391312518064057961769/5000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m4 - tenthN10Center4)^1,
    (-1158834550464257694666777946773/400000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m3 - tenthN10Center3)^1,
    (-8769210931393857/8000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-60783278669013033/25000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m3 - tenthN10Center3)^2,
    (1596132439483591558181890173/6400000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1,
    (417581472923517/1600000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (78149929717302471/80000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (163328023187343/1250000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (66073141596987/5000000000000:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^2,
    (22050/1:ℝ) * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^2 * (m3 - tenthN10Center3)^1,
    (-295540938815633751194318511/50000000000000000000000000000:ℝ) * (m1 - tenthN10Center1)^3,
    (209993172669441/5000000000000:ℝ) * (m1 - tenthN10Center1)^3 * (m4 - tenthN10Center4)^1,
    (-66073141596987/1562500000000:ℝ) * (m1 - tenthN10Center1)^3 * (m3 - tenthN10Center3)^1,
    (-35280/1:ℝ) * (m1 - tenthN10Center1)^3 * (m3 - tenthN10Center3)^2,
    (182539022593851/80000000000000:ℝ) * (m1 - tenthN10Center1)^3 * (m2 - tenthN10Center2)^1,
    (14175/1:ℝ) * (m1 - tenthN10Center1)^3 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (-93359048044702664377510637517100455404284713645259/400000000000000000000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1,
    (-15935033168338908918875688505885435301507/20000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m5 - tenthN10Center5)^1,
    (104468023312903906038875678238109554473313/200000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m4 - tenthN10Center4)^1,
    (-8222212839561727979881919403/2000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m4 - tenthN10Center4)^2,
    (122354768971431092582502043338997077796719/1600000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m3 - tenthN10Center3)^1,
    (19185163292310698619724478607/8000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1,
    (5007877469883883593903500423919/800000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-4576475751847271448683701887/1562500000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m3 - tenthN10Center3)^2,
    (-26307632794181571/10000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m3 - tenthN10Center3)^3,
    (-117985262734790106720932325503853954006623/1600000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1,
    (-285603240013955041807987575539/160000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (537924704704036122800311803/2500000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (18618074292907700832189560697/25000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (1252744418770551/500000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (60783278669013033/100000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^2,
    (-10536561868839107326463042063/80000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^2,
    (-139193824307839/400000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^2 * (m5 - tenthN10Center5)^1,
    (-8683325524144719/40000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^2 * (m4 - tenthN10Center4)^1,
    (-163328023187343/1250000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^2 * (m3 - tenthN10Center3)^1,
    (-22024380532329/2500000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^3,
    (-14700/1:ℝ) * (m0 - tenthN10Center0)^1 * (m2 - tenthN10Center2)^3 * (m3 - tenthN10Center3)^1,
    (75028184194183140496630021444436632749/10000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1,
    (167537275324054100643699297/1250000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m5 - tenthN10Center5)^1,
    (-10064271381900906443467320387/50000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^1,
    (-178963488395793/1000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^2,
    (33279068588893538803510892403/400000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1,
    (417581472923517/4000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1,
    (-20261092889671011/200000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (489984069562029/6250000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^2,
    (707532910141289372659254771/400000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1,
    (964813947127191/40000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (-69997724223147/1250000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (198219424790961/6250000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (26460/1:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^2,
    (-60846340864617/40000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^2,
    (-9450/1:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^1 * (m2 - tenthN10Center2)^2 * (m4 - tenthN10Center4)^1,
    (-13021135256084608748410161/100000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2,
    (7777524913683/5000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m5 - tenthN10Center5)^1,
    (-66073141596987/50000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m4 - tenthN10Center4)^1,
    (-141974795350773/400000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m3 - tenthN10Center3)^1,
    (-2205/1:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (445532865393/16000000000000:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1,
    (525/1:ℝ) * (m0 - tenthN10Center0)^1 * (m1 - tenthN10Center1)^2 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (-85398518963791071623756483933215614469/2000000000000000000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2,
    (-162696311860650873140243723/100000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m5 - tenthN10Center5)^1,
    (314346112431239952294269337/100000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m4 - tenthN10Center4)^1,
    (-413491691625939/100000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m4 - tenthN10Center4)^2,
    (-6084983632874551304567021613/4000000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m3 - tenthN10Center3)^1,
    (964813947127191/400000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1,
    (23332574741049/3125000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-594658274372883/125000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m3 - tenthN10Center3)^2,
    (-2646/1:ℝ) * (m0 - tenthN10Center0)^2 * (m3 - tenthN10Center3)^3,
    (415931375919424348967137/3125000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^1,
    (-2592508304561/1250000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^1 * (m5 - tenthN10Center5)^1,
    (9439020228141/6250000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^1 * (m4 - tenthN10Center4)^1,
    (20282113621539/50000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1,
    (2520/1:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^1 * (m3 - tenthN10Center3)^1 * (m4 - tenthN10Center4)^1,
    (-148510955131/8000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^2,
    (-350/1:ℝ) * (m0 - tenthN10Center0)^2 * (m2 - tenthN10Center2)^2 * (m5 - tenthN10Center5)^1,
    (-265275673344189271816371/200000000000000000000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1,
    (3146340076047/50000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1 * (m5 - tenthN10Center5)^1,
    (-2897444803077/50000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^1,
    (-180/1:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1 * (m4 - tenthN10Center4)^2,
    (445532865393/80000000000000:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1,
    (105/1:ℝ) * (m0 - tenthN10Center0)^2 * (m1 - tenthN10Center1)^1 * (m3 - tenthN10Center3)^1 * (m5 - tenthN10Center5)^1
  ]

private def tenthN10DeviationBounds : Fin 119 → ℝ :=
  ![
    (1197618739263578735296259865922655847981561187378499/200000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius5^1,
    (161141220249109063486944877269723649966513449927319197/20000000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius4^1,
    (163497321344516168555057458537462465585731/160000000000000000000000000000000000000000:ℝ) * tenthN10Radius4^2,
    (5591960529337495713526223704486694990759777534004666849/1600000000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius3^1,
    (381493749803871059961800736587412419700039/640000000000000000000000000000000000000000:ℝ) * tenthN10Radius3^1 * tenthN10Radius5^1,
    (40535344631561766137737381312587113381591463/32000000000000000000000000000000000000000000:ℝ) * tenthN10Radius3^1 * tenthN10Radius4^1,
    (70805295411083506272286557107637991000196751/100000000000000000000000000000000000000000000:ℝ) * tenthN10Radius3^2,
    (523122859586921884220794947867/800000000000000000000000000:ℝ) * tenthN10Radius3^3,
    (363711561105527216880782739218240735967991518108562357/640000000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius2^1,
    (2398869250343383674238871313599903981417803/6400000000000000000000000000000000000000000:ℝ) * tenthN10Radius2^1 * tenthN10Radius5^1,
    (30216599707686131314079542782645889548073563/320000000000000000000000000000000000000000000:ℝ) * tenthN10Radius2^1 * tenthN10Radius4^1,
    (3389220660710790476807042086021092374465841/10000000000000000000000000000000000000000000:ℝ) * tenthN10Radius2^1 * tenthN10Radius3^1,
    (24910612361281994486704521327/40000000000000000000000000:ℝ) * tenthN10Radius2^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (1208665287415574013042642152241/4000000000000000000000000000:ℝ) * tenthN10Radius2^1 * tenthN10Radius3^2,
    (4313059665313366988290430340345604423591957/80000000000000000000000000000000000000000000:ℝ) * tenthN10Radius2^2,
    (2767845817920221609633835703/32000000000000000000000000:ℝ) * tenthN10Radius2^2 * tenthN10Radius5^1,
    (172666469630796287577520307463/1600000000000000000000000000:ℝ) * tenthN10Radius2^2 * tenthN10Radius4^1,
    (4265534542077004380855321427119/80000000000000000000000000000:ℝ) * tenthN10Radius2^2 * tenthN10Radius3^1,
    (437951107757998916398232433/100000000000000000000000000:ℝ) * tenthN10Radius2^3,
    (2923070310464619/400000000000:ℝ) * tenthN10Radius2^3 * tenthN10Radius3^1,
    (2985314741299662365466063600885725670559729391413401/100000000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^1,
    (20431187346508012732356968382967598369037/400000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius5^1,
    (385081030572012341879903541997385633919297/20000000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius4^1,
    (3558658908754570640957788761/80000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius4^2,
    (3613661052332159064777980024597592781278897/200000000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius3^1,
    (8303537453760664828901507109/320000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius3^1 * tenthN10Radius5^1,
    (402888429138524671014214050747/8000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (843947672220392397194324784843/50000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius3^2,
    (2588551895804464805582680460056430031726117/320000000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^1,
    (19185163292310698619724478607/1600000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (863574606923981995001623714659/160000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (13605832179980255973008856969/625000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius3^1,
    (26307632794181571/2000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius3^2,
    (5962919412384104093709593409/40000000000000000000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^2,
    (3758233256311653/800000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^2 * tenthN10Radius4^1,
    (20261092889671011/20000000000000:ℝ) * tenthN10Radius1^1 * tenthN10Radius2^2 * tenthN10Radius3^1,
    (2225442873710923155425538034663613855433/6250000000000000000000000000000000000000000:ℝ) * tenthN10Radius1^2,
    (154654776626433169385037291/200000000000000000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius5^1,
    (11187105391312518064057961769/5000000000000000000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius4^1,
    (1158834550464257694666777946773/400000000000000000000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius3^1,
    (8769210931393857/8000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (60783278669013033/25000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius3^2,
    (1596132439483591558181890173/6400000000000000000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^1,
    (417581472923517/1600000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (78149929717302471/80000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (163328023187343/1250000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^1 * tenthN10Radius3^1,
    (66073141596987/5000000000000:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^2,
    (22050/1:ℝ) * tenthN10Radius1^2 * tenthN10Radius2^2 * tenthN10Radius3^1,
    (295540938815633751194318511/50000000000000000000000000000:ℝ) * tenthN10Radius1^3,
    (209993172669441/5000000000000:ℝ) * tenthN10Radius1^3 * tenthN10Radius4^1,
    (66073141596987/1562500000000:ℝ) * tenthN10Radius1^3 * tenthN10Radius3^1,
    (35280/1:ℝ) * tenthN10Radius1^3 * tenthN10Radius3^2,
    (182539022593851/80000000000000:ℝ) * tenthN10Radius1^3 * tenthN10Radius2^1,
    (14175/1:ℝ) * tenthN10Radius1^3 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (93359048044702664377510637517100455404284713645259/400000000000000000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1,
    (15935033168338908918875688505885435301507/20000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius5^1,
    (104468023312903906038875678238109554473313/200000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius4^1,
    (8222212839561727979881919403/2000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius4^2,
    (122354768971431092582502043338997077796719/1600000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius3^1,
    (19185163292310698619724478607/8000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius3^1 * tenthN10Radius5^1,
    (5007877469883883593903500423919/800000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (4576475751847271448683701887/1562500000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius3^2,
    (26307632794181571/10000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius3^3,
    (117985262734790106720932325503853954006623/1600000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1,
    (285603240013955041807987575539/160000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (537924704704036122800311803/2500000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (18618074292907700832189560697/25000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1 * tenthN10Radius3^1,
    (1252744418770551/500000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (60783278669013033/100000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^1 * tenthN10Radius3^2,
    (10536561868839107326463042063/80000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^2,
    (139193824307839/400000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^2 * tenthN10Radius5^1,
    (8683325524144719/40000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^2 * tenthN10Radius4^1,
    (163328023187343/1250000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^2 * tenthN10Radius3^1,
    (22024380532329/2500000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^3,
    (14700/1:ℝ) * tenthN10Radius0^1 * tenthN10Radius2^3 * tenthN10Radius3^1,
    (75028184194183140496630021444436632749/10000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1,
    (167537275324054100643699297/1250000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius5^1,
    (10064271381900906443467320387/50000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius4^1,
    (178963488395793/1000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius4^2,
    (33279068588893538803510892403/400000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius3^1,
    (417581472923517/4000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius3^1 * tenthN10Radius5^1,
    (20261092889671011/200000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (489984069562029/6250000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius3^2,
    (707532910141289372659254771/400000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^1,
    (964813947127191/40000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (69997724223147/1250000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (198219424790961/6250000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius3^1,
    (26460/1:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^1 * tenthN10Radius3^2,
    (60846340864617/40000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^2,
    (9450/1:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^1 * tenthN10Radius2^2 * tenthN10Radius4^1,
    (13021135256084608748410161/100000000000000000000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2,
    (7777524913683/5000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius5^1,
    (66073141596987/50000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius4^1,
    (141974795350773/400000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius3^1,
    (2205/1:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (445532865393/16000000000000:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius2^1,
    (525/1:ℝ) * tenthN10Radius0^1 * tenthN10Radius1^2 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (85398518963791071623756483933215614469/2000000000000000000000000000000000000000000000:ℝ) * tenthN10Radius0^2,
    (162696311860650873140243723/100000000000000000000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius5^1,
    (314346112431239952294269337/100000000000000000000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius4^1,
    (413491691625939/100000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius4^2,
    (6084983632874551304567021613/4000000000000000000000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius3^1,
    (964813947127191/400000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius3^1 * tenthN10Radius5^1,
    (23332574741049/3125000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (594658274372883/125000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius3^2,
    (2646/1:ℝ) * tenthN10Radius0^2 * tenthN10Radius3^3,
    (415931375919424348967137/3125000000000000000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^1,
    (2592508304561/1250000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^1 * tenthN10Radius5^1,
    (9439020228141/6250000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^1 * tenthN10Radius4^1,
    (20282113621539/50000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^1 * tenthN10Radius3^1,
    (2520/1:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^1 * tenthN10Radius3^1 * tenthN10Radius4^1,
    (148510955131/8000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^2,
    (350/1:ℝ) * tenthN10Radius0^2 * tenthN10Radius2^2 * tenthN10Radius5^1,
    (265275673344189271816371/200000000000000000000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1,
    (3146340076047/50000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1 * tenthN10Radius5^1,
    (2897444803077/50000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1 * tenthN10Radius4^1,
    (180/1:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1 * tenthN10Radius4^2,
    (445532865393/80000000000000:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1 * tenthN10Radius3^1,
    (105/1:ℝ) * tenthN10Radius0^2 * tenthN10Radius1^1 * tenthN10Radius3^1 * tenthN10Radius5^1
  ]

private def tenthN10Deviation (m0 m1 m2 m3 m4 m5 : ℝ) : ℝ :=
  ∑ i : Fin 119, tenthN10DeviationTerms m0 m1 m2 m3 m4 m5 i

private def tenthN10Error : ℝ :=
  ∑ i : Fin 119, tenthN10DeviationBounds i

private lemma abs_centered_product_le
    (c d0 d1 d2 d3 d4 d5 r0 r1 r2 r3 r4 r5 : ℝ)
    (e0 e1 e2 e3 e4 e5 : ℕ)
    (hd0 : |d0| ≤ r0) (hd1 : |d1| ≤ r1) (hd2 : |d2| ≤ r2)
    (hd3 : |d3| ≤ r3) (hd4 : |d4| ≤ r4) (hd5 : |d5| ≤ r5)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hr3 : 0 ≤ r3) (hr4 : 0 ≤ r4) (hr5 : 0 ≤ r5) :
    |c * d0^e0 * d1^e1 * d2^e2 * d3^e3 * d4^e4 * d5^e5| ≤
      |c| * r0^e0 * r1^e1 * r2^e2 * r3^e3 * r4^e4 * r5^e5 := by
  simp only [abs_mul, abs_pow]
  gcongr

theorem tenthN10_centered_identity (m0 m1 m2 m3 m4 m5 : ℝ) :
    canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
        m0 m1 m2 m3 m4 m5 =
      tenthN10Center + tenthN10Deviation m0 m1 m2 m3 m4 m5 := by
  simp [canonicalCompletedNativeHankelThreeXiTenthMomentNumerator,
    tenthN10Center, tenthN10Center0, tenthN10Center1, tenthN10Center2,
    tenthN10Center3, tenthN10Center4, tenthN10Center5,
    tenthN10Deviation, tenthN10DeviationTerms,
    Fin.sum_univ_succ]
  ring

theorem canonicalCompletedNativeHankelThreeXiTenthMomentNumerator_ge_box_margin :
    (1/1000000000000000:ℝ) ≤
      canonicalCompletedNativeHankelThreeXiTenthMomentNumerator
        (completedNativeXiCosineMoment 0)
        (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2)
        (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4)
        (completedNativeXiCosineMoment 5) := by
  have h0 := completedNativeXiCosineMoment_zero_tenth_certified_bounds
  have h1 := completedNativeXiCosineMoment_one_tenth_certified_bounds
  have h2 := completedNativeXiCosineMoment_two_tenth_certified_bounds
  have h3 := completedNativeXiCosineMoment_three_tenth_certified_bounds
  have h4 := completedNativeXiCosineMoment_four_tenth_certified_bounds
  have h5 := completedNativeXiCosineMoment_five_tenth_certified_bounds
  have hd0 : |completedNativeXiCosineMoment 0 - tenthN10Center0| ≤
      tenthN10Radius0 := by
    rw [abs_le]
    constructor <;> linarith [h0.1, h0.2]
  have hd1 : |completedNativeXiCosineMoment 1 - tenthN10Center1| ≤
      tenthN10Radius1 := by
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hd2 : |completedNativeXiCosineMoment 2 - tenthN10Center2| ≤
      tenthN10Radius2 := by
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have hd3 : |completedNativeXiCosineMoment 3 - tenthN10Center3| ≤
      tenthN10Radius3 := by
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]
  have hd4 : |completedNativeXiCosineMoment 4 - tenthN10Center4| ≤
      tenthN10Radius4 := by
    rw [abs_le]
    constructor <;> linarith [h4.1, h4.2]
  have hd5 : |completedNativeXiCosineMoment 5 - tenthN10Center5| ≤
      tenthN10Radius5 := by
    rw [abs_le]
    constructor <;> linarith [h5.1, h5.2]
  have hr0 : 0 ≤ tenthN10Radius0 := by norm_num [tenthN10Radius0]
  have hr1 : 0 ≤ tenthN10Radius1 := by norm_num [tenthN10Radius1]
  have hr2 : 0 ≤ tenthN10Radius2 := by norm_num [tenthN10Radius2]
  have hr3 : 0 ≤ tenthN10Radius3 := by norm_num [tenthN10Radius3]
  have hr4 : 0 ≤ tenthN10Radius4 := by norm_num [tenthN10Radius4]
  have hr5 : 0 ≤ tenthN10Radius5 := by norm_num [tenthN10Radius5]
  have hterm : ∀ i : Fin 119,
      |tenthN10DeviationTerms
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) i| ≤
        tenthN10DeviationBounds i := by
    intro i
    fin_cases i
    · convert (abs_centered_product_le
      (c := (1197618739263578735296259865922655847981561187378499/200000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-161141220249109063486944877269723649966513449927319197/20000000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-163497321344516168555057458537462465585731/160000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (5591960529337495713526223704486694990759777534004666849/1600000000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (381493749803871059961800736587412419700039/640000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (40535344631561766137737381312587113381591463/32000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-70805295411083506272286557107637991000196751/100000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-523122859586921884220794947867/800000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 3) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-363711561105527216880782739218240735967991518108562357/640000000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2398869250343383674238871313599903981417803/6400000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-30216599707686131314079542782645889548073563/320000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (3389220660710790476807042086021092374465841/10000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (24910612361281994486704521327/40000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (1208665287415574013042642152241/4000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-4313059665313366988290430340345604423591957/80000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2767845817920221609633835703/32000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-172666469630796287577520307463/1600000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-4265534542077004380855321427119/80000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 2) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-437951107757998916398232433/100000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 3) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2923070310464619/400000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 0) (e2 := 3) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (2985314741299662365466063600885725670559729391413401/100000000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (20431187346508012732356968382967598369037/400000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-385081030572012341879903541997385633919297/20000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-3558658908754570640957788761/80000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-3613661052332159064777980024597592781278897/200000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (8303537453760664828901507109/320000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-402888429138524671014214050747/8000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-843947672220392397194324784843/50000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (2588551895804464805582680460056430031726117/320000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (19185163292310698619724478607/1600000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-863574606923981995001623714659/160000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (13605832179980255973008856969/625000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (26307632794181571/2000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 1) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-5962919412384104093709593409/40000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-3758233256311653/800000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 2) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (20261092889671011/20000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 1) (e2 := 2) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2225442873710923155425538034663613855433/6250000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (154654776626433169385037291/200000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (11187105391312518064057961769/5000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-1158834550464257694666777946773/400000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-8769210931393857/8000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-60783278669013033/25000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (1596132439483591558181890173/6400000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (417581472923517/1600000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (78149929717302471/80000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (163328023187343/1250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (66073141596987/5000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (22050/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 2) (e2 := 2) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-295540938815633751194318511/50000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (209993172669441/5000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-66073141596987/1562500000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-35280/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (182539022593851/80000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (14175/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 0) (e1 := 3) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-93359048044702664377510637517100455404284713645259/400000000000000000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-15935033168338908918875688505885435301507/20000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (104468023312903906038875678238109554473313/200000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-8222212839561727979881919403/2000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (122354768971431092582502043338997077796719/1600000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (19185163292310698619724478607/8000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (5007877469883883593903500423919/800000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-4576475751847271448683701887/1562500000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-26307632794181571/10000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 3) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-117985262734790106720932325503853954006623/1600000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-285603240013955041807987575539/160000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (537924704704036122800311803/2500000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (18618074292907700832189560697/25000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (1252744418770551/500000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (60783278669013033/100000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 1) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-10536561868839107326463042063/80000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-139193824307839/400000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-8683325524144719/40000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-163328023187343/1250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 2) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-22024380532329/2500000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 3) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-14700/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 0) (e2 := 3) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (75028184194183140496630021444436632749/10000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (167537275324054100643699297/1250000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-10064271381900906443467320387/50000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-178963488395793/1000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (33279068588893538803510892403/400000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (417581472923517/4000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-20261092889671011/200000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (489984069562029/6250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (707532910141289372659254771/400000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (964813947127191/40000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-69997724223147/1250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (198219424790961/6250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (26460/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 1) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-60846340864617/40000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-9450/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 1) (e2 := 2) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-13021135256084608748410161/100000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (7777524913683/5000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-66073141596987/50000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-141974795350773/400000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2205/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (445532865393/16000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (525/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 1) (e1 := 2) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-85398518963791071623756483933215614469/2000000000000000000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-162696311860650873140243723/100000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (314346112431239952294269337/100000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-413491691625939/100000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-6084983632874551304567021613/4000000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (964813947127191/400000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (23332574741049/3125000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-594658274372883/125000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 2) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2646/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 0) (e3 := 3) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (415931375919424348967137/3125000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2592508304561/1250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (9439020228141/6250000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 1) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (20282113621539/50000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (2520/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 1) (e3 := 1) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-148510955131/8000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-350/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 0) (e2 := 2) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-265275673344189271816371/200000000000000000000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (3146340076047/50000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-2897444803077/50000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 1) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (-180/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 0) (e4 := 2) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (445532865393/80000000000000:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 0) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
    · convert (abs_centered_product_le
      (c := (105/1:ℝ)) (d0 := completedNativeXiCosineMoment 0 - tenthN10Center0) (d1 := completedNativeXiCosineMoment 1 - tenthN10Center1) (d2 := completedNativeXiCosineMoment 2 - tenthN10Center2) (d3 := completedNativeXiCosineMoment 3 - tenthN10Center3) (d4 := completedNativeXiCosineMoment 4 - tenthN10Center4) (d5 := completedNativeXiCosineMoment 5 - tenthN10Center5) (r0 := tenthN10Radius0) (r1 := tenthN10Radius1) (r2 := tenthN10Radius2) (r3 := tenthN10Radius3) (r4 := tenthN10Radius4) (r5 := tenthN10Radius5) (e0 := 2) (e1 := 1) (e2 := 0) (e3 := 1) (e4 := 0) (e5 := 1) (hd0 := hd0) (hd1 := hd1) (hd2 := hd2) (hd3 := hd3) (hd4 := hd4) (hd5 := hd5) (hr0 := hr0) (hr1 := hr1) (hr2 := hr2) (hr3 := hr3) (hr4 := hr4) (hr5 := hr5)) using 1 <;>
      norm_num [tenthN10DeviationTerms, tenthN10DeviationBounds]
  have htriangle :
      |tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5)| ≤
        ∑ i : Fin 119,
          |tenthN10DeviationTerms
            (completedNativeXiCosineMoment 0)
            (completedNativeXiCosineMoment 1)
            (completedNativeXiCosineMoment 2)
            (completedNativeXiCosineMoment 3)
            (completedNativeXiCosineMoment 4)
            (completedNativeXiCosineMoment 5) i| := by
    unfold tenthN10Deviation
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum :
      (∑ i : Fin 119,
        |tenthN10DeviationTerms
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) i|) ≤
        ∑ i : Fin 119, tenthN10DeviationBounds i := by
    exact Finset.sum_le_sum (fun i _hi => hterm i)
  have herror :
      |tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5)| ≤ tenthN10Error := by
    calc
      _ ≤ ∑ i : Fin 119,
          |tenthN10DeviationTerms
            (completedNativeXiCosineMoment 0)
            (completedNativeXiCosineMoment 1)
            (completedNativeXiCosineMoment 2)
            (completedNativeXiCosineMoment 3)
            (completedNativeXiCosineMoment 4)
            (completedNativeXiCosineMoment 5) i| := htriangle
      _ ≤ ∑ i : Fin 119, tenthN10DeviationBounds i := hsum
      _ = tenthN10Error := rfl
  have hcenter : (23/100000000000000:ℝ) ≤ tenthN10Center := by
    norm_num [tenthN10Center, tenthN10Center0, tenthN10Center1,
      tenthN10Center2, tenthN10Center3, tenthN10Center4, tenthN10Center5,
      canonicalCompletedNativeHankelThreeXiTenthMomentNumerator]
  have herr : tenthN10Error ≤ (223/1000000000000000:ℝ) := by
    norm_num [tenthN10Error, tenthN10DeviationBounds,
      tenthN10Radius0, tenthN10Radius1, tenthN10Radius2,
      tenthN10Radius3, tenthN10Radius4, tenthN10Radius5,
      Fin.sum_univ_succ]
  have hdevlow :
      -tenthN10Error ≤ tenthN10Deviation
          (completedNativeXiCosineMoment 0)
          (completedNativeXiCosineMoment 1)
          (completedNativeXiCosineMoment 2)
          (completedNativeXiCosineMoment 3)
          (completedNativeXiCosineMoment 4)
          (completedNativeXiCosineMoment 5) :=
    (abs_le.mp herror).1
  have hid := tenthN10_centered_identity
    (completedNativeXiCosineMoment 0)
    (completedNativeXiCosineMoment 1)
    (completedNativeXiCosineMoment 2)
    (completedNativeXiCosineMoment 3)
    (completedNativeXiCosineMoment 4)
    (completedNativeXiCosineMoment 5)
  calc
    (1/1000000000000000:ℝ) ≤ tenthN10Center - tenthN10Error := by
      linarith
    _ ≤ tenthN10Center + tenthN10Deviation
        (completedNativeXiCosineMoment 0)
        (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2)
        (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4)
        (completedNativeXiCosineMoment 5) := by
      linarith
    _ = _ := hid.symm

theorem canonicalCompletedNativeHankel_three_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det := by
  rw [canonicalCompletedNativeHankel_three_det_eq_xiTenthMomentRatio]
  have hn := canonicalCompletedNativeHankelThreeXiTenthMomentNumerator_ge_box_margin
  have hm := completedNativeXiCosineMoment_pos 0
  have hd : 0 < 36578304000 * completedNativeXiCosineMoment 0 ^ 5 := by
    positivity
  exact div_pos (by linarith) hd

end
end CarrySelfAdjointOperator
