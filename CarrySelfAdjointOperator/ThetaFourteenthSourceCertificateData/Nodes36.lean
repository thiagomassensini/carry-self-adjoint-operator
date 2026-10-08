import CarrySelfAdjointOperator.CompletedNativeThetaCubicQuadrature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaFourteenth_node_576 :
    ((3985457801/10000000000000000000000:ℝ) ≤ thetaFirstMode (9/8:ℝ) ∧ thetaFirstMode (9/8:ℝ) ≤ (39854578403/100000000000000000000000:ℝ)) ∧
    ((2980660120270455712213/100000000000000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/8:ℝ)) ∧ Real.pi*Real.exp (2*(9/8:ℝ)) ≤ (298066012027045571223/10000000000000000000:ℝ)) := by
  have hf := thetaFirstMode_precise_node_bounds (9/8:ℝ) (474386791817926286027/50000000000000000000:ℝ) (118596697954481571507/12500000000000000000:ℝ) (3985457801/10000000000000000000000:ℝ) (39854578403/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaExpLower,Finset.sum_range_succ])
    (by norm_num [thetaExpUpper,Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaExpUpper,Finset.sum_range_succ])
    (by norm_num [thetaExpLower,Finset.sum_range_succ])
  have he := thetaExp_bounds (x:=2*(9/8:ℝ)) (by norm_num) (by norm_num)
  have hel : (474386791817926286027/50000000000000000000:ℝ) ≤ Real.exp (2*(9/8:ℝ)) :=
    (show (474386791817926286027/50000000000000000000:ℝ) ≤ thetaExpLower (2*(9/8:ℝ)) by norm_num [thetaExpLower,Finset.sum_range_succ]).trans he.1
  have heu : Real.exp (2*(9/8:ℝ)) ≤ (118596697954481571507/12500000000000000000:ℝ) :=
    he.2.trans (by norm_num [thetaExpUpper,Finset.sum_range_succ])
  have hlo := mul_le_mul (show (157079632679489661923/50000000000000000000:ℝ) ≤ Real.pi by linarith [Real.pi_gt_d20])
    hel (by norm_num : (0:ℝ) ≤ (474386791817926286027/50000000000000000000:ℝ)) Real.pi_pos.le
  have hhi := mul_le_mul (show Real.pi ≤ (314159265358979323847/100000000000000000000:ℝ) by linarith [Real.pi_lt_d20])
    heu (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ (314159265358979323847/100000000000000000000:ℝ))
  refine ⟨hf,?_,?_⟩
  · exact (show (2980660120270455712213/100000000000000000000:ℝ) ≤ (157079632679489661923/50000000000000000000:ℝ)*(474386791817926286027/50000000000000000000:ℝ) by norm_num).trans hlo
  · exact hhi.trans (by norm_num)

theorem thetaFourteenth_derivatives_576 :
    ((-11779658800576428674760974096869/500000000000000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/8:ℝ) ∧ thetaFirstModeFirst (9/8:ℝ) ≤ (-11779658682453985948064311823613/500000000000000000000000000000000000000000:ℝ)) ∧
    ((33628737870613662044678011842381418396542970745885569/25000000000000000000000000000000000000000000000000000000000000:ℝ) ≤ thetaFirstModeSecond (9/8:ℝ) ∧ thetaFirstModeSecond (9/8:ℝ) ≤ (3362873823736357173011442641628651943865728640800787/2500000000000000000000000000000000000000000000000000000000000:ℝ)) ∧
    ((-924916816917768061579501983720132601701706526076228630705012668562952501/12500000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ) ≤ thetaFirstModeThird (9/8:ℝ) ∧ thetaFirstModeThird (9/8:ℝ) ≤ (-92491680517863258206823508327240551645883563653273152511945585403293754197/1250000000000000000000000000000000000000000000000000000000000000000000000000000000:ℝ)) := by
  have h := thetaFirstMode_cubic_node_derivative_bounds (9/8:ℝ) (2980660120270455712213/100000000000000000000:ℝ) (298066012027045571223/10000000000000000000:ℝ) (3985457801/10000000000000000000000:ℝ) (39854578403/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFourteenth_node_576).2.1 (thetaFourteenth_node_576).2.2 (thetaFourteenth_node_576).1.1 (thetaFourteenth_node_576).1.2
  convert h using 1 <;> norm_num

end CarrySelfAdjointOperator
