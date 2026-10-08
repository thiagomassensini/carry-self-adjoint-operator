import CarrySelfAdjointOperator.CompletedNativeChiralReturnEleventhSourceJet

/-!
# Thirteenth jet of the unchanged completed logarithmic source

The division-free source recurrence and existing raw even jets determine
this coefficient. The fourteenth characteristic derivative is retained
explicitly, without assuming a new integral bound or any moment sign.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Connected numerator fixed by thirteen differentiations of -F'/F.
The last argument is the negative real fourteenth characteristic jet. -/
def nativeSourceThirteenthNumerator (a b c d e f g h : ℝ) : ℝ :=
  a^6*h - 91*a^5*b*g - 1001*a^5*c*f - 3003*a^5*d*e +
    6006*a^4*b^2*f + 90090*a^4*b*c*e + 84084*a^4*b*d^2 +
    210210*a^4*c^2*d - 270270*a^3*b^3*e - 3783780*a^3*b^2*c*d -
    3153150*a^3*b*c^3 + 7567560*a^2*b^4*d + 37837800*a^2*b^3*c^2 -
    113513400*a*b^5*c + 97297200*b^7

/-- Complex source identity BEFORE taking the real coefficient. Even
characteristic jets through twelve are the existing raw integral ones.
No value or sign is assigned to the next characteristic jet. -/
theorem nativeSourceLogSlope_thirteenth_derivative_eq_rawCharacteristicJet :
    iteratedDeriv 13 completedNativeOperatorLogDerivative 0 =
      (nativeSourceThirteenthNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) 0 : ℝ) /
          (completedNativeXiCosineMoment 0 : ℂ)^7 -
        iteratedDeriv 14 completedNativeOperatorCharacteristic 0 /
          (completedNativeXiCosineMoment 0 : ℂ) := by
  obtain ⟨_, q1, _, q3, _, q5, _, q7⟩ := nativeSourceLogSlope_center_jets
  have q9 := nativeSourceLogSlope_ninth_derivative_eq_integralRatio
  have q11 := nativeSourceLogSlope_eleventh_derivative_eq_integralRatio
  have h := nativeSourceLogSlope_derivative_recurrence 13
  have hf0 : completedNativeOperatorCharacteristic 0 =
      (completedNativeXiCosineMoment 0 : ℂ) := by
    have he := XiThetaCosine.completedNative_eq_xiCosineKernel 0
    have haxis : completedNativeOperatorCharacteristic 0 =
        (completedNativeXiCosineTransformReal 0 : ℂ) := by
      simpa [completedNativeXiCosineTransformReal] using he
    rw [haxis, completedNativeXiCosineTransformReal_zero]
  have hf1 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 0
  have hf3 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 1
  have hf5 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 2
  have hf7 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 3
  have hf9 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 4
  have hf11 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 5
  have hf13 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 6
  norm_num [Finset.sum_range_succ, Nat.choose, hf0, hf1, hf3, hf5, hf7, hf9, hf11, hf13,
    iteratedDeriv_two_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_four_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_six_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_eight_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_ten_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_twelve_completedNativeOperatorCharacteristic_zero] at h
  simp only [iteratedDeriv_one] at q1
  rw [q1, q3, q5, q7, q9, q11] at h
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  unfold nativeSourceThirteenthNumerator
  unfold nativeSourceNinthNumerator nativeSourceEleventhNumerator at h
  push_cast at h ⊢
  field_simp [ha] at h ⊢
  linear_combination h

/-- Exact real coefficient. This records the missing raw source coordinate;
no canonical sequence or downstream positivity enters its derivation. -/
theorem nativeSourceOddBoundaryCoefficient_six_rawCharacteristicJet_formula :
    nativeSourceOddBoundaryCoefficient 6 =
      nativeSourceThirteenthNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6)
        (-(iteratedDeriv 14 completedNativeOperatorCharacteristic 0).re) /
        (6227020800 * completedNativeXiCosineMoment 0^7) := by
  norm_num only [nativeSourceOddBoundaryCoefficient, Nat.reduceMul, Nat.reduceAdd, Nat.factorial]
  rw [nativeSourceLogSlope_thirteenth_derivative_eq_rawCharacteristicJet]
  rw [← Complex.ofReal_pow, Complex.sub_re, Complex.div_ofReal_re,
    Complex.div_ofReal_re, Complex.ofReal_re]
  unfold nativeSourceThirteenthNumerator
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring


/-- The last source coordinate is now the original raw cosine integral;
its positivity as an integral does NOT imply positivity of the connected form. -/
theorem nativeSourceLogSlope_thirteenth_derivative_eq_integralRatio :
    iteratedDeriv 13 completedNativeOperatorLogDerivative 0 =
      (nativeSourceThirteenthNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) /
          completedNativeXiCosineMoment 0^7 : ℝ) := by
  rw [nativeSourceLogSlope_thirteenth_derivative_eq_rawCharacteristicJet,
    iteratedDeriv_fourteen_completedNativeOperatorCharacteristic_zero]
  unfold nativeSourceThirteenthNumerator
  push_cast
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  field_simp [ha]
  ring

/-- Seventh source coefficient, derived solely from the division-free recurrence
and raw cosine integrals, with NO canonical moment identification. -/
theorem nativeSourceOddBoundaryCoefficient_six_integral_formula :
    nativeSourceOddBoundaryCoefficient 6 =
      nativeSourceThirteenthNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) /
        (6227020800 * completedNativeXiCosineMoment 0^7) := by
  rw [nativeSourceOddBoundaryCoefficient_six_rawCharacteristicJet_formula,
    iteratedDeriv_fourteen_completedNativeOperatorCharacteristic_zero]
  simp

/-- Exact reality and factorial normalization, before any moment comparison. -/
theorem nativeSourceOddBoundaryCoefficient_six_cast_jet :
    iteratedDeriv 13 completedNativeOperatorLogDerivative 0 =
      6227020800 * (nativeSourceOddBoundaryCoefficient 6 : ℂ) := by
  rw [nativeSourceOddBoundaryCoefficient_six_integral_formula,
    nativeSourceLogSlope_thirteenth_derivative_eq_integralRatio]
  push_cast
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  field_simp [ha]

/-- The preceding even source jet vanishes by parity in the ORIGINAL recurrence. -/
theorem nativeSourceLogSlope_twelfth_derivative_eq_zero :
    iteratedDeriv 12 completedNativeOperatorLogDerivative 0 = 0 := by
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  have q8 := nativeSourceLogSlope_eighth_derivative_eq_zero
  have q10 := nativeSourceLogSlope_tenth_derivative_eq_zero
  have h := nativeSourceLogSlope_derivative_recurrence 12
  have hf1 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 0
  have hf3 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 1
  have hf5 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 2
  have hf7 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 3
  have hf9 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 4
  have hf11 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 5
  have hf13 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 6
  norm_num [Finset.sum_range_succ, Nat.choose, q0, q2, q4, q6, q8, q10,
    hf1, hf3, hf5, hf7, hf9, hf11, hf13] at h
  exact h.resolve_right completedNativeOperatorCharacteristic_zero_ne_zero

/-- Exact seventh-order odd transverse expansion of the actual source. All
higher orders remain in one analytic fourteenth-order remainder. -/
theorem nativeSourceTransverseSlope_seven_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h) =
        (∑ j ∈ Finset.range 7, (-1 : ℂ)^j *
          (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) + h^14*R h := by
  obtain ⟨G, hGa, hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 14
  let R : ℂ → ℂ := fun h => Complex.I * G (Complex.I*h)
  have hGc : AnalyticAt ℂ (fun h => G (Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R, (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Complex.I) 0).fun_mul hGc, ?_⟩
  have ht : Filter.Tendsto (fun h : ℂ => Complex.I*h) (nhds 0) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      (Filter.tendsto_id : Filter.Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul Complex.I
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  obtain ⟨q1, q3, q5, q7⟩ := nativeSourceOddBoundaryCoefficient_cast_jets
  have q8 := nativeSourceLogSlope_eighth_derivative_eq_zero
  have q9 := nativeSourceOddBoundaryCoefficient_four_cast_jet
  have q10 := nativeSourceLogSlope_tenth_derivative_eq_zero
  have q11 := nativeSourceOddBoundaryCoefficient_five_cast_jet
  have q12 := nativeSourceLogSlope_twelfth_derivative_eq_zero
  have q13 := nativeSourceOddBoundaryCoefficient_six_cast_jet
  filter_upwards [ht.eventually hG] with h hh
  rw [hh]
  dsimp only [R]
  norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, smul_eq_mul]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end
end CarrySelfAdjointOperator
