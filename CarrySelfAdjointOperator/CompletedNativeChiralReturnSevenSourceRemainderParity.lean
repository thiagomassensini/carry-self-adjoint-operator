import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenSampleStorage

/-!
# Parity of the actual analytic source remainder

The unchanged division-free source recurrence kills its fourteenth even jet.
Taylor order fifteen then supplies an order-fourteen remainder vanishing at
zero. No moment sequence or positivity premise is used.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem nativeSourceLogSlope_fourteenth_derivative_eq_zero :
    iteratedDeriv 14 completedNativeOperatorLogDerivative 0 = 0 := by
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  have q8 := nativeSourceLogSlope_eighth_derivative_eq_zero
  have q10 := nativeSourceLogSlope_tenth_derivative_eq_zero
  have q12 := nativeSourceLogSlope_twelfth_derivative_eq_zero
  have h := nativeSourceLogSlope_derivative_recurrence 14
  have hf1 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 0
  have hf3 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 1
  have hf5 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 2
  have hf7 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 3
  have hf9 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 4
  have hf11 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 5
  have hf13 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 6
  have hf15 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 7
  norm_num [Finset.sum_range_succ, Nat.choose, q0, q2, q4, q6, q8, q10, q12,
    hf1, hf3, hf5, hf7, hf9, hf11, hf13, hf15] at h
  exact h.resolve_right completedNativeOperatorCharacteristic_zero_ne_zero

/-- The genuine order-fourteen remainder has no constant term. -/
theorem nativeSourceTransverseSlope_seven_exact_remainder_zero :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0 = 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h) =
        (∑ j ∈ Finset.range 7, (-1 : ℂ)^j *
          (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) + h^14*R h := by
  obtain ⟨G, hGa, hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 15
  let R : ℂ → ℂ := fun h => -h * G (Complex.I*h)
  have hGc : AnalyticAt ℂ (fun h => G (Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R, (analyticAt_id.neg.fun_mul hGc), (by simp [R]), ?_⟩
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
  have q14 := nativeSourceLogSlope_fourteenth_derivative_eq_zero
  filter_upwards [ht.eventually hG] with h hh
  rw [hh]
  dsimp only [R]
  norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11,
    q12, q13, q14, smul_eq_mul]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- Reuse the existing completed source expansion, without canonical moments. -/
theorem radialSevenOddSourceTemplate_eventually_eq_slopes_zero :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0 = 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin 7, radialCompletedSlope k i =
        radialSevenOddSourceTemplate R (radialFourSourceStep k) i := by
  obtain ⟨R, hRa, hR0, hR⟩ := nativeSourceTransverseSlope_seven_exact_remainder_zero
  refine ⟨R, hRa, hR0, ?_⟩
  have ht (i : Fin 7) : Tendsto
      (fun k : ℕ => (((i+1 : ℕ) : ℂ)*(radialFourSourceStep k : ℂ))) atTop (nhds 0) := by
    simpa only [mul_zero, canonicalGreenJetStep_eq_radialFourSourceStep] using canonicalGreenJetStep_tendsto_zero.const_mul
      (((i+1 : ℕ) : ℂ))
  filter_upwards [Filter.eventually_all.mpr (fun i : Fin 7 => (ht i).eventually hR)] with k hk
  intro i
  calc
    radialCompletedSlope k i = -Complex.I * completedNativeOperatorLogDerivative
        (Complex.I*(((i+1 : ℕ) : ℂ)*(radialFourSourceStep k : ℂ))) := by
      unfold radialCompletedSlope canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
      rw [canonicalGreenJetStep_eq_radialFourSourceStep]
      congr 1
      congr 1
      ring
    _ = radialSevenOddSourceTemplate R (radialFourSourceStep k) i := by
      rw [hk i]
      unfold radialSevenOddSourceTemplate
      push_cast
      simp_rw [mul_pow]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · ring


end
end CarrySelfAdjointOperator
