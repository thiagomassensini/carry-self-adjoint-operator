import CarrySelfAdjointOperator.CompletedNativeChiralReturnNinthSourceJet

/-!
# Eleventh source jet and the exact twelfth-order remainder

The source is the unchanged completed -F'/F. The new coefficient follows
from its division-free recurrence and the same raw cosine integrals.
Every finite Cauchy coordinate and the entire analytic remainder are
synthesized before any mixed readout. No sign is asserted here.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Connected raw source numerator fixed by eleven differentiations. -/
def nativeSourceEleventhNumerator (a b c d e f g : ℝ) : ℝ :=
  -a^5*g + 66*a^4*b*f + 495*a^4*c*e + 462*a^4*d^2 -
    2970*a^3*b^2*e - 27720*a^3*b*c*d - 11550*a^3*c^3 +
    83160*a^2*b^3*d + 311850*a^2*b^2*c^2 -
    1247400*a*b^4*c + 1247400*b^6

/-- The tenth source derivative vanishes by the source product recurrence. -/
theorem nativeSourceLogSlope_tenth_derivative_eq_zero :
    iteratedDeriv 10 completedNativeOperatorLogDerivative 0 = 0 := by
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  have q8 := nativeSourceLogSlope_eighth_derivative_eq_zero
  have h := nativeSourceLogSlope_derivative_recurrence 10
  have hf1 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 0
  have hf3 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 1
  have hf5 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 2
  have hf7 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 3
  have hf9 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 4
  have hf11 := iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero 5
  norm_num [Finset.sum_range_succ, Nat.choose, q0, q2, q4, q6, q8,
    hf1, hf3, hf5, hf7, hf9, hf11] at h
  exact h.resolve_right completedNativeOperatorCharacteristic_zero_ne_zero

/-- Exact real integral ratio obtained from the original source recurrence,
not by transporting a canonical moment formula. -/
theorem nativeSourceLogSlope_eleventh_derivative_eq_integralRatio :
    iteratedDeriv 11 completedNativeOperatorLogDerivative 0 =
      (nativeSourceEleventhNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) /
          completedNativeXiCosineMoment 0 ^ 6 : ℝ) := by
  obtain ⟨_, q1, _, q3, _, q5, _, q7⟩ := nativeSourceLogSlope_center_jets
  have q9 := nativeSourceLogSlope_ninth_derivative_eq_integralRatio
  have h := nativeSourceLogSlope_derivative_recurrence 11
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
  norm_num [Finset.sum_range_succ, Nat.choose, hf0, hf1, hf3, hf5, hf7, hf9, hf11,
    iteratedDeriv_two_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_four_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_six_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_eight_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_ten_completedNativeOperatorCharacteristic_zero,
    iteratedDeriv_twelve_completedNativeOperatorCharacteristic_zero] at h
  simp only [iteratedDeriv_one] at q1
  rw [q1, q3, q5, q7, q9] at h
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  unfold nativeSourceEleventhNumerator
  unfold nativeSourceNinthNumerator at h
  push_cast at h ⊢
  field_simp [ha] at h ⊢
  linear_combination h

/-- Sixth odd coefficient before moment identification; no sign asserted. -/
theorem nativeSourceOddBoundaryCoefficient_five_integral_formula :
    nativeSourceOddBoundaryCoefficient 5 =
      nativeSourceEleventhNumerator
        (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
        (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
        (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
        (completedNativeXiCosineMoment 6) /
        (39916800 * completedNativeXiCosineMoment 0 ^ 6) := by
  norm_num only [nativeSourceOddBoundaryCoefficient, Nat.reduceMul,
    Nat.reduceAdd, Nat.factorial]
  rw [nativeSourceLogSlope_eleventh_derivative_eq_integralRatio, Complex.ofReal_re]
  ring

/-- Realness and factorial normalization of the new odd source jet. -/
theorem nativeSourceOddBoundaryCoefficient_five_cast_jet :
    iteratedDeriv 11 completedNativeOperatorLogDerivative 0 =
      39916800 * (nativeSourceOddBoundaryCoefficient 5 : ℂ) := by
  rw [nativeSourceOddBoundaryCoefficient_five_integral_formula,
    nativeSourceLogSlope_eleventh_derivative_eq_integralRatio]
  push_cast
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  field_simp [ha]

/-- Exact sixth-order odd transverse expansion of the actual source. All
higher orders remain in one analytic twelfth-order remainder. -/
theorem nativeSourceTransverseSlope_six_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h) =
        (∑ j ∈ Finset.range 6, (-1 : ℂ)^j *
          (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) + h^12*R h := by
  obtain ⟨G, hGa, hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 12
  let R : ℂ → ℂ := fun h => -Complex.I * G (Complex.I*h)
  have hGc : AnalyticAt ℂ (fun h => G (Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R, (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) 0).fun_mul hGc, ?_⟩
  have ht : Filter.Tendsto (fun h : ℂ => Complex.I*h) (nhds 0) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      (Filter.tendsto_id : Filter.Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul Complex.I
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  obtain ⟨q1, q3, q5, q7⟩ := nativeSourceOddBoundaryCoefficient_cast_jets
  have q8 := nativeSourceLogSlope_eighth_derivative_eq_zero
  have q9 := nativeSourceOddBoundaryCoefficient_four_cast_jet
  have q10 := nativeSourceLogSlope_tenth_derivative_eq_zero
  have q11 := nativeSourceOddBoundaryCoefficient_five_cast_jet
  filter_upwards [ht.eventually hG] with h hh
  rw [hh]
  dsimp only [R]
  norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, smul_eq_mul]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]
  ring


open ChiralReturn

/-- Sixth odd Taylor prefix plus its ENTIRE remainder at the unchanged
radial source node. The analytic source supplies R in the theorem below. -/
def radialSixthOddSourceTemplate (R : ℂ → ℂ) (h : ℂ) (i : ℕ) : ℂ :=
  (∑ j ∈ Finset.range 6, (-1 : ℂ)^j * (nativeSourceOddBoundaryCoefficient j : ℂ) *
    h^(2*j+1) * (((i+1 : ℕ) : ℂ)^(2*j+1))) +
  h^12 * ((i+1 : ℕ) : ℂ)^12 * R (((i+1 : ℕ) : ℂ)*h)

/-- Exact vector synthesis BEFORE any scalar mixed readout; every source
remainder coefficient and every finite Cauchy coordinate is retained. -/
theorem radialSixthOddSourceTemplate_synthesis (k N : ℕ) (R : ℂ → ℂ)
    (h : ℂ) (d : Fin N → ℂ) :
    radialIncidentSynthesis k N (fun i => d i * radialSixthOddSourceTemplate R h i) =
      (∑ j ∈ Finset.range 6,
        ((-1 : ℂ)^j * (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) •
          radialEulerPowerSynthesis k N (2*j+1) d) +
      radialIncidentSynthesis k N (fun i => d i *
        (h^12 * (((i : ℕ)+1 : ℕ) : ℂ)^12 * R (((((i : ℕ)+1 : ℕ) : ℂ))*h))) := by
  have he : (fun i : Fin N => d i * radialSixthOddSourceTemplate R h i) =
      (∑ j ∈ Finset.range 6,
        ((-1 : ℂ)^j * (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) •
          (fun i => d i * ((((i : ℕ)+1 : ℕ) : ℂ)^(2*j+1)))) +
      (fun i => d i * (h^12 * (((i : ℕ)+1 : ℕ) : ℂ)^12 *
        R (((((i : ℕ)+1 : ℕ) : ℂ))*h))) := by
    funext i
    simp only [radialSixthOddSourceTemplate, Finset.sum_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rfl

/-- At every FIXED finite cutoff, one threshold makes the exact vector
Taylor sewing valid simultaneously at all original radial source nodes.
No sign of the prefix or remainder is inferred. -/
theorem radialSixthOddSourceTemplate_eventually_eq_slopes (N : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin N, radialCompletedSlope k i =
        radialSixthOddSourceTemplate R (canonicalGreenJetStep k) i := by
  obtain ⟨R, hRa, hR⟩ := nativeSourceTransverseSlope_six_exact_remainder
  refine ⟨R, hRa, ?_⟩
  have ht (i : Fin N) : Tendsto
      (fun k : ℕ => (((i : ℕ)+1 : ℕ) : ℂ) * canonicalGreenJetStep k) atTop (nhds 0) := by
    simpa only [mul_zero] using canonicalGreenJetStep_tendsto_zero.const_mul
      ((((i : ℕ)+1 : ℕ) : ℂ))
  have hs := Filter.eventually_all.mpr (fun i : Fin N => (ht i).eventually hR)
  filter_upwards [hs] with k hk
  intro i
  calc
    radialCompletedSlope k i = -Complex.I * completedNativeOperatorLogDerivative
        (Complex.I * ((((i : ℕ)+1 : ℕ) : ℂ) * canonicalGreenJetStep k)) := by
      unfold radialCompletedSlope canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
      congr 1
      congr 1
      ring
    _ = _ := hk i
    _ = radialSixthOddSourceTemplate R (canonicalGreenJetStep k) i := by
      unfold radialSixthOddSourceTemplate
      rw [mul_pow]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        ring
      · ring

end
end CarrySelfAdjointOperator
