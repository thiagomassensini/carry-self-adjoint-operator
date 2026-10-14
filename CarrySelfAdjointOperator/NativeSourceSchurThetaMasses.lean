import CarrySelfAdjointOperator.NativeSourceSchurThetaIntegral

/-! Exact positive and negative masses of the original theta density.
Every odd Schur polynomial has a strictly nonzero negative mass. This is
compatible with a positive total integral; the first odd case proves both. -/
namespace CarrySelfAdjointOperator
open scoped BigOperators
open Polynomial MeasureTheory Set Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def nativeThetaPositiveMass (P : ℝ[X]) : ℝ :=
  ∫ u in Ioi (0 : ℝ), max (P.eval u * completedNativeXiCosineKernel u) 0

def nativeThetaNegativeMass (P : ℝ[X]) : ℝ :=
  ∫ u in Ioi (0 : ℝ), max (-(P.eval u * completedNativeXiCosineKernel u)) 0

theorem nativeThetaPositiveMass_nonneg (P : ℝ[X]) : 0 ≤ nativeThetaPositiveMass P :=
  integral_nonneg (fun _ => le_max_right _ _)

theorem nativeThetaNegativeMass_nonneg (P : ℝ[X]) : 0 ≤ nativeThetaNegativeMass P :=
  integral_nonneg (fun _ => le_max_right _ _)

theorem nativeXiPolynomialIntegral_eq_masses (P : ℝ[X]) :
    nativeXiPolynomialIntegral P = nativeThetaPositiveMass P - nativeThetaNegativeMass P := by
  have hf := integrableOn_polynomial_mul_nativeXiKernel P
  change (∫ u in Ioi (0 : ℝ), P.eval u * completedNativeXiCosineKernel u) = _
  unfold nativeThetaPositiveMass nativeThetaNegativeMass
  rw [← integral_sub hf.pos_part hf.neg_part]
  apply integral_congr_ae
  filter_upwards [] with u
  let a := P.eval u * completedNativeXiCosineKernel u
  change a = max a 0 - max (-a) 0
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    ring
  · have hn : a < 0 := lt_of_not_ge ha
    rw [max_eq_right hn.le, max_eq_left (neg_pos.mpr hn).le]
    ring

/-- This negative contribution is genuinely present at every odd order;
it cannot be removed by a claim of pointwise positivity. -/
theorem nativeSchurThetaPolynomial_odd_negativeMass_pos (n : ℕ) :
    0 < nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 n) := by
  let P := nativeSchurThetaPolynomial 1 n
  let f : ℝ → ℝ := fun u => max (-(P.eval u * completedNativeXiCosineKernel u)) 0
  have hf : Integrable f (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_polynomial_mul_nativeXiKernel P).neg_part
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (nativeSchurThetaPolynomial_odd_density_eventually_neg n)
  have hsupport : Ioi (max M 0) ⊆ Function.support f := by
    intro u hu
    have hneg := hM u (le_trans (le_max_left _ _) hu.le)
    have hpos : 0 < f u := by
      dsimp [f, P]
      exact (neg_pos.mpr hneg).trans_le (le_max_left _ _)
    exact hpos.ne'
  have hmeasure : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi (max M 0)) := by
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  change 0 < ∫ u, f u ∂volume.restrict (Ioi (0 : ℝ))
  exact (integral_pos_iff_support_of_nonneg (fun _ => le_max_right _ _) hf).mpr
    (hmeasure.trans_le (measure_mono hsupport))

theorem nativeSourceSchurRemainder_eq_thetaMasses (s n : ℕ) :
    nativeSourceSchurRemainder s n =
      nativeThetaPositiveMass (nativeSchurThetaPolynomial s n) -
        nativeThetaNegativeMass (nativeSchurThetaPolynomial s n) := by
  rw [← nativeSchurThetaPolynomial_integral s n, nativeXiPolynomialIntegral_eq_masses]

/-- A concrete source-facing sign target; the domination is not asserted. -/
theorem nativeSourceSchurRemainder_pos_iff_thetaMassDominance (s n : ℕ) :
    0 < nativeSourceSchurRemainder s n ↔
      nativeThetaNegativeMass (nativeSchurThetaPolynomial s n) <
        nativeThetaPositiveMass (nativeSchurThetaPolynomial s n) := by
  rw [nativeSourceSchurRemainder_eq_thetaMasses s n, sub_pos]

/-- The original all-order strict sign is exactly domination of these
explicit source masses. Their existence does not prove the domination. -/
theorem nativeSourceBoundary_all_pos_iff_thetaMassDominance :
    (∀ n : ℕ, 1 ≤ n → ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) ↔
      ∀ n, (nativeThetaNegativeMass (nativeSchurThetaPolynomial 0 n) <
        nativeThetaPositiveMass (nativeSchurThetaPolynomial 0 n)) ∧
        (nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 n) <
          nativeThetaPositiveMass (nativeSchurThetaPolynomial 1 n)) := by
  rw [nativeSourceBoundary_all_pos_iff_sourceSchur]
  simp_rw [nativeSourceSchurRemainder_pos_iff_thetaMassDominance]

/-- The existing strict theta-kurtosis result makes the first odd remainder
positive even though its new negative mass is strictly positive. -/
theorem nativeSourceSchurRemainder_first_odd_pos : 0 < nativeSourceSchurRemainder 1 0 := by
  have hm := nativeSourceMixedLeadingCoefficients_pos.2
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at hm
  have h0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  rw [nativeSourceSchurRemainder_eq]
  have he : sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 0 =
      canonicalCompletedNativeLogDerivativeMoment 1 := by
    simp [sourceMomentSchur, dotProduct]
  rw [he]
  exact mul_pos h0 (by linarith)

theorem nativeThetaMasses_first_odd :
    0 < nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 0) ∧
      nativeThetaNegativeMass (nativeSchurThetaPolynomial 1 0) <
        nativeThetaPositiveMass (nativeSchurThetaPolynomial 1 0) := by
  refine ⟨nativeSchurThetaPolynomial_odd_negativeMass_pos 0, ?_⟩
  exact (nativeSourceSchurRemainder_pos_iff_thetaMassDominance 1 0).mp
    nativeSourceSchurRemainder_first_odd_pos

end
end CarrySelfAdjointOperator
