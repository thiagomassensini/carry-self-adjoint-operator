import CarrySelfAdjointOperator.NativeCompletedDividedVectorResponse

/-! Strong convergence of a response constructed from the original vector
Taylor tower. No scalar moment is used as an input vector or coefficient.
The finite prefixes keep both variables and every divided-power crossing. -/
namespace CarrySelfAdjointOperator.DividedVectorResponse
open Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem series_coeff_eq_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {series : FormalMultilinearSeries ℂ ℂ E}
    (hs : HasFPowerSeriesAt f series 0) (n : ℕ) :
    series.coeff n = completedGreenTaylorJet f n := by
  rcases hs with ⟨radius, hball⟩
  have hd := hball.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul] at hd
  have he : (n.factorial : ℂ) • series.coeff n = iteratedDeriv n f 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hd
  rw [completedGreenTaylorJet, ← he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

theorem sourceVector_hasSum :
    ∀ᶠ z in nhds (0 : ℂ),
      HasSum (fun n => z^n • completedGreenTaylorJet sourceVector n) (sourceVector z) := by
  rcases sourceVector_analyticAt_zero with ⟨series, hs⟩
  have h := hasFPowerSeriesAt_iff.mp hs
  filter_upwards [h] with z hz
  simpa only [zero_add, series_coeff_eq_jet hs] using hz

/-- The central-axis expansion converges in the original Hilbert norm,
including the derivative value at zero. -/
theorem response_axis_hasSum :
    ∀ᶠ z in nhds (0 : ℂ),
      HasSum (fun n => z^n • coefficientVector n 0) (response 0 z) := by
  rcases sourceVector_analyticAt_zero with ⟨series, hs⟩
  have h := hasFPowerSeriesAt_iff.mp hs.has_fpower_series_dslope_fslope
  filter_upwards [h] with z hz
  simpa only [zero_add, FormalMultilinearSeries.coeff_fslope,
    series_coeff_eq_jet hs, coefficientVector, Nat.add_zero, response] using hz

/-- A vector prefix of the divided response, rather than a matrix
factorization of target moments. -/
def responsePrefix (N : ℕ) (a z : ℂ) : CompletedPrimeDepthJetCarrier :=
  ∑ n ∈ Finset.range N,
    (∑ p ∈ Finset.range (n+1), a^p*z^(n-p)) • coefficientVector n 0

theorem responsePrefix_ordered_crosses (N : ℕ) (a z : ℂ) :
    responsePrefix N a z =
      ∑ n ∈ Finset.range N, ∑ p ∈ Finset.range (n+1),
        (a^p*z^(n-p)) • coefficientVector p (n-p) := by
  unfold responsePrefix
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have he : p+(n-p) = n := Nat.add_sub_of_le hpn
  simp only [coefficientVector, he, Nat.add_zero]

/-- Exact finite vector equation with both independent variables. -/
theorem responsePrefix_source_equation (N : ℕ) (a z : ℂ) :
    (z-a) • responsePrefix N a z =
      ∑ n ∈ Finset.range N, (z^(n+1)-a^(n+1)) • coefficientVector n 0 := by
  unfold responsePrefix
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_smul]
  have h := Commute.mul_neg_geom_sum₂ (Commute.all a z) (n+1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]

theorem response_axis_prefix_tendsto :
    ∀ᶠ z in nhds (0 : ℂ),
      Tendsto (fun N => responsePrefix N 0 z) atTop (nhds (response 0 z)) := by
  filter_upwards [response_axis_hasSum] with z hz
  have he : (fun N => responsePrefix N 0 z) =
      fun N => ∑ n ∈ Finset.range N, z^n • coefficientVector n 0 := by
    funext N
    unfold responsePrefix
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_eq_single 0]
    · simp
    · intro p _ hp
      simp [zero_pow hp]
    · simp
  rw [he]
  exact hz.tendsto_sum_nat

/-- Convergence at two distinct source points near the center. The central
diagonal is handled separately by the preceding strong axis theorem. -/
theorem responsePrefix_off_diagonal_tendsto :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ a ∈ U, ∀ z ∈ U, z ≠ a →
        Tendsto (fun N => responsePrefix N a z) atTop (nhds (response a z)) := by
  rcases mem_nhds_iff.mp sourceVector_hasSum with ⟨U, hU, hopen, hzero⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro a ha z hz hne
  have shifted (t : ℂ) (ht : t ∈ U) :
      HasSum (fun n => t^(n+1) • coefficientVector n 0)
        (sourceVector t-completedGreenTaylorJet sourceVector 0) := by
    have h := (hasSum_nat_add_iff' 1).mpr (hU ht)
    simpa only [Finset.sum_range_one, pow_zero, one_smul, coefficientVector,
      Nat.add_zero] using h
  have hseries := ((shifted z hz).sub (shifted a ha)).const_smul ((z-a)⁻¹)
  have hterms : (fun n => (z-a)⁻¹ •
      (z^(n+1) • coefficientVector n 0-a^(n+1) • coefficientVector n 0)) =
      fun n => (∑ p ∈ Finset.range (n+1), a^p*z^(n-p)) • coefficientVector n 0 := by
    funext n
    rw [← sub_smul, smul_smul]
    have h := Commute.mul_neg_geom_sum₂ (Commute.all a z) (n+1)
    simp only [Nat.add_sub_cancel] at h
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_mul]
  change HasSum (fun n => (z-a)⁻¹ •
    (z^(n+1) • coefficientVector n 0-a^(n+1) • coefficientVector n 0)) _ at hseries
  rw [hterms] at hseries
  have hvalue : (z-a)⁻¹ •
      ((sourceVector z-completedGreenTaylorJet sourceVector 0)-
        (sourceVector a-completedGreenTaylorJet sourceVector 0)) = response a z := by
    rw [response_off_diagonal a z hne]
    congr 1
    abel
  rw [hvalue] at hseries
  exact hseries.tendsto_sum_nat

end
end CarrySelfAdjointOperator.DividedVectorResponse
