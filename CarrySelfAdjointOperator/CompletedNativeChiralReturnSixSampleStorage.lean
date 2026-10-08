import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixSampleRegularization
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourSampleStorage

/-!
# Full six-sample source storage

The exact analytic source remainder is synthesized together with its own
odd prefix in the unchanged Cauchy carrier before the mixed readout.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Exact Taylor template at the same six source nodes. R will be supplied
only by the existing analytic source theorem, not by a target coefficient. -/
def radialSixSourceTemplate (R : ℂ → ℂ) (h : ℝ) (i : Fin 6) : ℂ :=
  radialSixthOddSourceTemplate R (h : ℂ) i

/-- Full vector synthesis of prefix AND analytic remainder, with no early
compression of the two channels. -/
theorem radialSixSourceTemplate_synthesis (k : ℕ) (h : ℝ) (R : ℂ → ℂ) (d : Fin 6 → ℂ) :
    radialIncidentSynthesis k 6 (fun i => d i * radialSixSourceTemplate R h i) =
      (∑ j ∈ Finset.range 6,
        (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) •
          radialEulerPowerSynthesis k 6 (2*j+1) d) +
      radialIncidentSynthesis k 6 (fun i => d i *
        (((h^12 : ℝ) : ℂ) * (((i : ℕ)+1 : ℕ) : ℂ)^12 *
          R (((((i : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ))) := by
  simpa only [radialSixSourceTemplate, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_one] using radialSixthOddSourceTemplate_synthesis k 6 R (h : ℂ) d

/-- All higher boundary coordinates participate in the exact polynomial
source energy; only at h=0 do they vanish in the regular boundary chart. -/
theorem radialSixSourcePrefix_energy (k : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hkh : ((k : ℝ)+1)*h = 1) (x : Fin 6 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 6 (radialSixNormalizedBoundaryInput h x))
      (∑ j ∈ Finset.range 6,
        (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) •
          radialEulerPowerSynthesis k 6 (2*j+1) (radialSixNormalizedBoundaryInput h x))).re =
      radialSixRegularizedBoundaryEnergy h x := by
  let d := radialSixNormalizedBoundaryInput h x
  have hc (j a : ℕ) (ha : a < 2*j+1) :
      (conj (radialSixRegularizedBoundary h x a) *
        radialSixRegularizedBoundary h x (2*j-a)).re =
      h^(2*j) * (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re := by
    rw [radialSixRegularizedBoundary_eq h hh x a,
      radialSixRegularizedBoundary_eq h hh x (2*j-a)]
    have hp : h^a * h^(2*j-a) = h^(2*j) := by rw [← pow_add]; congr 1; omega
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    change _ = _
    linear_combination
      (radialEulerBoundaryJet d a).re * (radialEulerBoundaryJet d (2*j-a)).re * hp +
      (radialEulerBoundaryJet d a).im * (radialEulerBoundaryJet d (2*j-a)).im * hp
  simp only [inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul,
    radialSixRegularizedBoundaryEnergy]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
      (conj (radialSixRegularizedBoundary h x a) *
        radialSixRegularizedBoundary h x (2*j-a)).re) =
      h^(2*j) * (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc j a (Finset.mem_range.mp ha)]
    ring
  rw [hs]
  have hpow : ((k : ℝ)+1)*h^(2*j+1) = h^(2*j) := by
    rw [pow_succ]
    linear_combination h^(2*j) * hkh
  have hg := radialEulerPower_odd_green_energy k 6 j d
  linear_combination 2 * ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j) * h^(2*j+1) * hg +
    2 * ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j) *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) * hpow

/-- The analytic remainder energy contains every i/j cross of the original
Cauchy synthesis. Its factor h is exact, not a bound assumed on storage. -/
theorem radialSixSourceRemainder_energy (k : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hkh : ((k : ℝ)+1)*h = 1) (R : ℂ → ℂ) (x : Fin 6 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 6 (radialSixNormalizedBoundaryInput h x))
      (radialIncidentSynthesis k 6 (fun i => radialSixNormalizedBoundaryInput h x i *
        (((h^12 : ℝ) : ℂ) * (((i : ℕ)+1 : ℕ) : ℂ)^12 *
          R (((((i : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ))))).re =
      radialSixRegularizedRemainderEnergy R h x := by
  have hg := radialEulerPower_inner k 6 0 0 (radialSixNormalizedBoundaryInput h x)
    (fun i => radialSixNormalizedBoundaryInput h x i *
      (((h^12 : ℝ) : ℂ) * (((i : ℕ)+1 : ℕ) : ℂ)^12 *
        R (((((i : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))
  simp only [radialEulerPowerSynthesis_zero, pow_zero, mul_one] at hg
  rw [hg]
  unfold radialSixRegularizedRemainderEnergy
  have hs : (∑ i : Fin 6, ∑ j : Fin 6,
      conj (radialSixNormalizedBoundaryInput h x i) *
        (radialSixNormalizedBoundaryInput h x j *
          (((h^12 : ℝ) : ℂ) * (((j : ℕ)+1 : ℕ) : ℂ)^12 *
            R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ))) *
          ((((k : ℝ)+1 : ℝ) : ℂ) / (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ))) =
      (h : ℂ) * (∑ i : Fin 6, ∑ j : Fin 6,
        conj (radialSixRegularizedInput h x i) * radialSixRegularizedInput h x j *
          (((j : ℕ)+1 : ℕ) : ℂ)^12 * R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ) /
            (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [radialSixRegularizedInput_eq h hh x i, radialSixRegularizedInput_eq h hh x j]
    have hp : ((k : ℝ)+1)*h^12 = h^11 := by
      have ht := congrArg (fun t : ℝ => t*h^11) hkh
      convert ht using 1 <;> ring
    have hpC := congrArg Complex.ofReal hp
    push_cast at hpC ⊢
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    have he := congrArg (fun t : ℂ =>
      conj (radialSixNormalizedBoundaryInput h x i) * radialSixNormalizedBoundaryInput h x j *
        (((j : ℕ)+1 : ℕ) : ℂ)^12 * R (((((j : ℕ)+1 : ℕ) : ℝ)*h : ℝ) : ℂ) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ) * t) hpC
    push_cast at he
    linear_combination he

  rw [hs, Complex.re_ofReal_mul]
  ring

/-- Exact equality of the full source synthesis/readout and its continuous
boundary chart, under only the geometric radial scale relation. -/
theorem radialSixSourceTemplate_energy (k : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hkh : ((k : ℝ)+1)*h = 1) (R : ℂ → ℂ) (x : Fin 6 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 6 (radialSixNormalizedBoundaryInput h x))
      (radialIncidentSynthesis k 6 (fun i => radialSixNormalizedBoundaryInput h x i *
        radialSixSourceTemplate R h i))).re = radialSixRegularizedStorage R h x := by
  rw [radialSixSourceTemplate_synthesis, inner_add_right, Complex.add_re, mul_add,
    radialSixSourcePrefix_energy k h hh hkh x,
    radialSixSourceRemainder_energy k h hh hkh R x]
  rfl


/-- Reuse the existing sixth odd source expansion and the unchanged radial grid. -/
theorem radialSixSourceTemplate_eventually_eq_slopes :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin 6, radialCompletedSlope k i = radialSixSourceTemplate R (radialFourSourceStep k) i := by
  obtain ⟨R, hRa, hR⟩ := radialSixthOddSourceTemplate_eventually_eq_slopes 6
  refine ⟨R, hRa, ?_⟩
  simpa only [radialSixSourceTemplate, canonicalGreenJetStep_eq_radialFourSourceStep] using hR

/-- The continuous chart reads out the FULL original storage after complete
source synthesis, including every higher source term. -/
theorem storage_one_sixSample_eventually_regularized :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      (storage k (radialCompletedInputCoefficients k
        (radialSixNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re =
          radialSixRegularizedStorage R (radialFourSourceStep k) x := by
  obtain ⟨R, hRa, hR⟩ := radialSixSourceTemplate_eventually_eq_slopes
  refine ⟨R, hRa, ?_⟩
  filter_upwards [hR, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6]
    with k hk hreg
  intro x
  have hh := (radialFourSourceStep_pos k).ne'
  have hkh : ((k : ℝ)+1)*radialFourSourceStep k = 1 := by
    unfold radialFourSourceStep
    exact mul_inv_cancel₀ (by positivity)
  rw [storage_one_eq_complete_slope_pairing k 6 _
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)]
  simp_rw [hk]
  exact radialSixSourceTemplate_energy k _ hh hkh R x

/-- Scalar homogeneity of the inverse boundary chart. -/
theorem radialSixNormalizedBoundaryInput_smul (h : ℝ) (z : ℂ) (x : Fin 6 → ℂ) :
    radialSixNormalizedBoundaryInput h (z • x) = z • radialSixNormalizedBoundaryInput h x := by
  funext i
  simp only [radialSixNormalizedBoundaryInput, radialSixBoundaryReconstruct,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The normalized chart inherits homogeneity from the original full storage,
not from an invented positive form. -/
theorem storage_one_sixSample_normalized_smul (k : ℕ) (h : ℝ) (z : ℂ) (x : Fin 6 → ℂ) :
    (storage k (radialCompletedInputCoefficients k (radialSixNormalizedBoundaryInput h (z • x))) 1).re =
      Complex.normSq z *
        (storage k (radialCompletedInputCoefficients k (radialSixNormalizedBoundaryInput h x)) 1).re := by
  rw [radialSixNormalizedBoundaryInput_smul]
  have hi : radialCompletedInputCoefficients k (z • radialSixNormalizedBoundaryInput h x) =
      z • radialCompletedInputCoefficients k (radialSixNormalizedBoundaryInput h x) := by
    funext i
    simp only [radialCompletedInputCoefficients, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hi, chiralReturnStorage_smul, Complex.re_ofReal_mul]

/-- ONE radial threshold controls EVERY nonzero vector of the FULL Fin 6
coefficient family. All mixed sectors and the analytic remainder are included. -/
theorem storage_one_sixSample_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ d : Fin 6 → ℂ, d ≠ 0 →
      0 < (storage k (radialCompletedInputCoefficients k d) 1).re := by
  obtain ⟨R, hRa, hE⟩ := storage_one_sixSample_eventually_regularized
  have hU := radialFourSourceStep_tendsto_zero.eventually
    (radialSixRegularizedStorage_eventually_pos_on_unit R hRa.continuousAt)
  filter_upwards [hE, hU] with k hk hku
  intro d hd
  let x := radialSixScaledBoundary (radialFourSourceStep k) d
  have hh := (radialFourSourceStep_pos k).ne'
  have hx : x ≠ 0 := by
    intro he
    have hi := radialSixNormalizedBoundaryInput_scaled _ hh d
    rw [show radialSixScaledBoundary (radialFourSourceStep k) d = 0 from he] at hi
    have hz : radialSixNormalizedBoundaryInput (radialFourSourceStep k) 0 = 0 := by
      funext i
      simp [radialSixNormalizedBoundaryInput, radialSixBoundaryReconstruct]
    rw [hz] at hi
    exact hd hi.symm
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let z : ℂ := (‖x‖⁻¹ : ℝ)
  have hu : ‖z • x‖ = 1 := by
    simp [z, norm_smul, Complex.norm_real, norm_inv, inv_mul_cancel₀ hn]
  have hp := hku (z • x) hu
  rw [← hk (z • x), storage_one_sixSample_normalized_smul] at hp
  have hz : 0 < Complex.normSq z := by
    apply Complex.normSq_pos.mpr
    change ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hn
  have hsign := (mul_pos_iff_of_pos_left hz).mp hp
  simpa only [x, radialSixNormalizedBoundaryInput_scaled _ hh d] using hsign

/-- The original chiral coefficient family also has strict full storage,
without a moment positivity certificate. -/
theorem storage_one_original_sixSample_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 6 → ℂ, c ≠ 0 → 0 < (storage k c 1).re := by
  filter_upwards [storage_one_sixSample_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk hreg
  intro c hc
  let d := radialCompletedValueCoefficients k c
  have hi : radialCompletedInputCoefficients k d = c := by
    funext i
    unfold d radialCompletedValueCoefficients radialCompletedInputCoefficients
    field_simp [(hreg i).2.1, (hreg i).2.2]
  have hd : d ≠ 0 := by
    intro he
    have hz : radialCompletedInputCoefficients k (0 : Fin 6 → ℂ) = 0 := by
      funext i
      simp [radialCompletedInputCoefficients]
    rw [he, hz] at hi
    exact hc hi.symm
  simpa only [hi] using hk d hd

/-- Finite contractivity follows for N=6 only. No arbitrary-N claim is made. -/
theorem radialReturnTransfer_six_eventually_norm_le_one :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k 6‖ ≤ 1 := by
  filter_upwards [storage_one_original_sixSample_eventually_pos] with k hk
  apply (radialReturnTransfer_norm_le_one_iff_storage k 6).mpr
  intro c
  by_cases hc : c = 0
  · simp [hc, storage]
  · exact (hk c hc).le


/-- Quantitative uniform closure of the six-sample remainder seam. The
bound uses the existing radial h^a boundary coordinates, without modifying
the metric of the incident source. -/
theorem storage_one_sixSample_eventually_boundary_coercive :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ d : Fin 6 → ℂ,
      ε * (∑ a : Fin 6, Complex.normSq
        (radialSixScaledBoundary (radialFourSourceStep k) d a)) ≤
          (storage k (radialCompletedInputCoefficients k d) 1).re := by
  obtain ⟨R, hRa, hE⟩ := storage_one_sixSample_eventually_regularized
  obtain ⟨ε, he, hU⟩ := radialSixRegularizedStorage_eventually_unit_margin R hRa.continuousAt
  refine ⟨ε/6, div_pos he (by norm_num), ?_⟩
  have hUk := radialFourSourceStep_tendsto_zero.eventually hU
  filter_upwards [hE, hUk] with k hk hku
  intro d
  let x := radialSixScaledBoundary (radialFourSourceStep k) d
  have hh := (radialFourSourceStep_pos k).ne'
  have hfloor : ε * ‖x‖^2 ≤ (storage k (radialCompletedInputCoefficients k d) 1).re := by
    by_cases hd : d = 0
    · have hx : x = 0 := by
        funext a
        simp [x, hd, radialSixScaledBoundary, radialEulerBoundaryJet]
      have hi : radialCompletedInputCoefficients k d = 0 := by
        funext a
        simp [hd, radialCompletedInputCoefficients]
      simp [hx, hi, storage]
    · have hx : x ≠ 0 := by
        intro heq
        have hi := radialSixNormalizedBoundaryInput_scaled _ hh d
        rw [show radialSixScaledBoundary (radialFourSourceStep k) d = 0 from heq] at hi
        have hz : radialSixNormalizedBoundaryInput (radialFourSourceStep k) 0 = 0 := by
          funext i
          simp [radialSixNormalizedBoundaryInput, radialSixBoundaryReconstruct]
        rw [hz] at hi
        exact hd hi.symm
      have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let z : ℂ := (‖x‖⁻¹ : ℝ)
      have hu : ‖z • x‖ = 1 := by
        simp [z, norm_smul, Complex.norm_real, norm_inv, inv_mul_cancel₀ hn]
      have hp := hku (z • x) hu
      rw [← hk (z • x), storage_one_sixSample_normalized_smul] at hp
      have hnz : ‖z‖ = ‖x‖⁻¹ := by simp [z, Complex.norm_real, norm_inv]
      have hz : Complex.normSq z = (‖x‖^2)⁻¹ := by
        rw [Complex.normSq_eq_norm_sq, hnz, inv_pow]
      rw [hz, inv_mul_eq_div] at hp
      have hf := (lt_div_iff₀ (sq_pos_of_ne_zero hn)).mp hp
      simpa only [x, radialSixNormalizedBoundaryInput_scaled _ hh d] using hf.le
  have hsum : (∑ a : Fin 6, Complex.normSq (x a)) ≤ 6 * ‖x‖^2 := by
    calc
      _ = ∑ a : Fin 6, ‖x a‖^2 := by simp only [Complex.normSq_eq_norm_sq]
      _ ≤ ∑ _a : Fin 6, ‖x‖^2 := by
        apply Finset.sum_le_sum
        intro a _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x a) 2
      _ = 6 * ‖x‖^2 := by simp
  calc
    (ε/6) * (∑ a : Fin 6, Complex.normSq (radialSixScaledBoundary (radialFourSourceStep k) d a))
      ≤ (ε/6) * (6*‖x‖^2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ε * ‖x‖^2 := by ring
    _ ≤ _ := hfloor

/-- The same completed source gives finite-combination chiral contractivity
on the six-node radial family, using the existing storage equivalence. -/
theorem chiralMultiplier_six_eventually_contractive :
    ∀ᶠ k : ℕ in atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 6 := by
  filter_upwards [storage_one_original_sixSample_eventually_pos] with k hk
  apply (chiralMultiplierContractiveAt_iff_storage_one_nonnegative k 6).mpr
  intro c
  by_cases hc : c = 0
  · simp [hc, storage]
  · exact (hk c hc).le

end
end CarrySelfAdjointOperator
