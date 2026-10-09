import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryRegularization

/-!
# Complete seven-sample radial storage

The existing source-derived odd Taylor template is synthesized in the original
Cauchy carrier, with its entire analytic remainder. The certified seven-face
margin is then transported uniformly over ALL coefficient directions.
No canonical moment, metric replacement, or discarded cross term is used.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The source's own seven-term odd prefix and its entire remainder. -/
def radialSevenOddSourceTemplate (R : ℂ → ℂ) (h : ℝ) (i : Fin 7) : ℂ :=
  (∑ j ∈ Finset.range 7,
    (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) *
      (((i+1 : ℕ) : ℂ)^(2*j+1))) +
    ((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) *
      R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ))

/-- The two losses remain separate: finite higher boundary coordinates and
complete analytic source remainder. This is the SAME signed readout. -/
def radialSevenRegularizedStorage (R : ℂ → ℂ) (h : ℝ) (x : Fin 7 → ℂ) : ℝ :=
  radialSevenRegularizedBoundaryEnergy h x + radialSevenRegularizedRemainderEnergy R h x

theorem radialSevenRegularizedStorage_zero (R : ℂ → ℂ) (x : Fin 7 → ℂ) :
    radialSevenRegularizedStorage R 0 x = nativeSourceSevenBoundaryEnergy x := by
  simp [radialSevenRegularizedStorage, radialSevenRegularizedBoundaryEnergy_zero,
    radialSevenRegularizedRemainderEnergy]

theorem radialSevenRegularizedStorage_continuousAt (R : ℂ → ℂ)
    (hR : ContinuousAt R 0) (x : Fin 7 → ℂ) :
    ContinuousAt (fun y : ℝ × (Fin 7 → ℂ) => radialSevenRegularizedStorage R y.1 y.2) (0,x) := by
  exact radialSevenRegularizedBoundaryEnergy_continuous.continuousAt.add
    (((continuous_const.mul continuous_fst).continuousAt).mul
      (radialSevenRemainderQuadraticReadout_continuousAt R hR x))

/-- The incoming source is split only AFTER its complete vector synthesis. -/
theorem radialSevenOddSourceTemplate_synthesis (k : ℕ) (h : ℝ) (R : ℂ → ℂ) (d : Fin 7 → ℂ) :
    radialIncidentSynthesis k 7 (fun i => d i * radialSevenOddSourceTemplate R h i) =
      (∑ j ∈ Finset.range 7,
        (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) •
          radialEulerPowerSynthesis k 7 (2*j+1) d) +
      radialIncidentSynthesis k 7 (fun i => d i *
        (((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) *
          R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))) := by
  have he : (fun i => d i * radialSevenOddSourceTemplate R h i) =
      (∑ j ∈ Finset.range 7,
        (((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j * h^(2*j+1) : ℝ) : ℂ) •
          (fun i : Fin 7 => d i * (((i+1 : ℕ) : ℂ)^(2*j+1)))) +
      (fun i => d i * (((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) *
          R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))) := by
    funext i
    simp only [radialSevenOddSourceTemplate, Finset.sum_apply, Pi.add_apply,
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

theorem radialSevenOddSourceTemplate_energy (k : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hkh : ((k : ℝ)+1)*h = 1) (R : ℂ → ℂ) (x : Fin 7 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 7 (radialSevenNormalizedBoundaryInput h x))
      (radialIncidentSynthesis k 7 (fun i => radialSevenNormalizedBoundaryInput h x i *
        radialSevenOddSourceTemplate R h i))).re = radialSevenRegularizedStorage R h x := by
  rw [radialSevenOddSourceTemplate_synthesis, inner_add_right, Complex.add_re, mul_add,
    radialSevenSourcePrefix_energy k h hh hkh x,
    radialSevenSourceRemainder_energy k h hh hkh R x]
  rfl

/-- Reuse the existing completed source expansion, without canonical moments. -/
theorem radialSevenOddSourceTemplate_eventually_eq_slopes :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin 7, radialCompletedSlope k i =
        radialSevenOddSourceTemplate R (radialFourSourceStep k) i := by
  obtain ⟨R, hRa, hR⟩ := nativeSourceTransverseSlope_seven_exact_remainder
  refine ⟨R, hRa, ?_⟩
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

/-- Exact full original storage after completed value/companion synthesis. -/
theorem storage_one_sevenSample_eventually_regularized :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 7 → ℂ,
      (storage k (radialCompletedInputCoefficients k
        (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re =
          radialSevenRegularizedStorage R (radialFourSourceStep k) x := by
  obtain ⟨R, hRa, hR⟩ := radialSevenOddSourceTemplate_eventually_eq_slopes
  refine ⟨R, hRa, ?_⟩
  filter_upwards [hR, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7]
    with k hk hreg
  intro x
  have hh := (radialFourSourceStep_pos k).ne'
  have hkh : ((k : ℝ)+1)*radialFourSourceStep k = 1 := by
    unfold radialFourSourceStep
    exact mul_inv_cancel₀ (by positivity)
  rw [storage_one_eq_complete_slope_pairing k 7 _
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)]
  simp_rw [hk]
  exact radialSevenOddSourceTemplate_energy k _ hh hkh R x

/-- A chosen certified boundary margin retains half its value uniformly.
The threshold controls ALL directions; it is not chosen after the vector. -/
theorem radialSevenRegularizedStorage_eventually_unit_margin
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ x : Fin 7 → ℂ, ε*‖x‖^2 ≤ nativeSourceSevenBoundaryEnergy x) :
    ∀ᶠ h : ℝ in nhds 0, ∀ x : Fin 7 → ℂ, ‖x‖ = 1 →
      ε/2 < radialSevenRegularizedStorage R h x := by
  let K : Set (Fin 7 → ℂ) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hl : ∀ x ∈ K, ∀ᶠ y : ℝ × (Fin 7 → ℂ) in nhds (0,x),
      ε/2 < radialSevenRegularizedStorage R y.1 y.2 := by
    intro x hx
    have hnx : ‖x‖ = 1 := by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx
    have hp : ε/2 < radialSevenRegularizedStorage R 0 x := by
      rw [radialSevenRegularizedStorage_zero]
      have hm := hb x
      rw [hnx] at hm
      norm_num at hm
      linarith
    exact Filter.Tendsto.eventually_lt tendsto_const_nhds
      (radialSevenRegularizedStorage_continuousAt R hR x).tendsto hp
  have hu := hK.eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun h x => ε/2 < radialSevenRegularizedStorage R h x) hl
  filter_upwards [hu] with h hh
  intro x hx
  exact hh x (by simpa only [K, Metric.mem_sphere, dist_zero_right] using hx)

/-- Scalar homogeneity of the inverse boundary chart. -/
theorem radialSevenNormalizedBoundaryInput_smul (h : ℝ) (z : ℂ) (x : Fin 7 → ℂ) :
    radialSevenNormalizedBoundaryInput h (z • x) = z • radialSevenNormalizedBoundaryInput h x := by
  funext i
  simp only [radialSevenNormalizedBoundaryInput, radialSevenBoundaryReconstruct,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The normalized chart inherits homogeneity from the original full storage,
not from an invented positive form. -/
theorem storage_one_sevenSample_normalized_smul (k : ℕ) (h : ℝ) (z : ℂ) (x : Fin 7 → ℂ) :
    (storage k (radialCompletedInputCoefficients k (radialSevenNormalizedBoundaryInput h (z • x))) 1).re =
      Complex.normSq z *
        (storage k (radialCompletedInputCoefficients k (radialSevenNormalizedBoundaryInput h x)) 1).re := by
  rw [radialSevenNormalizedBoundaryInput_smul]
  have hi : radialCompletedInputCoefficients k (z • radialSevenNormalizedBoundaryInput h x) =
      z • radialCompletedInputCoefficients k (radialSevenNormalizedBoundaryInput h x) := by
    funext i
    simp only [radialCompletedInputCoefficients, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hi, chiralReturnStorage_smul, Complex.re_ofReal_mul]

/-- ONE radial threshold controls EVERY nonzero vector of the FULL Fin 7
coefficient family. All mixed sectors and the analytic remainder are included. -/
theorem storage_one_sevenSample_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ d : Fin 7 → ℂ, d ≠ 0 →
      0 < (storage k (radialCompletedInputCoefficients k d) 1).re := by
  obtain ⟨R, hRa, hE⟩ := storage_one_sevenSample_eventually_regularized
  obtain ⟨ε, hε, hb⟩ := nativeSourceSevenBoundaryEnergy_uniform_margin
  have hU := radialFourSourceStep_tendsto_zero.eventually
    (radialSevenRegularizedStorage_eventually_unit_margin R hRa.continuousAt ε hε hb)
  filter_upwards [hE, hU] with k hk hku
  intro d hd
  let x := radialSevenScaledBoundary (radialFourSourceStep k) d
  have hh := (radialFourSourceStep_pos k).ne'
  have hx : x ≠ 0 := by
    intro he
    have hi := radialSevenNormalizedBoundaryInput_scaled _ hh d
    rw [show radialSevenScaledBoundary (radialFourSourceStep k) d = 0 from he] at hi
    have hz : radialSevenNormalizedBoundaryInput (radialFourSourceStep k) 0 = 0 := by
      funext i
      simp [radialSevenNormalizedBoundaryInput, radialSevenBoundaryReconstruct]
    rw [hz] at hi
    exact hd hi.symm
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let z : ℂ := (‖x‖⁻¹ : ℝ)
  have hu : ‖z • x‖ = 1 := by
    simp [z, norm_smul, Complex.norm_real, norm_inv, inv_mul_cancel₀ hn]
  have hp := (lt_trans (div_pos hε (by norm_num)) (hku (z • x) hu))
  rw [← hk (z • x), storage_one_sevenSample_normalized_smul] at hp
  have hz : 0 < Complex.normSq z := by
    apply Complex.normSq_pos.mpr
    change ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero hn
  have hsign := (mul_pos_iff_of_pos_left hz).mp hp
  simpa only [x, radialSevenNormalizedBoundaryInput_scaled _ hh d] using hsign

/-- The original chiral coefficient family also has strict full storage,
without a moment positivity certificate. -/
theorem storage_one_original_sevenSample_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 7 → ℂ, c ≠ 0 → 0 < (storage k c 1).re := by
  filter_upwards [storage_one_sevenSample_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7] with k hk hreg
  intro c hc
  let d := radialCompletedValueCoefficients k c
  have hi : radialCompletedInputCoefficients k d = c := by
    funext i
    unfold d radialCompletedValueCoefficients radialCompletedInputCoefficients
    field_simp [(hreg i).2.1, (hreg i).2.2]
  have hd : d ≠ 0 := by
    intro he
    have hz : radialCompletedInputCoefficients k (0 : Fin 7 → ℂ) = 0 := by
      funext i
      simp [radialCompletedInputCoefficients]
    rw [he, hz] at hi
    exact hc hi.symm
  simpa only [hi] using hk d hd

/-- Finite contractivity follows for N=7 only. No arbitrary-N claim is made. -/
theorem radialReturnTransfer_seven_eventually_norm_le_one :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k 7‖ ≤ 1 := by
  filter_upwards [storage_one_original_sevenSample_eventually_pos] with k hk
  apply (radialReturnTransfer_norm_le_one_iff_storage k 7).mpr
  intro c
  by_cases hc : c = 0
  · simp [hc, storage]
  · exact (hk c hc).le


/-- Quantitative uniform closure of the seven-sample remainder seam. The
bound uses the existing radial h^a boundary coordinates, without modifying
the metric of the incident source. -/
theorem storage_one_sevenSample_eventually_boundary_coercive :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ d : Fin 7 → ℂ,
      ε * (∑ a : Fin 7, Complex.normSq
        (radialSevenScaledBoundary (radialFourSourceStep k) d a)) ≤
          (storage k (radialCompletedInputCoefficients k d) 1).re := by
  obtain ⟨R, hRa, hE⟩ := storage_one_sevenSample_eventually_regularized
  obtain ⟨ε₀, he₀, hb⟩ := nativeSourceSevenBoundaryEnergy_uniform_margin
  let ε := ε₀/2
  have he : 0 < ε := div_pos he₀ (by norm_num)
  have hU := radialSevenRegularizedStorage_eventually_unit_margin R hRa.continuousAt ε₀ he₀ hb
  refine ⟨ε/7, div_pos he (by norm_num), ?_⟩
  have hUk := radialFourSourceStep_tendsto_zero.eventually hU
  filter_upwards [hE, hUk] with k hk hku
  intro d
  let x := radialSevenScaledBoundary (radialFourSourceStep k) d
  have hh := (radialFourSourceStep_pos k).ne'
  have hfloor : ε * ‖x‖^2 ≤ (storage k (radialCompletedInputCoefficients k d) 1).re := by
    by_cases hd : d = 0
    · have hx : x = 0 := by
        funext a
        simp [x, hd, radialSevenScaledBoundary, radialEulerBoundaryJet]
      have hi : radialCompletedInputCoefficients k d = 0 := by
        funext a
        simp [hd, radialCompletedInputCoefficients]
      simp [hx, hi, storage]
    · have hx : x ≠ 0 := by
        intro heq
        have hi := radialSevenNormalizedBoundaryInput_scaled _ hh d
        rw [show radialSevenScaledBoundary (radialFourSourceStep k) d = 0 from heq] at hi
        have hz : radialSevenNormalizedBoundaryInput (radialFourSourceStep k) 0 = 0 := by
          funext i
          simp [radialSevenNormalizedBoundaryInput, radialSevenBoundaryReconstruct]
        rw [hz] at hi
        exact hd hi.symm
      have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let z : ℂ := (‖x‖⁻¹ : ℝ)
      have hu : ‖z • x‖ = 1 := by
        simp [z, norm_smul, Complex.norm_real, norm_inv, inv_mul_cancel₀ hn]
      have hp := hku (z • x) hu
      rw [← hk (z • x), storage_one_sevenSample_normalized_smul] at hp
      have hnz : ‖z‖ = ‖x‖⁻¹ := by simp [z, Complex.norm_real, norm_inv]
      have hz : Complex.normSq z = (‖x‖^2)⁻¹ := by
        rw [Complex.normSq_eq_norm_sq, hnz, inv_pow]
      rw [hz, inv_mul_eq_div] at hp
      have hf := (lt_div_iff₀ (sq_pos_of_ne_zero hn)).mp hp
      simpa only [x, radialSevenNormalizedBoundaryInput_scaled _ hh d] using hf.le
  have hsum : (∑ a : Fin 7, Complex.normSq (x a)) ≤ 7 * ‖x‖^2 := by
    calc
      _ = ∑ a : Fin 7, ‖x a‖^2 := by simp only [Complex.normSq_eq_norm_sq]
      _ ≤ ∑ _a : Fin 7, ‖x‖^2 := by
        apply Finset.sum_le_sum
        intro a _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x a) 2
      _ = 7 * ‖x‖^2 := by simp
  calc
    (ε/7) * (∑ a : Fin 7, Complex.normSq (radialSevenScaledBoundary (radialFourSourceStep k) d a))
      ≤ (ε/7) * (7*‖x‖^2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ε * ‖x‖^2 := by ring
    _ ≤ _ := hfloor

/-- The same completed source gives finite-combination chiral contractivity
on the seven-node radial family, using the existing storage equivalence. -/
theorem chiralMultiplier_seven_eventually_contractive :
    ∀ᶠ k : ℕ in atTop,
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k 7 := by
  filter_upwards [storage_one_original_sevenSample_eventually_pos] with k hk
  apply (chiralMultiplierContractiveAt_iff_storage_one_nonnegative k 7).mpr
  intro c
  by_cases hc : c = 0
  · simp [hc, storage]
  · exact (hk c hc).le

end
end CarrySelfAdjointOperator
