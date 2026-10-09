import CarrySelfAdjointOperator.CompletedNativeChiralBoundaryJetTransport
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixSampleRegularization

/-!
# Complete finite-dimensional control of the signed chiral jet energy

The old vector synthesis, radial grid and both chiral channels are unchanged.
Every finite-step ordered cross remains in the error. The threshold is chosen
AFTER fixing the dimension and tolerance. No boundary sign is assumed.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

private def controlOrder {n : ℕ} : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i => 2*(i : ℕ)) (fun i => 2*(i : ℕ)+1)

private def controlCoefficient (n : ℕ) (x : Fin (2*n) → ℂ) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (nativeSourceEvenBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x)

private theorem coefficient_norm_le (n : ℕ) (x : Fin (2*n) → ℂ)
    (i : Fin n ⊕ Fin n) : ‖controlCoefficient n x i‖ ≤ ‖x‖ := by
  cases i with
  | inl i =>
    simpa [controlCoefficient, nativeSourceEvenBoundaryPhase, norm_mul, norm_pow] using
      norm_le_pi_norm x (nativeSourceEvenBoundaryIndex n i)
  | inr i =>
    simpa [controlCoefficient, nativeSourceOddBoundaryPhase, norm_mul, norm_pow] using
      norm_le_pi_norm x (nativeSourceOddBoundaryIndex n i)

private def coefficientLimit (p q : ℕ) : ℂ :=
  polarizedGreenMomentCoefficient primeDepthGeometricMoment p q

private theorem complete_pairing (n k : ℕ) (x : Fin (2*n) → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k x) =
    ∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
      conj (controlCoefficient n x i) * controlCoefficient n x j *
        canonicalCompletedNativeProjectiveChiralForm
          (projectiveChiralDifferenceJet k (controlOrder i))
          (projectiveChiralDifferenceJet k (controlOrder j)) := by
  exact nativeSourceProjectiveBoundaryJetSynthesis_pairing n k x x

private theorem limit_is_raw_boundary (n : ℕ) (x : Fin (2*n) → ℂ) :
    4 * (∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
      conj (controlCoefficient n x i) * controlCoefficient n x j *
        coefficientLimit (controlOrder i) (controlOrder j)).re =
      nativeSourceFiniteBoundaryEnergy (2*n) x := by
  have h : Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)) atTop
      (nhds (∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
        conj (controlCoefficient n x i) * controlCoefficient n x j *
          coefficientLimit (controlOrder i) (controlOrder j))) := by
    simp_rw [complete_pairing]
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
      (controlOrder i) (controlOrder j)).const_mul _
  have hr := (Complex.continuous_re.continuousAt.tendsto.comp h).const_mul (4 : ℝ)
  have he := nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x
  have ht : Tendsto (fun k => 4 * (canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)).re) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
    simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy] using he
  exact tendsto_nhds_unique hr ht

private theorem finite_cross_bound {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (D : ι → ι → ℂ) (δ R : ℝ)
    (_hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (ha : ∀ i, ‖a i‖ ≤ R) (hD : ∀ i j, ‖D i j‖ ≤ δ) :
    ‖∑ i, ∑ j, conj (a i) * a j * D i j‖ ≤
      (Fintype.card ι : ℝ)^2 * δ * R^2 := by
  calc
    _ ≤ ∑ i, ‖∑ j, conj (a i) * a j * D i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖conj (a i) * a j * D i j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι, R * R * δ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul (mul_le_mul (ha i) (ha j) (norm_nonneg _) hR)
        (hD i j) (norm_nonneg _) (mul_nonneg hR hR)
    _ = _ := by simp [pow_two]; ring

/-- In EVERY fixed finite order the COMPLETE signed chiral energy approaches
its own raw boundary uniformly over ALL coefficient directions. No positive
boundary, moment Gram, discarded mixed term or uniform-in-dimension radius
is used. This is an absolute control in the existing coordinate norm. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
    (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
        ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) -
          nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η * ‖x‖^2 := by
  let m : ℝ := 2*n
  let δ : ℝ := η / (4*m^2+1)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hd : 0 < 4*m^2+1 := by positivity
  have hδ : 0 < δ := div_pos hη hd
  have hb : 4*m^2*δ ≤ η := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hs : ∀ᶠ k : ℕ in atTop, ∀ i j : Fin n ⊕ Fin n,
      ‖canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k (controlOrder i))
        (projectiveChiralDifferenceJet k (controlOrder j)) -
          coefficientLimit (controlOrder i) (controlOrder j)‖ ≤ δ := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have h := ((projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
      (controlOrder i) (controlOrder j)).sub_const
        (coefficientLimit (controlOrder i) (controlOrder j))).norm
    have ht : ∀ᶠ k : ℕ in atTop,
        ‖canonicalCompletedNativeProjectiveChiralForm
          (projectiveChiralDifferenceJet k (controlOrder i))
          (projectiveChiralDifferenceJet k (controlOrder j)) -
            coefficientLimit (controlOrder i) (controlOrder j)‖ < δ :=
      h.eventually_lt tendsto_const_nhds (by simpa [coefficientLimit] using hδ)
    filter_upwards [ht] with k hk
    exact hk.le
  filter_upwards [hs] with k hk
  intro x
  let D : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ := fun i j =>
    canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (controlOrder i))
      (projectiveChiralDifferenceJet k (controlOrder j)) -
        coefficientLimit (controlOrder i) (controlOrder j)
  let e : ℂ := ∑ i, ∑ j, conj (controlCoefficient n x i) * controlCoefficient n x j * D i j
  have herror : ‖e‖ ≤ m^2 * δ * ‖x‖^2 := by
    simpa only [e, Fintype.card_sum, Fintype.card_fin, Nat.cast_add,
      show (n : ℝ)+(n : ℝ) = m by dsimp [m]; ring] using
      finite_cross_bound (controlCoefficient n x) D δ ‖x‖ hδ.le (norm_nonneg x)
        (coefficient_norm_le n x) hk
  have he : 2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
        ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) -
        nativeSourceFiniteBoundaryEnergy (2*n) x = 4 * e.re := by
    rw [← nativeSourceProjectiveBoundaryJetSynthesis_energy,
      ← limit_is_raw_boundary, complete_pairing]
    dsimp [e, D]
    simp only [mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    4 * |e.re| ≤ 4 * ‖e‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm e) (by norm_num)
    _ ≤ 4 * (m^2 * δ * ‖x‖^2) := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ ≤ η * ‖x‖^2 := by nlinarith [sq_nonneg ‖x‖]

private theorem cross_smul (z u v : ℂ) :
    (conj (z*u)*(z*v)).re = Complex.normSq z * (conj u*v).re := by
  have he : conj (z*u)*(z*v) = (Complex.normSq z : ℂ)*(conj u*v) := by
    rw [map_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [he, Complex.re_ofReal_mul]

/-- Homogeneity of the old raw energy, retaining every ordered source cross. -/
theorem nativeSourceFiniteBoundaryEnergy_smul (N : ℕ) (z : ℂ) (x : Fin N → ℂ) :
    nativeSourceFiniteBoundaryEnergy N (z • x) =
      Complex.normSq z * nativeSourceFiniteBoundaryEnergy N x := by
  rw [nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum,
    nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum]
  simp only [Pi.smul_apply, smul_eq_mul, cross_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

/-- Same raw expression and normalization as the source-certified six-jet face. -/
theorem nativeSourceFiniteBoundaryEnergy_six (x : Fin 6 → ℂ) :
    nativeSourceFiniteBoundaryEnergy 6 x = nativeSourceSixBoundaryEnergy x := by
  rw [nativeSourceSixBoundaryEnergy_eq_alternating_green]
  rfl

private theorem six_boundary_margin :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 6 → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy 6 x := by
  obtain ⟨ε, hε, hunit⟩ := radialSixRegularizedStorage_eventually_unit_margin
    (fun _ => 0) continuousAt_const
  have hu := hunit.self_of_nhds
  simp only [radialSixRegularizedStorage_zero] at hu
  refine ⟨ε,hε,?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [nativeSourceFiniteBoundaryEnergy]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let z : ℂ := (‖x‖⁻¹ : ℝ)
    let y : Fin 6 → ℂ := z • x
    have hy : ‖y‖ = 1 := by
      simp [y, z, norm_smul, norm_inv, inv_mul_cancel₀ hn]
    have hxy : (‖x‖ : ℂ) • y = x := by
      dsimp only [y, z]
      rw [smul_smul]
      have hnC : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [mul_inv_cancel₀ hnC]
    have hb := (hu y hy).le
    have he := nativeSourceFiniteBoundaryEnergy_smul 6 (‖x‖ : ℂ) y
    rw [hxy, Complex.normSq_ofReal] at he
    rw [he, nativeSourceFiniteBoundaryEnergy_six]
    nlinarith [sq_nonneg ‖x‖]

/-- Reuse the ALREADY proved six-source boundary margin, then control all
finite-step chiral crosses together. No new source sign is certified. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      |2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).1‖^2 -
        ‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).2‖^2) -
          nativeSourceFiniteBoundaryEnergy 6 x| ≤
        η * nativeSourceFiniteBoundaryEnergy 6 x := by
  obtain ⟨ε,hε,hm⟩ := six_boundary_margin
  filter_upwards [nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
    3 (η*ε) (mul_pos hη hε)] with k hk
  intro x
  have hb := hk x
  have he := mul_le_mul_of_nonneg_left (hm x) hη.le
  nlinarith

/-- Strict dominance of the two ACTUAL completed chiral jet syntheses in the
old certified six-coordinate sector, uniformly over every input direction. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      ε * ‖x‖^2 ≤
        ‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).1‖^2 -
          ‖(nativeSourceProjectiveBoundaryJetSynthesis 3 k x).2‖^2 := by
  obtain ⟨ε,hε,hm⟩ := six_boundary_margin
  refine ⟨ε/4, div_pos hε (by norm_num), ?_⟩
  filter_upwards [nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
    (1/2) (by norm_num)] with k hk
  intro x
  have hb := abs_le.mp (hk x)
  have he := hm x
  linarith

end
end CarrySelfAdjointOperator
