import CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControl
import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact finite source transport from the completed difference jets to storage

The map is the existing signed finite-difference transform, followed by the
existing projective amplitude at each radial node. Both Cauchy channels are
transported together. No source moment defines a coefficient of this map.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The phase already present in the raw even/odd boundary synthesis. -/
def nativeSourceJetOrderPhase (a : ℕ) : ℂ := (((-1 : ℝ)^(a/2) : ℝ) : ℂ)

/-- Coefficient matrix fixed by the OLD grid, factorial normalization and
completed source amplitude. This is a source-coordinate transform, not a Gram. -/
def nativeSourceChiralJetInputMatrix (n k : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  fun r a => completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k r) * nativeSourceJetOrderPhase a *
    (((a.val.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ a.val)⁻¹) *
    completedGreenForwardWeight a.val r.val

/-- The full finite coefficient change arising from the completed jet vectors. -/
def nativeSourceChiralJetInput (n k : ℕ) :
    (Fin (2*n) → ℂ) →ₗ[ℂ] (Fin (2*n) → ℂ) where
  toFun x r := ∑ a, nativeSourceChiralJetInputMatrix n k r a * x a
  map_add' x y := by funext r; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

private theorem sum_even_odd {E : Type*} [AddCommMonoid E] (n : ℕ)
    (f : Fin (2*n) → E) :
    (∑ a, f a) = (∑ i : Fin n, f (nativeSourceEvenBoundaryIndex n i)) +
      ∑ i : Fin n, f (nativeSourceOddBoundaryIndex n i) := by
  let e : Fin n × Fin 2 ≃ Fin (2*n) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
  rw [← Equiv.sum_comp e f, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : E => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [e,finProdFinEquiv,nativeSourceEvenBoundaryIndex]
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    simp [e,finProdFinEquiv,nativeSourceOddBoundaryIndex]
    omega

private theorem synthesis_by_order (n k : ℕ) (x : Fin (2*n) → ℂ) :
    nativeSourceProjectiveBoundaryJetSynthesis n k x =
      ∑ a : Fin (2*n), (nativeSourceJetOrderPhase a.val * x a) •
        projectiveChiralDifferenceJet k a.val := by
  change (∑ i : Fin n ⊕ Fin n,
    Sum.elim (nativeSourceEvenBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x) i •
      projectiveChiralDifferenceJet k
        (Sum.elim (fun i : Fin n => 2*i.val) (fun i : Fin n => 2*i.val+1) i)) = _
  rw [Fintype.sum_sum_type, sum_even_odd]
  apply congrArg₂ (fun a b : CanonicalCompletedNativeProjectiveChiralCarrier => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Sum.elim_inl, nativeSourceEvenBoundaryPhase, nativeSourceJetOrderPhase,
      nativeSourceEvenBoundaryIndex]
    rw [show 2*i.val/2 = i.val by omega]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Sum.elim_inr, nativeSourceOddBoundaryPhase, nativeSourceJetOrderPhase,
      nativeSourceOddBoundaryIndex]
    rw [show (2*i.val+1)/2 = i.val by omega]

private theorem differenceJet_in_family (k M order : ℕ) (ho : order < M) :
    projectiveChiralDifferenceJet k order =
      ∑ r : Fin M,
        ((((order.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ order)⁻¹) *
          completedGreenForwardWeight order r.val *
          completedNativeNormalizedPositiveChiralAmplitude
            (canonicalCompletedC3RadialTiltPoint k r)) •
        canonicalCompletedNativeRadialChiralDefectState k r := by
  have hsum : (∑ r ∈ Finset.range (order+1), completedGreenForwardWeight order r •
      canonicalCompletedNativeRadialProjectiveChiralState k r) =
      ∑ r : Fin M, completedGreenForwardWeight order r.val •
        canonicalCompletedNativeRadialProjectiveChiralState k r := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => completedGreenForwardWeight order r •
        canonicalCompletedNativeRadialProjectiveChiralState k r) M]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hlt : order < r := by
      have hn : ¬ r < order+1 := by simpa only [Finset.mem_range] using hr
      omega
    simp [completedGreenForwardWeight, Nat.choose_eq_zero_of_lt hlt]
  unfold projectiveChiralDifferenceJet
  rw [hsum]
  simp only [canonicalCompletedNativeRadialProjectiveChiralState, Finset.smul_sum, smul_smul, mul_assoc]

/-- Exact whole vector sewing, with the SAME coefficient map on both channels.
This equality precedes any norm, scalar readout, sign or regularity condition. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource (n k : ℕ)
    (x : Fin (2*n) → ℂ) :
    nativeSourceProjectiveBoundaryJetSynthesis n k x =
      (radialIncidentSynthesis k (2*n) (nativeSourceChiralJetInput n k x),
       radialReturnedSynthesis k (2*n) (nativeSourceChiralJetInput n k x)) := by
  have he : nativeSourceProjectiveBoundaryJetSynthesis n k x =
      ∑ r : Fin (2*n), (nativeSourceChiralJetInput n k x r) •
        canonicalCompletedNativeRadialChiralDefectState k r := by
    rw [synthesis_by_order]
    simp_rw [differenceJet_in_family k (2*n) _ (Fin.isLt _), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_smul]
    congr 1
    change (∑ a : Fin (2*n), (nativeSourceJetOrderPhase a.val * x a) * _) =
      ∑ a : Fin (2*n), nativeSourceChiralJetInputMatrix n k r a * x a
    apply Finset.sum_congr rfl
    intro a _
    unfold nativeSourceChiralJetInputMatrix
    ring
  rw [he]
  apply Prod.ext
  · exact map_sum
      (AddMonoidHom.fst CanonicalCompletedNativeChiralCauchyCarrier
        CanonicalCompletedNativeChiralCauchyCarrier)
      (fun r : Fin (2*n) => (nativeSourceChiralJetInput n k x r) •
        canonicalCompletedNativeRadialChiralDefectState k r) Finset.univ
  · exact map_sum
      (AddMonoidHom.snd CanonicalCompletedNativeChiralCauchyCarrier
        CanonicalCompletedNativeChiralCauchyCarrier)
      (fun r : Fin (2*n) => (nativeSourceChiralJetInput n k x r) •
        canonicalCompletedNativeRadialChiralDefectState k r) Finset.univ

/-- The existing original storage, not a proxy energy, in the exact jet chart. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage (n k : ℕ)
    (x : Fin (2*n) → ℂ) :
    2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) =
      2 * (storage k (nativeSourceChiralJetInput n k x) 1).re := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource, storage_re_eq_norm_balance]
  simp [radialIncidentSynthesis, radialReturnedSynthesis]

/-- All dimensions: control of the ORIGINAL full storage, in its geometric
finite-difference coordinates. Every cross and analytic completion is retained. -/
theorem storage_one_chiralJetInput_eventually_energy_control (n : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |2 * (storage k (nativeSourceChiralJetInput n k x) 1).re -
        nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η * ‖x‖^2 := by
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] using
    nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control n η hη

/-- The old six-source margin controls the ORIGINAL storage in this same chart. -/
theorem storage_one_chiralJetInput_six_eventually_relative_control
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      |2 * (storage k (nativeSourceChiralJetInput 3 k x) 1).re -
        nativeSourceFiniteBoundaryEnergy 6 x| ≤ η * nativeSourceFiniteBoundaryEnergy 6 x := by
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] using
    nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control η hη

/-- Strict source storage margin in the same geometric six-jet chart. -/
theorem storage_one_chiralJetInput_six_eventually_coercive :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      ε * ‖x‖^2 ≤ (storage k (nativeSourceChiralJetInput 3 k x) 1).re := by
  obtain ⟨ε,hε,hb⟩ := nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant
  refine ⟨ε,hε,?_⟩
  filter_upwards [hb] with k hk
  intro x
  have he := nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage 3 k x
  have ht := hk x
  linarith

/-- No BR2 or positivity assumption enters invertibility of this geometric map. -/
theorem nativeSourceChiralJetInput_injective (n k : ℕ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    Function.Injective (nativeSourceChiralJetInput n k) := by
  have htri : (nativeSourceChiralJetInputMatrix n k).BlockTriangular id := by
    intro i j hij
    have hlt : j.val < i.val := hij
    simp [nativeSourceChiralJetInputMatrix, completedGreenForwardWeight,
      Nat.choose_eq_zero_of_lt hlt]
  have hd : (nativeSourceChiralJetInputMatrix n k).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular htri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have ha := completedNativeNormalizedPositiveChiralAmplitude_ne_zero (hreg i).1 (hreg i).2
    have hp : nativeSourceJetOrderPhase i.val ≠ 0 := by
      unfold nativeSourceJetOrderPhase
      exact_mod_cast pow_ne_zero (i.val/2) (by norm_num : (-1 : ℝ) ≠ 0)
    have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    have hs := canonicalCompletedC3RadialSecondStep_ne_zero k
    simpa [nativeSourceChiralJetInputMatrix, completedGreenForwardWeight] using
      mul_ne_zero (mul_ne_zero ha hp) (inv_ne_zero (mul_ne_zero hf (pow_ne_zero _ hs)))
  intro x y hxy
  have hz : x-y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd (by
    rw [Matrix.mulVec_sub]
    change nativeSourceChiralJetInput n k x - nativeSourceChiralJetInput n k y = 0
    rw [hxy, sub_self])
  exact sub_eq_zero.mp hz

/-- Eventual bijectivity: the normalized chart covers ALL original coefficients
in each fixed dimension. Its conditioning is not asserted uniform in k or n. -/
theorem nativeSourceChiralJetInput_eventually_bijective (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, Function.Bijective (nativeSourceChiralJetInput n k) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)] with k hk
  have hi := nativeSourceChiralJetInput_injective n k (fun i => ⟨(hk i).2.1, (hk i).2.2⟩)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- All original source inputs are covered by the control, without a fitted
inverse or a new source norm. The unique jet chart is fixed geometrically. -/
theorem storage_one_chiralJetInput_allCoefficients_control (n : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin (2*n) → ℂ,
      ∃ x : Fin (2*n) → ℂ, nativeSourceChiralJetInput n k x = c ∧
        |2 * (storage k c 1).re - nativeSourceFiniteBoundaryEnergy (2*n) x| ≤
          η * ‖x‖^2 := by
  filter_upwards [nativeSourceChiralJetInput_eventually_bijective n,
    storage_one_chiralJetInput_eventually_energy_control n η hη] with k hb hk
  intro c
  obtain ⟨x,hx⟩ := hb.2 c
  refine ⟨x,hx,?_⟩
  rw [← hx]
  exact hk x

/-- The SAME complete raw Gamma correction gap is controlled in every fixed
finite order. The three other channels cancel by the old whole-source identity. -/
theorem rawGamma_chiralJetInput_eventually_energy_control (n : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      let c := nativeSourceChiralJetInput n k x
      |4 * (‖gammaSourceSynthesis k c 1‖^2 -
        (rawGammaWronskianBalance k c c 1 1).im) -
          nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η * ‖x‖^2 := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control n η hη,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)] with k hk hreg
  intro x
  dsimp only
  have hb := hk x
  rw [storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k _ 1
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)] at hb
  convert hb using 1
  congr 1
  ring

/-- In the old certified six-coordinate sector, the actual raw correction is
strictly dominated by Gamma energy, with a margin in the same geometric chart. -/
theorem rawGamma_chiralJetInput_six_eventually_coercive :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 6 → ℂ,
      let c := nativeSourceChiralJetInput 3 k x
      ε * ‖x‖^2 ≤ ‖gammaSourceSynthesis k c 1‖^2 -
        (rawGammaWronskianBalance k c c 1 1).im := by
  obtain ⟨ε,hε,hb⟩ := storage_one_chiralJetInput_six_eventually_coercive
  refine ⟨ε/2, div_pos hε (by norm_num), ?_⟩
  filter_upwards [hb,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk hreg
  intro x
  dsimp only
  have ht := hk x
  rw [storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k _ 1
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)] at ht
  linarith

end
end CarrySelfAdjointOperator
