import CarrySelfAdjointOperator.MaterialChiralCoordinateCanary
import CarrySelfAdjointOperator.AdjacentMaterialLogGapDecomposition
import Mathlib.Algebra.Ring.GeomSum

namespace CarrySelfAdjointOperator.LogGapConnection
open CPFormal.Analytic.Cp FiniteClockJets MaterialCameraJets MaterialChiralCanary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Faithful linear interface for the existing U, with no coordinate change. -/
def sourceCoordinateEnd (n k : ℕ) : Module.End ℂ (FiniteRealSpectralHilbert (2*n)) where
  toFun := sourceCoordinateInput n k
  map_add' x y := by
    ext i
    change (∑ a, nativeSourceChiralJetInputMatrix n k i a * (x a+y a)) =
      (∑ a, nativeSourceChiralJetInputMatrix n k i a * x a) +
        ∑ a, nativeSourceChiralJetInputMatrix n k i a * y a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    change (∑ a, nativeSourceChiralJetInputMatrix n k i a * (c*x a)) =
      c * ∑ a, nativeSourceChiralJetInputMatrix n k i a * x a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

private theorem commutator_power {R : Type*} [Ring R] (U L : R) (r : ℕ) :
    U * L^r - L^r * U =
      ∑ j ∈ Finset.range r, L^j * (U*L-L*U) * L^(r-1-j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ']
    have hs : (∑ j ∈ Finset.range r,
        L^(j+1) * (U*L-L*U) * L^(r+1-1-(j+1))) =
        L * ∑ j ∈ Finset.range r, L^j * (U*L-L*U) * L^(r-1-j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have he : r+1-1-(j+1) = r-1-j := by omega
      rw [he, pow_succ']
      simp only [mul_assoc]
    rw [hs, ← ih]
    simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero, pow_succ']
    noncomm_ring

/-- Actual existing operators, with U L^r - L^r U orientation. -/
theorem sourceCoordinateEnd_commutator_power (n k r : ℕ) :
    sourceCoordinateEnd n k * finiteMaterialClock (2*n)^r -
      finiteMaterialClock (2*n)^r * sourceCoordinateEnd n k =
      ∑ j ∈ Finset.range r,
        finiteMaterialClock (2*n)^j *
          (sourceCoordinateEnd n k * finiteMaterialClock (2*n) -
            finiteMaterialClock (2*n) * sourceCoordinateEnd n k) *
          finiteMaterialClock (2*n)^(r-1-j) :=
  commutator_power _ _ r

/-- Polynomial weight of one oriented log edge at order r; r=0 is empty. -/
def logEdgePowerWeight (q r : ℕ) : ℂ :=
  positiveLogGap q * ∑ m ∈ Finset.range r,
    positiveLogVertexWeight (q+1)^(r-1-m) * positiveLogVertexWeight q^m

theorem logEdgePowerWeight_eq_difference (q r : ℕ) :
    logEdgePowerWeight q r =
      positiveLogVertexWeight (q+1)^r - positiveLogVertexWeight q^r := by
  unfold logEdgePowerWeight
  have hg : positiveLogGap q = positiveLogVertexWeight (q+1) - positiveLogVertexWeight q := by
    simp [positiveLogGap, positiveLogVertexWeight, Nat.add_assoc]
  rw [hg]
  have h := (Commute.all (positiveLogVertexWeight q) (positiveLogVertexWeight (q+1))).mul_geom_sum₂ r
  have hs : (∑ m ∈ Finset.range r,
      positiveLogVertexWeight q^m * positiveLogVertexWeight (q+1)^(r-1-m)) =
      ∑ m ∈ Finset.range r,
        positiveLogVertexWeight (q+1)^(r-1-m) * positiveLogVertexWeight q^m := by
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hs] at h
  linear_combination -h

theorem logPower_difference_eq_edgeSum (i a r : ℕ) (hia : i ≤ a) :
    positiveLogVertexWeight a^r - positiveLogVertexWeight i^r =
      ∑ q ∈ Finset.Ico i a, logEdgePowerWeight q r := by
  induction a, hia using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    rw [Finset.sum_Ico_succ_top ha, ← ih, logEdgePowerWeight_eq_difference]
    ring

/-- Actual forward-weight support: row i can only receive orders a>=i. -/
theorem sourceInputMatrix_zero_below {n k : ℕ} (i a : Fin (2*n)) (ha : a.val < i.val) :
    nativeSourceChiralJetInputMatrix n k i a = 0 := by
  simp [nativeSourceChiralJetInputMatrix, completedGreenForwardWeight,
    Nat.choose_eq_zero_of_lt ha]

/-- Literal commutator coefficient, retaining all source amplitudes/phases. -/
def logCommutatorMatrix (n k r : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  fun i a => nativeSourceChiralJetInputMatrix n k i a *
    ((finiteRealSpectralFrequency a : ℂ)^r - (finiteRealSpectralFrequency i : ℂ)^r)

/-- The matrix is the actual commutator action of the existing linear operators. -/
theorem sourceCoordinateEnd_commutator_apply (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    ((sourceCoordinateEnd n k * finiteMaterialClock (2*n)^r -
        finiteMaterialClock (2*n)^r * sourceCoordinateEnd n k) x) i =
      (logCommutatorMatrix n k r).mulVec (fun a => x a) i := by
  change sourceCoordinateInput n k (materialJet r x) i -
    materialJet r (sourceCoordinateInput n k x) i = _
  rw [sourceCoordinateInput_materialJet_commutator]
  rfl

theorem logCommutatorMatrix_diagonal (n k r : ℕ) (i : Fin (2*n)) :
    logCommutatorMatrix n k r i i = 0 := by simp [logCommutatorMatrix]

theorem logCommutatorMatrix_strict_support {n k r : ℕ} (i a : Fin (2*n))
    (ha : a.val ≤ i.val) : logCommutatorMatrix n k r i a = 0 := by
  rcases ha.eq_or_lt with he | hl
  · have : a = i := Fin.ext he
    subst a
    exact logCommutatorMatrix_diagonal n k r i
  · simp [logCommutatorMatrix, sourceInputMatrix_zero_below i a hl]

/-- Edge contributions remain unsynthesized inside each source coefficient. -/
theorem sourceCoordinateInput_commutator_edgeSum (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ a : Fin (2*n), ∑ q ∈ Finset.Ico i.val a.val,
        logEdgePowerWeight q r * nativeSourceChiralJetInputMatrix n k i a * x a := by
  rw [sourceCoordinateInput_materialJet_commutator]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hia : i.val ≤ a.val
  · have hf (j : Fin (2*n)) : (finiteRealSpectralFrequency j : ℂ) = positiveLogVertexWeight j.val := rfl
    rw [hf a, hf i, logPower_difference_eq_edgeSum i.val a.val r hia]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · have hai : a.val < i.val := by omega
    simp [sourceInputMatrix_zero_below i a hai, Finset.Ico_eq_empty_of_le (by omega : a.val ≤ i.val)]

private theorem interval_sum_eq_finite {N : ℕ} (i a : ℕ) (ha : a ≤ N) (f : ℕ → ℂ) :
    (∑ q ∈ Finset.Ico i a, f q) =
      ∑ q : Fin N, if i ≤ q.val ∧ q.val < a then f q.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun q => if i ≤ q ∧ q < a then f q else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- Contribution passing through one coordinate edge. No Green-port claim. -/
def sourceEdgeContribution (n k : ℕ) (x : FiniteRealSpectralHilbert (2*n))
    (q i : Fin (2*n)) : ℂ :=
  ∑ a : Fin (2*n), if i.val ≤ q.val ∧ q.val < a.val then
    nativeSourceChiralJetInputMatrix n k i a * x a else 0

/-- Reordered whole commutator: each edge retains all later source orders. -/
theorem sourceCoordinateInput_commutator_edgeFlux (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r * sourceEdgeContribution n k x q i := by
  rw [sourceCoordinateInput_commutator_edgeSum]
  have he (a : Fin (2*n)) :
      (∑ q ∈ Finset.Ico i.val a.val,
        logEdgePowerWeight q r * nativeSourceChiralJetInputMatrix n k i a * x a) =
      ∑ q : Fin (2*n), if i.val ≤ q.val ∧ q.val < a.val then
        logEdgePowerWeight q.val r * nativeSourceChiralJetInputMatrix n k i a * x a else 0 :=
    interval_sum_eq_finite i.val a.val (by omega) _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  unfold sourceEdgeContribution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> ring

/-- First nonzero edge in every positive even dimension (including 2,4,6). -/
theorem logCommutatorMatrix_first_edge (n k : ℕ) (hn : 0 < n) :
    logCommutatorMatrix n k 1 ⟨0, by omega⟩ ⟨1, by omega⟩ =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * (Real.log 2 : ℂ) := by
  simp [logCommutatorMatrix, nativeSourceChiralJetInputMatrix, nativeSourceJetOrderPhase,
    completedGreenForwardWeight, finiteRealSpectralFrequency]

theorem logCommutatorMatrix_first_edge_ne_zero (n k : ℕ) (hn : 0 < n)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hHB : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    logCommutatorMatrix n k 1 ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0 := by
  rw [logCommutatorMatrix_first_edge n k hn]
  have ha := completedNativeNormalizedPositiveChiralAmplitude_ne_zero hF hHB
  have hs := canonicalCompletedC3RadialSecondStep_ne_zero k
  have hl : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) (inv_ne_zero hs)) hl

private theorem strict_matrix_power_zero {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : ∀ i a, a.val ≤ i.val → C i a = 0) (r : ℕ) :
    ∀ i a, a.val < i.val+r → (C^r) i a = 0 := by
  induction r with
  | zero =>
    intro i a ha
    have hne : i ≠ a := by intro h; subst a; omega
    simp [hne]
  | succ r ih =>
    intro i a ha
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hbi : b.val ≤ i.val
    · rw [hC i b hbi, zero_mul]
    · rw [ih b a (by omega), mul_zero]

/-- Unconditional finite nilpotence, not cancellation of the signed energy. -/
theorem logCommutatorMatrix_nilpotent (n k r : ℕ) :
    logCommutatorMatrix n k r ^ (2*n) = 0 := by
  ext i a
  exact strict_matrix_power_zero _ (fun i a h => logCommutatorMatrix_strict_support i a h)
    (2*n) i a (by omega)

end
end CarrySelfAdjointOperator.LogGapConnection
