import CarrySelfAdjointOperator.NewtonStirlingTransport

/-!
# The same depth difference in the power and Newton frames

The Stirling matrix already acts on columns of frame samples: `P = S E`.
The row-frame matrices below therefore satisfy `Delta * S = S * J`.
Depth multiplication acts on the full sequence space; a finite polynomial
prefix is invariant under the difference, but not under multiplication.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open CPFormal.Analytic.Cp
open scoped BigOperators

noncomputable section

/-- Powers of depth in the same amplitude coordinates as the Newton jets. -/
def powerDepthJet (q : ℂ) (r k : ℕ) : ℂ := (k : ℂ) ^ r * q ^ k

/-- The existing Stirling transport, expressed with the power-frame name. -/
theorem powerDepthJet_eq_stirling_newton (q : ℂ) (r k : ℕ) :
    powerDepthJet q r k = ∑ j ∈ Finset.range (r + 1),
      (Nat.stirlingSecond r j : ℂ) * (j.factorial : ℂ) * newtonJet q j k :=
  pow_mul_amplitude_eq_sum_newtonJet q r k

theorem carryWeightedScalarFirstDifference_powerDepthJet_apply
    {q : ℂ} (hq : q ≠ 0) (r k : ℕ) :
    carryWeightedScalarFirstDifference q (powerDepthJet q r) k =
      (((k : ℂ) + 1) ^ r - (k : ℂ) ^ r) * q ^ k := by
  simp only [carryWeightedScalarFirstDifference, powerDepthJet, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

private theorem forwardDifference_pow (x : ℂ) (r : ℕ) :
    (x + 1) ^ r - x ^ r =
      ∑ m ∈ Finset.range r, (r.choose m : ℂ) * x ^ m := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- All power orders are lowered by the binomial finite-difference matrix. -/
theorem carryWeightedScalarFirstDifference_powerDepthJet
    {q : ℂ} (hq : q ≠ 0) (r : ℕ) :
    carryWeightedScalarFirstDifference q (powerDepthJet q r) =
      fun k => ∑ m ∈ Finset.range r, (r.choose m : ℂ) * powerDepthJet q m k := by
  funext k
  rw [carryWeightedScalarFirstDifference_powerDepthJet_apply hq,
    forwardDifference_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  simp only [powerDepthJet, mul_assoc]

/-- Linear packaging of the existing difference, on the algebraic sequence core. -/
def weightedDepthDifferenceLinear (q : ℂ) : Module.End ℂ (ℕ → ℂ) where
  toFun := carryWeightedScalarFirstDifference q
  map_add' f g := by
    funext k
    simp only [carryWeightedScalarFirstDifference, Pi.add_apply]
    ring
  map_smul' c f := by
    funext k
    simp only [carryWeightedScalarFirstDifference, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- Multiplication by vertical depth, without truncating its output. -/
def depthMultiplication : Module.End ℂ (ℕ → ℂ) where
  toFun f k := (k : ℂ) * f k
  map_add' f g := by funext k; simp [mul_add]
  map_smul' c f := by funext k; simp [mul_left_comm]

/-- The discrete Ore relation is `Delta + I`, not the continuous derivative law. -/
theorem weightedDepthDifference_depthMultiplication_commutator (q : ℂ) :
    weightedDepthDifferenceLinear q * depthMultiplication -
        depthMultiplication * weightedDepthDifferenceLinear q =
      weightedDepthDifferenceLinear q + LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext k
  change q⁻¹ * (((k + 1 : ℕ) : ℂ) * f (k + 1)) - (k : ℂ) * f k -
      (k : ℂ) * (q⁻¹ * f (k + 1) - f k) =
    (q⁻¹ * f (k + 1) - f k) + f k
  push_cast
  ring

/-- The logarithmic multiplier along the actual tower `p^k`. -/
def towerLogMultiplication (p : ℕ) : Module.End ℂ (ℕ → ℂ) :=
  (Real.log (p : ℝ) : ℂ) • depthMultiplication

theorem towerLogMultiplication_apply (p : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    towerLogMultiplication p f k = (Real.log ((p : ℝ) ^ k) : ℂ) * f k := by
  simp [towerLogMultiplication, depthMultiplication, Real.log_pow]
  ring

/-- Scalar specialization of the same operator commutator to logarithmic depth. -/
theorem weightedDepthDifference_towerLogMultiplication_commutator
    (q : ℂ) (p : ℕ) :
    weightedDepthDifferenceLinear q * towerLogMultiplication p -
        towerLogMultiplication p * weightedDepthDifferenceLinear q =
      (Real.log (p : ℝ) : ℂ) •
        (weightedDepthDifferenceLinear q + LinearMap.id) := by
  have h := congrArg (fun A : Module.End ℂ (ℕ → ℂ) =>
      (Real.log (p : ℝ) : ℂ) • A)
    (weightedDepthDifference_depthMultiplication_commutator q)
  simpa only [towerLogMultiplication, mul_smul_comm, smul_mul_assoc, smul_sub] using h

/-- The native ratio is reused directly, for every carry base. -/
theorem nativeDepthDifference_logMultiplication_commutator (p : ℕ) :
    weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) * towerLogMultiplication p -
        towerLogMultiplication p * weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) =
      (Real.log (p : ℝ) : ℂ) •
        (weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) + LinearMap.id) :=
  weightedDepthDifference_towerLogMultiplication_commutator _ p

/-- Row `i` lists the expansion of the difference of the power jet of order `i`. -/
def powerDifferenceMatrix (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => if j.val < i.val then (i.val.choose j.val : ℂ) else 0

/-- Row `i` lists the expansion of the difference of the Newton jet of order `i`. -/
def newtonDifferenceMatrix (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => if i.val = j.val + 1 then 1 else 0

/-- The power-frame matrix acts on the same concrete sequences as the difference. -/
theorem powerDifferenceMatrix_mulVec_powerDepthJet
    (N : ℕ) {q : ℂ} (hq : q ≠ 0) (k : ℕ) (i : Fin (N + 1)) :
    (powerDifferenceMatrix N).mulVec (fun j => powerDepthJet q j.val k) i =
      carryWeightedScalarFirstDifference q (powerDepthJet q i.val) k := by
  rw [carryWeightedScalarFirstDifference_powerDepthJet hq]
  change (∑ j : Fin (N + 1),
    (if j.val < i.val then (i.val.choose j.val : ℂ) else 0) *
      powerDepthJet q j.val k) = _
  simp only [ite_mul, zero_mul]
  let f : ℕ → ℂ := fun j =>
    if j < i.val then (i.val.choose j : ℂ) * powerDepthJet q j k else 0
  change (∑ j : Fin (N + 1), f j.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  dsimp only [f]
  calc
    (∑ j ∈ Finset.range (N + 1),
        if j < i.val then (i.val.choose j : ℂ) * powerDepthJet q j k else 0) =
        ∑ j ∈ Finset.range i.val,
          if j < i.val then (i.val.choose j : ℂ) * powerDepthJet q j k else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp [hj]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]

/-- The Newton-frame matrix implements the already proved exact lowering law. -/
theorem newtonDifferenceMatrix_mulVec_newtonJet
    (N : ℕ) {q : ℂ} (hq : q ≠ 0) (k : ℕ) (i : Fin (N + 1)) :
    (newtonDifferenceMatrix N).mulVec (fun j => newtonJet q j.val k) i =
      carryWeightedScalarFirstDifference q (newtonJet q i.val) k := by
  by_cases hi : i.val = 0
  · simp [Matrix.mulVec, dotProduct, newtonDifferenceMatrix, hi,
      carryWeightedScalarFirstDifference_newtonJet_zero hq]
  · let j : Fin (N + 1) := ⟨i.val - 1, by omega⟩
    have hij : i.val = j.val + 1 := by dsimp [j]; omega
    have hdelta (l : Fin (N + 1)) : i.val = l.val + 1 ↔ l = j := by
      constructor
      · intro h
        apply Fin.ext
        dsimp [j]
        omega
      · rintro rfl
        exact hij
    rw [hij, carryWeightedScalarFirstDifference_newtonJet_succ hq]
    simp [Matrix.mulVec, dotProduct, newtonDifferenceMatrix, hdelta]

/-- The scalar difference commutes with every finite constant matrix readout. -/
theorem carryWeightedScalarFirstDifference_mulVec
    {ι κ : Type*} [Fintype κ] (q : ℂ) (A : Matrix ι κ ℂ)
    (v : κ → ℕ → ℂ) (i : ι) (k : ℕ) :
    carryWeightedScalarFirstDifference q (fun n => A.mulVec (fun j => v j n) i) k =
      A.mulVec (fun j => carryWeightedScalarFirstDifference q (v j) k) i := by
  simp only [carryWeightedScalarFirstDifference, Matrix.mulVec, dotProduct,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private def newtonSampleMatrix (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => newtonJet 1 j.val k.val

private theorem newtonSampleMatrix_det (N : ℕ) : (newtonSampleMatrix N).det = 1 := by
  have ht : (newtonSampleMatrix N).BlockTriangular id := by
    intro i j h
    have hij : j.val < i.val := h
    simp [newtonSampleMatrix, newtonJet, Nat.choose_eq_zero_of_lt hij]
  rw [Matrix.det_of_upperTriangular ht]
  simp [newtonSampleMatrix, newtonJet]

/-- The existing Stirling matrix intertwines the actual power and Newton
difference actions on every finite prefix. Rows index frame elements. -/
theorem powerDifferenceMatrix_mul_stirlingNewtonMatrix (N : ℕ) :
    powerDifferenceMatrix N * stirlingNewtonMatrix N =
      stirlingNewtonMatrix N * newtonDifferenceMatrix N := by
  have hv : (powerDifferenceMatrix N * stirlingNewtonMatrix N) * newtonSampleMatrix N =
      (stirlingNewtonMatrix N * newtonDifferenceMatrix N) * newtonSampleMatrix N := by
    ext i k
    change ((powerDifferenceMatrix N * stirlingNewtonMatrix N).mulVec
      (fun j => newtonJet 1 j.val k.val)) i =
      ((stirlingNewtonMatrix N * newtonDifferenceMatrix N).mulVec
        (fun j => newtonJet 1 j.val k.val)) i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hS (n : ℕ) : (stirlingNewtonMatrix N).mulVec (fun j => newtonJet 1 j.val n) =
        fun j => powerDepthJet 1 j.val n := by
      funext j
      exact stirlingNewtonMatrix_mulVec_newtonJet N 1 n j
    have hJ : (newtonDifferenceMatrix N).mulVec (fun j => newtonJet 1 j.val k.val) =
        fun j => carryWeightedScalarFirstDifference 1 (newtonJet 1 j.val) k.val := by
      funext j
      exact newtonDifferenceMatrix_mulVec_newtonJet N one_ne_zero k.val j
    rw [hS, powerDifferenceMatrix_mulVec_powerDepthJet N one_ne_zero, hJ,
      ← carryWeightedScalarFirstDifference_mulVec]
    have hframe : (fun n => (stirlingNewtonMatrix N).mulVec
        (fun j => newtonJet 1 j.val n) i) = powerDepthJet 1 i.val := by
      funext n
      exact congrFun (hS n) i
    rw [hframe]
  have hunit : IsUnit (newtonSampleMatrix N).det := by rw [newtonSampleMatrix_det]; exact isUnit_one
  have h := congrArg (fun A => A * (newtonSampleMatrix N)⁻¹) hv
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one] using h

/-- Conjugation uses the existing invertible Stirling matrix, with its
previously proved nonzero determinant. -/
theorem powerDifferenceMatrix_eq_stirling_conjugate (N : ℕ) :
    powerDifferenceMatrix N =
      stirlingNewtonMatrix N * newtonDifferenceMatrix N * (stirlingNewtonMatrix N)⁻¹ := by
  have h := congrArg (fun A => A * (stirlingNewtonMatrix N)⁻¹)
    (powerDifferenceMatrix_mul_stirlingNewtonMatrix N)
  have hu := isUnit_iff_ne_zero.mpr (stirlingNewtonMatrix_det_ne_zero N)
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one] using h

end
end CarrySelfAdjointOperator.ProjectiveDepth
