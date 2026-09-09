import CarrySelfAdjointOperator.NewtonCarryGreenBridge
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Exact Stirling transport of the existing Newton depth jets

Powers of depth are expressed through the existing Newton jets by the
second-kind Stirling coefficients. The leading coefficient is factorial;
the inverse is obtained by isolating that nonzero diagonal term.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open scoped BigOperators
open PowerSeries

noncomputable section

private theorem mul_descFactorial_eq (k j : ℕ) :
    k * k.descFactorial j = k.descFactorial (j + 1) + j * k.descFactorial j := by
  by_cases h : j ≤ k
  · rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel h]
  · have hlt : k < j := Nat.lt_of_not_ge h
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

/-- The finite Stirling identity, proved for every degree and sample index. -/
theorem pow_eq_sum_stirlingSecond_descFactorial (r k : ℕ) :
    k ^ r = ∑ j ∈ Finset.range (r + 1), Nat.stirlingSecond r j * k.descFactorial j := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hshift :
          (∑ j ∈ Finset.range (r + 1), j * Nat.stirlingSecond r j * k.descFactorial j) =
          ∑ j ∈ Finset.range (r + 1),
            (j + 1) * Nat.stirlingSecond r (j + 1) * k.descFactorial (j + 1) := by
        have h := (Finset.sum_range_succ
          (fun j => j * Nat.stirlingSecond r j * k.descFactorial j) (r + 1)).symm.trans
          (Finset.sum_range_succ'
            (fun j => j * Nat.stirlingSecond r j * k.descFactorial j) (r + 1))
        simpa [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self r)] using h
      calc
        k ^ (r + 1) = ∑ j ∈ Finset.range (r + 1),
            Nat.stirlingSecond r j * (k * k.descFactorial j) := by
          rw [pow_succ', ih, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j ∈ Finset.range (r + 1), Nat.stirlingSecond r j * k.descFactorial (j + 1)) +
            ∑ j ∈ Finset.range (r + 1), j * Nat.stirlingSecond r j * k.descFactorial j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_descFactorial_eq]
          ring
        _ = ∑ j ∈ Finset.range (r + 1 + 1),
            Nat.stirlingSecond (r + 1) j * k.descFactorial j := by
          rw [hshift, Finset.sum_range_succ'
            (fun j => Nat.stirlingSecond (r + 1) j * k.descFactorial j) (r + 1)]
          simp only [Nat.stirlingSecond_succ_zero, zero_mul, add_zero]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [Nat.stirlingSecond_succ_succ]
          ring

/-- Power-depth samples are finite Stirling combinations of Newton samples. -/
theorem pow_mul_amplitude_eq_sum_newtonJet {R : Type*} [CommRing R]
    (q : R) (r k : ℕ) :
    (k : R) ^ r * q ^ k =
      ∑ j ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r j : R) * (j.factorial : R) * newtonJet q j k := by
  have h : (k : R) ^ r =
      ∑ j ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r j : R) * (j.factorial : R) * (k.choose j : R) := by
    have hn := pow_eq_sum_stirlingSecond_descFactorial r k
    simp only [Nat.descFactorial_eq_factorial_mul_choose] at hn
    simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul, mul_assoc] using
      congrArg (fun n : ℕ => (n : R)) hn
  rw [h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [newtonJet]
  ring

/-- On a carry tower, the logarithmic power of the critical amplitude is the
same Stirling combination, with the single scale factor `log p`. -/
theorem tower_log_power_criticalAmplitude_eq_stirling_newtonJet
    (p k r : ℕ) :
    Real.log ((p : ℝ) ^ k) ^ r *
        CPFormal.Carry.Cp.criticalAmplitude p k =
      Real.log (p : ℝ) ^ r *
        ∑ j ∈ Finset.range (r + 1),
      (Nat.stirlingSecond r j : ℝ) * (j.factorial : ℝ) *
            newtonJet (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio p) j k := by
  rw [Real.log_pow]
  calc
    ((k : ℝ) * Real.log (p : ℝ)) ^ r *
        CPFormal.Carry.Cp.criticalAmplitude p k =
      Real.log (p : ℝ) ^ r * ((k : ℝ) ^ r *
        CPFormal.Carry.Cp.criticalAmplitude p k) := by ring
    _ = Real.log (p : ℝ) ^ r * ((k : ℝ) ^ r *
        CPFormal.Analytic.Cp.primeCarryAmplitudeRatio p ^ k) := by
      congr 2
      rw [← newtonJet_zero_eq_criticalAmplitude p k, newtonJet_zero]
    _ = Real.log (p : ℝ) ^ r *
        ∑ j ∈ Finset.range (r + 1),
          (Nat.stirlingSecond r j : ℝ) * (j.factorial : ℝ) *
            newtonJet (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio p) j k := by
      rw [pow_mul_amplitude_eq_sum_newtonJet]

/-- Explicit triangular recovery of each existing Newton jet. -/
theorem factorial_mul_newtonJet_eq_power_sub_lower {R : Type*} [CommRing R]
    (q : R) (r k : ℕ) :
    (r.factorial : R) * newtonJet q r k = (k : R) ^ r * q ^ k -
      ∑ j ∈ Finset.range r,
        (Nat.stirlingSecond r j : R) * (j.factorial : R) * newtonJet q j k := by
  have h := pow_mul_amplitude_eq_sum_newtonJet q r k
  rw [Finset.sum_range_succ] at h
  simp only [Nat.stirlingSecond_self, Nat.cast_one, one_mul] at h
  exact eq_sub_of_add_eq' h.symm

/-- The same finite transport holds as a formal generating-series identity. -/
theorem mk_power_amplitude_eq_stirling_projective {R : Type*} [CommRing R]
    (q : R) (r : ℕ) :
    mk (fun k => (k : R) ^ r * q ^ k) =
      ∑ j ∈ Finset.range (r + 1),
        C ((Nat.stirlingSecond r j : R) * (j.factorial : R)) *
          (weightedCoordinate q ^ j * (1 + weightedCoordinate q)) := by
  simp_rw [← mk_newtonJet_eq_weightedProjective]
  ext k
  simpa only [map_sum, coeff_C_mul, coeff_mk, mul_assoc] using
    pow_mul_amplitude_eq_sum_newtonJet q r k

/-- The exact finite frame matrix, with output order on rows and Newton
order on columns. Its entries vanish strictly above the diagonal. -/
def stirlingNewtonMatrix (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => (Nat.stirlingSecond i.val j.val : ℂ) * (j.val.factorial : ℂ)

theorem stirlingNewtonMatrix_det (N : ℕ) :
    (stirlingNewtonMatrix N).det = ∏ i : Fin (N + 1), (i.val.factorial : ℂ) := by
  have ht : (stirlingNewtonMatrix N).BlockTriangular OrderDual.toDual := by
    intro i j h
    have hij : i.val < j.val := h
    simp [stirlingNewtonMatrix, Nat.stirlingSecond_eq_zero_of_lt hij]
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [stirlingNewtonMatrix, Nat.stirlingSecond_self]

theorem stirlingNewtonMatrix_det_ne_zero (N : ℕ) :
    (stirlingNewtonMatrix N).det ≠ 0 := by
  rw [stirlingNewtonMatrix_det]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr i.val.factorial_ne_zero

/-- Every finite Stirling frame change is bijective. This is an algebraic
statement, with no claim that the change preserves a Hilbert metric. -/
theorem stirlingNewtonMatrix_mulVec_bijective (N : ℕ) :
    Function.Bijective (stirlingNewtonMatrix N).mulVec := by
  have hu : IsUnit (stirlingNewtonMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (stirlingNewtonMatrix_det_ne_zero N))
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
    Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- The matrix acts on the actual Newton samples, including every order
through the chosen finite prefix. -/
theorem stirlingNewtonMatrix_mulVec_newtonJet (N : ℕ) (q : ℂ) (k : ℕ)
    (i : Fin (N + 1)) :
    (stirlingNewtonMatrix N).mulVec (fun j => newtonJet q j.val k) i =
      (k : ℂ) ^ i.val * q ^ k := by
  let f := fun j => (Nat.stirlingSecond i.val j : ℂ) *
    (j.factorial : ℂ) * newtonJet q j k
  change (∑ j : Fin (N + 1), f j.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  have hsum : (∑ j ∈ Finset.range (i.val + 1), f j) =
      ∑ j ∈ Finset.range (N + 1), f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hij : i.val < j := by
      have hj' : i.val + 1 ≤ j := by
        simpa only [Finset.mem_range, not_lt] using hj
      omega
    simp [f, Nat.stirlingSecond_eq_zero_of_lt hij]
  rw [← hsum]
  exact (pow_mul_amplitude_eq_sum_newtonJet q i.val k).symm

end
end CarrySelfAdjointOperator.ProjectiveDepth
