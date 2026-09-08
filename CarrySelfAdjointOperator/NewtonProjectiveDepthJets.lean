import CarrySelfAdjointOperator.ProjectiveDepthEquivalence

/-!
# Newton jets in the existing projective depth coordinate

The coefficient sequence `choose k r * q^k` has generating series
`Y_q^r * (1 + Y_q)`, where `Y_q` is the rescaling of the existing coordinate.
The sequence difference lowers order when `q` is nonzero. All series identities
are formal; they require no convergence or spectral hypotheses.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries

noncomputable section

section Ring

variable {R : Type*} [CommRing R]

/-- Divided discrete powers dressed by the depth amplitude. -/
def newtonJet (q : R) (r k : ℕ) : R := (k.choose r : R) * q ^ k

@[simp] theorem newtonJet_zero (q : R) (k : ℕ) :
    newtonJet q 0 k = q ^ k := by simp [newtonJet]

@[simp] theorem newtonJet_one (q : R) (k : ℕ) :
    newtonJet q 1 k = (k : R) * q ^ k := by simp [newtonJet]

/-- Dressing is the existing formal rescaling `X ↦ qX`. -/
def weightedCoordinate (q : R) : PowerSeries R := rescale q coordinate

theorem weightedCoordinate_relation (q : R) :
    (1 - C q * X) * weightedCoordinate q = C q * X := by
  have h := congrArg (rescale q) (one_sub_X_mul_coordinate (R := R))
  simpa [weightedCoordinate, rescale_X] using h

/-- Dressing commutes with the Euler derivative of the depth coordinate. -/
theorem euler_weightedCoordinate (q : R) :
    X * (d⁄dX R (weightedCoordinate q)) = rescale q (greenVelocity (R := R)) := by
  ext k
  cases k with
  | zero =>
      rw [coeff_rescale]
      simp [greenVelocity]
  | succ k =>
      rw [coeff_succ_X_mul, coeff_derivative, weightedCoordinate,
        coeff_rescale, coeff_rescale, coordinate, coeff_succ_X_mul]
      simp only [greenVelocity, coeff_succ_X_mul, DiscreteValve.geometricSeries,
        DiscreteValve.greenKernelSeries, coeff_mk]
      ring

/-- The undressed Newton generating function in the existing projective chart. -/
theorem mk_choose_eq_projective (r : ℕ) :
    (mk fun k => (k.choose r : R)) = coordinate ^ r * (1 + coordinate) := by
  rw [one_add_coordinate_eq_geometricSeries, coordinate, mul_pow, mul_assoc,
    ← pow_succ]
  change (mk fun k => (k.choose r : R)) = X ^ r * (mk 1 : PowerSeries R) ^ (r + 1)
  rw [mk_one_pow_eq_mk_choose_add]
  ext k
  rw [coeff_mk, coeff_X_pow_mul']
  by_cases h : r ≤ k
  · simp [h, Nat.add_sub_of_le h]
  · simp [h, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

/-- All Newton orders are powers of the dressed projective coordinate,
with the same geometric density factor. -/
theorem mk_newtonJet_eq_weightedProjective (q : R) (r : ℕ) :
    mk (newtonJet q r) = weightedCoordinate q ^ r * (1 + weightedCoordinate q) := by
  have h := congrArg (rescale q) (mk_choose_eq_projective (R := R) r)
  have hm : rescale q (mk fun k => (k.choose r : R)) = mk (newtonJet q r) := by
    ext k
    simp [coeff_rescale, newtonJet, mul_comm]
  rw [hm] at h
  simpa [weightedCoordinate] using h

/-- In order one the Newton generating function is precisely the rescaled
Green velocity already constructed in the projective depth module. -/
theorem mk_newtonJet_one_eq_rescale_greenVelocity (q : R) :
    mk (newtonJet q 1) = rescale q (greenVelocity (R := R)) := by
  rw [mk_newtonJet_eq_weightedProjective, greenVelocity_eq_coordinate_mul_one_add]
  simp [weightedCoordinate]

/-- Undoing amplitude rescaling and then the existing projective substitution
recovers the polynomial frame. -/
theorem toProjective_mk_choose (r : ℕ) :
    toProjective (mk fun k => (k.choose r : R)) = X ^ r * (1 + X) := by
  rw [mk_choose_eq_projective]
  unfold toProjective
  simp only [PowerSeries.subst_mul (inverseCoordinate_hasSubst (R := R)),
    PowerSeries.subst_pow (inverseCoordinate_hasSubst (R := R)),
    PowerSeries.subst_add (inverseCoordinate_hasSubst (R := R)),
    coordinate_subst_inverseCoordinate]
  congr 2
  change PowerSeries.subst inverseCoordinate (C (1 : R)) = 1
  rw [PowerSeries.subst_C]
  rfl

end Ring

end
end CarrySelfAdjointOperator.ProjectiveDepth
