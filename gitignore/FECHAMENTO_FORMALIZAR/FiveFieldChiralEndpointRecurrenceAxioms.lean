import CarrySelfAdjointOperator.FiveFieldChiralEndpointRecurrence

open NativeCarryFiveFieldCapstone

-- These are kernel checks, not numerical evaluations of a physical realization.
example (t1 t2 : ℂ) : twoJumpMomentF t1 t2 2 = -(t1 + t2 + t1 * t2) := by
  simp [twoJumpMomentF, twoJumpHomogeneousMoment]

example (t1 t2 : ℂ) : twoJumpMomentG t1 t2 2 = 2 + (t1 + t2) := by
  simp [twoJumpMomentG, twoJumpHomogeneousMoment]

example (x : ℂ) : recurrenceEndpointPolynomial x 2 = x ^ 2 + 2 * x + 2 := by
  simp [recurrenceEndpointPolynomial]
  ring

example (t1 t2 : ℂ) (m : ℕ) :
    twoJumpMomentF t1 t2 m + (t1 + 1) * twoJumpMomentG t1 t2 m =
      recurrenceEndpointPolynomial t1 m :=
  twoJumpMoment_endpoint_duality t1 t2 t1 (Or.inl rfl) m

example (t1 t2 : ℂ) (m : ℕ) :
    twoJumpMomentF t1 t2 m + (t2 + 1) * twoJumpMomentG t1 t2 m =
      recurrenceEndpointPolynomial t2 m :=
  twoJumpMoment_endpoint_duality t1 t2 t2 (Or.inr rfl) m

-- No distinctness assumption on the endpoints is needed for this algebraic step.
example (t : ℂ) (m : ℕ) :
    twoJumpMomentF t t m + (t + 1) * twoJumpMomentG t t m =
      recurrenceEndpointPolynomial t m :=
  twoJumpMoment_endpoint_duality t t t (Or.inl rfl) m

#print axioms recurrenceEndpointPolynomial_eq_factorial_sum
#print axioms recurrenceEndpointPolynomial_initial_residual
#print axioms recurrenceEndpointPolynomial_residual
#print axioms twoJumpHomogeneousMoment_eq_basis
#print axioms twoJumpHomogeneousMoment_eq_endpoint
#print axioms twoJumpMoment_endpoint_duality
#print axioms twoJumpMoment_projected_endpoint_duality
