import CarrySelfAdjointOperator.NativePhysicalFiniteSewing

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators
open Polynomial NativeCauchyPorts NativeLaguerre
noncomputable section
set_option autoImplicit false

def finiteValveCoefficients (N : ℕ) (q : ℝ) (v : Fin N → ℂ) : Fin (N+2) → ℂ :=
  fun j => finiteCoefficientValve q (finRadialCoefficients N v) j.val

theorem finiteValve_outside (N : ℕ) (q : ℝ) (v : Fin N → ℂ) (j : ℕ) (hj : N+2 ≤ j) :
    finiteCoefficientValve q (finRadialCoefficients N v) j = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t+2 := ⟨j-2, by omega⟩
  simp only [finiteCoefficientValve, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul, coefficientShift_succ]
  rw [finRadialCoefficients_outside N v (t+2) (by omega),
    finRadialCoefficients_outside N v (t+1) (by omega),
    finRadialCoefficients_outside N v t (by omega)]
  ring

/-- Two new coordinates are retained in the finite valve window. -/
theorem finiteValve_zeroExtension (N : ℕ) (q : ℝ) (v : Fin N → ℂ) :
    finRadialCoefficients (N+2) (finiteValveCoefficients N q v) =
      finiteCoefficientValve q (finRadialCoefficients N v) := by
  ext j
  by_cases hj : j < N+2
  · rw [finRadialCoefficients_apply (N+2) _ ⟨j, hj⟩]
    rfl
  · rw [finRadialCoefficients_outside (N+2) _ j (by omega),
      finiteValve_outside N q v j (by omega)]

theorem finiteValve_terminal_coordinates (N : ℕ) (q : ℝ) (v : Fin (N+2) → ℂ) :
    finiteValveCoefficients (N+2) q v ⟨N+2, by omega⟩ =
      -2*v ⟨N+1, by omega⟩ + (q : ℂ)*v ⟨N, by omega⟩ ∧
    finiteValveCoefficients (N+2) q v ⟨N+3, by omega⟩ =
      (q : ℂ)*v ⟨N+1, by omega⟩ := by
  constructor <;>
    simp only [finiteValveCoefficients, finiteCoefficientValve, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul, coefficientShift_succ]
  · rw [finRadialCoefficients_outside (N+2) v (N+2) (by omega),
      finRadialCoefficients_apply (N+2) v ⟨N+1, by omega⟩,
      finRadialCoefficients_apply (N+2) v ⟨N, by omega⟩]
    ring
  · rw [finRadialCoefficients_outside (N+2) v (N+3) (by omega),
      finRadialCoefficients_outside (N+2) v (N+2) (by omega),
      finRadialCoefficients_apply (N+2) v ⟨N+1, by omega⟩]
    ring

theorem finiteValve_polynomial (N : ℕ) (q : ℝ) (v : Fin N → ℂ) :
    materialPolynomial (N+2) (finiteValveCoefficients N q v) =
      (q : ℂ)⁻¹ • materialPolynomial N v -
        (2 : ℂ) • (X * materialPolynomial N v) +
        (q : ℂ) • (X^2 * materialPolynomial N v) := by
  ext j
  rw [← finRadialCoefficients_coeff, finiteValve_zeroExtension]
  cases j with
  | zero =>
    simp [finiteCoefficientValve, coefficientShift_zero, finRadialCoefficients_coeff]
  | succ j =>
    cases j with
    | zero =>
      have hsq : (X^2 * materialPolynomial N v).coeff 1 = 0 := by
        rw [show (X : ℂ[X])^2 = X*X by ring, mul_assoc, Polynomial.coeff_X_mul]
        simp
      simp [finiteCoefficientValve, coefficientShift_succ, coefficientShift_zero,
        finRadialCoefficients_coeff, Polynomial.coeff_X_mul, hsq]
    | succ j =>
      simp [finiteCoefficientValve, coefficientShift_succ, finRadialCoefficients_coeff,
        Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul]

theorem finiteValve_physicalGreen (n k : ℕ) (q : ℝ) (v : Fin (2*n) → ℂ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    nativeSourceProjectiveBoundaryJetSynthesis (n+1) k
      (physicalEndpointJetInput (2*(n+1)) k
        (fun j => finiteCoefficientValve q (finRadialCoefficients (2*n) v) j.val)) =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (finiteCoefficientValve q (finRadialCoefficients (2*n) v)) +
          physicalGreenResidualNumerator q k (finiteCoefficientValve q (finRadialCoefficients (2*n) v))) := by
  have he := physicalFiniteSewing_capstone (n+1) k
    (fun j => finiteCoefficientValve q (finRadialCoefficients (2*n) v) j.val) q hq0 hq1
  have hx : finRadialCoefficients (2*(n+1))
      (fun j => finiteCoefficientValve q (finRadialCoefficients (2*n) v) j.val) =
      finiteCoefficientValve q (finRadialCoefficients (2*n) v) := by
    ext j
    by_cases hj : j < 2*(n+1)
    · rw [finRadialCoefficients_apply (2*(n+1)) _ ⟨j, hj⟩]
    · rw [finRadialCoefficients_outside (2*(n+1)) _ j (by omega),
        finiteValve_outside (2*n) q v j (by omega)]
  exact he.1.trans (by simpa only [hx] using he.2)

end
end CarrySelfAdjointOperator.PhysicalSewing
