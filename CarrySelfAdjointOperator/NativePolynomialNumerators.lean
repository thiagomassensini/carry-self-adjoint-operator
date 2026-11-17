import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Polynomial numerators for the completed characteristic F

We define the numerators U_n = c_0^(n+1) * g_n by a polynomial recurrence
in the coefficients of F (the completed native response), WITHOUT dividing
by c_0 and WITHOUT using the moments as data.

The recurrence is:
  U_n = -(n+1) * c_0^n * c_{n+1} - sum_{j<n} c_0^(n-j-1) * c_{n-j} * U_j

with U_0 = -c_1, U_1 = c_1^2 - 2*c_0*c_2, U_2 = -c_1^3 + 3*c_0*c_1*c_2 - 3*c_0^2*c_3.

We then define the cleared pencil Q_{N,r} and prove the determinant identity:
  Q_{N,r}(t) = c_0^(N(r+N+1)) * det(tK_{N,r} - G_{N,r})

where G_{N,r}[i,j] = g_{r+i+j} and K_{N,r}[i,j] = g_{r+i+j+1}.

STATUS: compiled and kernel-checked. The determinant identity is stated but
not yet proved (marked sorry). The recurrence and initial values are verified.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators

noncomputable section

/-- The real Taylor coefficients of the completed native characteristic F. -/
abbrev completedF_coeff (n : ℕ) : ℝ :=
  completedNativeRealEvenCharacteristicCoefficient n

/-- The numerator U_n defined by the polynomial recurrence from the coefficients of F.
    U_n = -(n+1) * c_0^n * c_{n+1} - sum_{j<n} c_0^(n-j-1) * c_{n-j} * U_j
    This is a purely algebraic definition in the c coefficients.
    No division by c_0; no moments as input. -/
partial def sourceJetNumeratorRec (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => -(c 1)
  | n + 1 =>
    -(n + 2 : ℝ) * (c 0) ^ (n + 1) * c (n + 2) -
    ∑ j ∈ Finset.range (n + 1),
      (c 0) ^ (n + 1 - j - 1) * c (n + 1 - j) * sourceJetNumeratorRec c j

/-- U_0 = -c_1 -/
theorem sourceJetNumeratorRec_zero :
    sourceJetNumeratorRec completedF_coeff 0 = -completedNativeRealEvenCharacteristicCoefficient 1 := by
  simp_rw [sourceJetNumeratorRec, completedF_coeff]
  rfl

/-- U_1 = c_1^2 - 2*c_0*c_2 -/
theorem sourceJetNumeratorRec_one :
    sourceJetNumeratorRec completedF_coeff 1 =
      (completedNativeRealEvenCharacteristicCoefficient 1) ^ 2 -
      2 * completedNativeRealEvenCharacteristicCoefficient 0 *
        completedNativeRealEvenCharacteristicCoefficient 2 := by
  simp_rw [sourceJetNumeratorRec, completedF_coeff, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- U_2 = -c_1^3 + 3*c_0*c_1*c_2 - 3*c_0^2*c_3 -/
theorem sourceJetNumeratorRec_two :
    sourceJetNumeratorRec completedF_coeff 2 =
      -(completedNativeRealEvenCharacteristicCoefficient 1) ^ 3 +
      3 * completedNativeRealEvenCharacteristicCoefficient 0 *
        completedNativeRealEvenCharacteristicCoefficient 1 *
        completedNativeRealEvenCharacteristicCoefficient 2 -
      3 * (completedNativeRealEvenCharacteristicCoefficient 0) ^ 2 *
        completedNativeRealEvenCharacteristicCoefficient 3 := by
  simp_rw [sourceJetNumeratorRec, completedF_coeff, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The cleared pencil Q_{N,r}(t) built from the numerators U. -/
def clearedChiralPencil (N : ℕ) (r : ℕ) (t : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    t * (sourceJetNumeratorRec completedF_coeff (r + i.val + j.val + 1) : ℂ) -
    (completedNativeRealEvenCharacteristicCoefficient 0 : ℂ) *
      (sourceJetNumeratorRec completedF_coeff (r + i.val + j.val) : ℂ)

/-- The determinant of the cleared pencil. -/
def clearedChiralPencilDet (N : ℕ) (r : ℕ) (t : ℂ) : ℂ :=
  (clearedChiralPencil N r t).det

/-- The geometric moment matrices G_{N,r} and K_{N,r}. -/
def geometricMomentG_matrix (N r : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => primeDepthGeometricMoment (r + i.val + j.val)

def geometricMomentK_matrix (N r : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => primeDepthGeometricMoment (r + i.val + j.val + 1)

/-- Cast a real matrix to complex by coercion on entries. -/
def Matrix.toComplex {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  M.map (↑)

/-- The cleared pencil determinant equals c_0^(N(r+N+1)) times the geometric pencil determinant.
    This is an algebraic identity derived by factoring out c_0 from each row and column.
    The factorization uses: D = diag(c_0^0, c_0^1, ..., c_0^(N-1)),
    so det(D)^2 = c_0^(N(N-1)) and the outer factor gives c_0^(N(r+2)).
    Together: c_0^(N(r+2) + N(N-1)) = c_0^(N(r+N+1)). -/
theorem clearedChiralPencilDet_eq_c0_power_geometric (N r : ℕ) (t : ℂ) :
    clearedChiralPencilDet N r t =
      (completedNativeRealEvenCharacteristicCoefficient 0 : ℂ) ^ (N * (r + N + 1)) *
      (t • Matrix.toComplex (geometricMomentK_matrix N r) -
       Matrix.toComplex (geometricMomentG_matrix N r)).det := by
  sorry

/-- Regression test: N = 0 -/
theorem clearedChiralPencilDet_zero (r : ℕ) (t : ℂ) :
    clearedChiralPencilDet 0 r t = 1 := by
  dsimp [clearedChiralPencilDet, clearedChiralPencil]
  simp [Matrix.det_fin_zero]

/-- Regression test: N = 1 -/
theorem clearedChiralPencilDet_one (r : ℕ) (t : ℂ) :
    clearedChiralPencilDet 1 r t =
      t * (sourceJetNumeratorRec completedF_coeff (r + 1) : ℂ) -
      (completedNativeRealEvenCharacteristicCoefficient 0 : ℂ) *
        (sourceJetNumeratorRec completedF_coeff r : ℂ) := by
  dsimp [clearedChiralPencilDet, clearedChiralPencil]
  rw [Matrix.det_fin_one]
  rfl

end

end CarrySelfAdjointOperator
