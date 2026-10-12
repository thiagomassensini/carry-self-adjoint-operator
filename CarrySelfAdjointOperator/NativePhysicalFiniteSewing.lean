import CarrySelfAdjointOperator.NativePhysicalEndpointEncoder
import CarrySelfAdjointOperator.NativePhysicalGreenResolvent

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators
open Polynomial NativeCauchyPorts NativeLaguerre
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

def finRadialCoefficients (N : ℕ) (v : Fin N → ℂ) : ℕ →₀ ℂ :=
  ∑ j : Fin N, Finsupp.single j.val (v j)

theorem finRadialCoefficients_apply (N : ℕ) (v : Fin N → ℂ) (j : Fin N) :
    finRadialCoefficients N v j.val = v j := by
  classical
  simp [finRadialCoefficients, Finsupp.single_apply, ← Fin.ext_iff]

theorem finRadialCoefficients_outside (N : ℕ) (v : Fin N → ℂ) (j : ℕ) (hj : N ≤ j) :
    finRadialCoefficients N v j = 0 := by
  classical
  change (∑ a : Fin N, Finsupp.single a.val (v a)) j = 0
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [if_neg (by have ha := a.isLt; omega)]

theorem physicalCompletedFiniteSource_fin (N k : ℕ) (v : Fin N → ℂ) :
    physicalCompletedFiniteSource k (finRadialCoefficients N v) =
      finiteProjectiveSource N k v := by
  rw [physicalCompletedFiniteSource_original]
  simp [finRadialCoefficients, finiteProjectiveSource]

/-- The three whole-vector routes in the SAME original two-leg carrier. -/
theorem physicalFiniteSewing_capstone (n k : ℕ) (v : Fin (2*n) → ℂ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    nativeSourceProjectiveBoundaryJetSynthesis n k
        (physicalEndpointJetInput (2*n) k v) = finiteProjectiveSource (2*n) k v ∧
    finiteProjectiveSource (2*n) k v =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (finRadialCoefficients (2*n) v) +
          physicalGreenResidualNumerator q k (finRadialCoefficients (2*n) v)) := by
  refine ⟨physicalEndpointJetInput_wholeSource n k v, ?_⟩
  rw [← physicalCompletedFiniteSource_fin]
  exact physicalCompletedFiniteGreen_reconstruct q hq0 hq1 k _

/-- Extension by zero changes only the finite coordinate window. -/
def extendMaterial (N M : ℕ) (v : Fin N → ℂ) : Fin M → ℂ :=
  fun j => if h : j.val < N then v ⟨j.val, h⟩ else 0

theorem materialPolynomial_extend (N M : ℕ) (hNM : N ≤ M) (v : Fin N → ℂ) :
    materialPolynomial M (extendMaterial N M v) = materialPolynomial N v := by
  ext j
  by_cases hj : j < N
  · simp [materialPolynomial, extendMaterial, hj, lt_of_lt_of_le hj hNM]
  · by_cases hjM : j < M
    · simp [materialPolynomial, extendMaterial, hj, hjM,
        Polynomial.ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_lt hj)]
    · simp [materialPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge,
        Nat.le_of_not_lt hj, Nat.le_of_not_lt hjM]

theorem physicalEndpointJetInput_extend (N M k : ℕ) (hNM : N ≤ M)
    (v : Fin N → ℂ) (a : Fin N) :
    physicalEndpointJetInput M k (extendMaterial N M v) ⟨a.val, lt_of_lt_of_le a.isLt hNM⟩ =
      physicalEndpointJetInput N k v a := by
  change endpointGauge k a * _ = endpointGauge k a * _
  rw [materialPolynomial_extend N M hNM]

theorem finRadialCoefficients_extend (N M : ℕ) (hNM : N ≤ M) (v : Fin N → ℂ) :
    finRadialCoefficients M (extendMaterial N M v) = finRadialCoefficients N v := by
  ext j
  by_cases hj : j < N
  · rw [finRadialCoefficients_apply M _ ⟨j, lt_of_lt_of_le hj hNM⟩,
      finRadialCoefficients_apply N v ⟨j, hj⟩]
    simp [extendMaterial, hj]
  · by_cases hjM : j < M
    · rw [finRadialCoefficients_apply M _ ⟨j, hjM⟩,
        finRadialCoefficients_outside N v j (Nat.le_of_not_lt hj)]
      simp [extendMaterial, hj]
    · rw [finRadialCoefficients_outside M _ j (Nat.le_of_not_lt hjM),
        finRadialCoefficients_outside N v j (Nat.le_of_not_lt hj)]

theorem finiteProjectiveSource_extend (N M k : ℕ) (hNM : N ≤ M) (v : Fin N → ℂ) :
    finiteProjectiveSource M k (extendMaterial N M v) = finiteProjectiveSource N k v := by
  rw [← physicalCompletedFiniteSource_fin, ← physicalCompletedFiniteSource_fin,
    finRadialCoefficients_extend N M hNM]

/-- The positive material-address convention already used by the native
Cauchy lift: m maps to radial degree m-1, and the zero atom is separate. -/
def materialStencilPolynomial : FormalStencil →ₗ[ℤ] ℂ[X] :=
  Finsupp.linearCombination ℤ
    (fun m => if m = 0 then 0 else monomial (m-1) (1 : ℂ))

theorem materialStencilPolynomial_atom (j : ℕ) :
    materialStencilPolynomial (atom (j+1)) = X^j := by
  simp [materialStencilPolynomial, atom, ← C_mul_X_pow_eq_monomial]

theorem materialStencilPolynomial_bracket (p r : ℕ) :
    materialStencilPolynomial (centeredBracketStencil (p+r+1) r) =
      X^p * (1-X^r)^2 := by
  have hl : p+r+1-r = p+1 := by omega
  have hr : p+r+1+r = (p+2*r)+1 := by omega
  rw [centeredBracketStencil, map_add, map_sub, map_nsmul, hl, hr,
    materialStencilPolynomial_atom, materialStencilPolynomial_atom,
    materialStencilPolynomial_atom]
  simp only [nsmul_eq_mul, pow_add, pow_mul]
  ring

theorem materialStencilPolynomial_camera (b M : ℕ) :
    materialStencilPolynomial (finiteStencil b M) = materialStencilPolynomial (seedStencil b) +
      ∑ a ∈ Finset.range M, materialStencilPolynomial (centerStencil b a) := by
  simp [finiteStencil]

/-- A guaranteed even coordinate window, derived from the material degree. -/
def materialStencilHalfWindow (s : FormalStencil) : ℕ :=
  (materialStencilPolynomial s).natDegree + 1

def materialStencilCoefficients (s : FormalStencil) :
    Fin (2*materialStencilHalfWindow s) → ℂ :=
  fun j => (materialStencilPolynomial s).coeff j

theorem materialStencilCoefficients_polynomial (s : FormalStencil) :
    materialPolynomial (2*materialStencilHalfWindow s) (materialStencilCoefficients s) =
      materialStencilPolynomial s := by
  change ofFn (2*materialStencilHalfWindow s)
    (toFn (2*materialStencilHalfWindow s) (materialStencilPolynomial s)) = _
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  change (materialStencilPolynomial s).natDegree < 2*((materialStencilPolynomial s).natDegree+1)
  omega

/-- Applied to the literal producer, with its independently synthesized
polynomial and all original Green residuals. -/
theorem materialStencil_physicalFiniteSewing (s : FormalStencil) (k : ℕ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow s) k
      (physicalEndpointJetInput (2*materialStencilHalfWindow s) k (materialStencilCoefficients s)) =
        finiteProjectiveSource (2*materialStencilHalfWindow s) k (materialStencilCoefficients s) ∧
    finiteProjectiveSource (2*materialStencilHalfWindow s) k (materialStencilCoefficients s) =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s)) +
         physicalGreenResidualNumerator q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s))) :=
  physicalFiniteSewing_capstone _ k _ q hq0 hq1

theorem originalBracket_physicalFiniteSewing (p r k : ℕ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    let s := centeredBracketStencil (p+r+1) r
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow s) k
      (physicalEndpointJetInput (2*materialStencilHalfWindow s) k (materialStencilCoefficients s)) =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s)) +
         physicalGreenResidualNumerator q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s))) := by
  exact (materialStencil_physicalFiniteSewing _ k q hq0 hq1).1.trans
    (materialStencil_physicalFiniteSewing _ k q hq0 hq1).2

theorem originalCamera_physicalFiniteSewing (b M k : ℕ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    let s := finiteStencil b M
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow s) k
      (physicalEndpointJetInput (2*materialStencilHalfWindow s) k (materialStencilCoefficients s)) =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s)) +
         physicalGreenResidualNumerator q k
          (finRadialCoefficients (2*materialStencilHalfWindow s) (materialStencilCoefficients s))) := by
  exact (materialStencil_physicalFiniteSewing _ k q hq0 hq1).1.trans
    (materialStencil_physicalFiniteSewing _ k q hq0 hq1).2

theorem physicalEndpointJetInput_extended_last_zero (N k : ℕ) (v : Fin N → ℂ) :
    physicalEndpointJetInput (N+1) k (extendMaterial N (N+1) v) ⟨N, by omega⟩ = 0 := by
  change endpointGauge k N * _ = 0
  rw [materialPolynomial_extend N (N+1) (by omega)]
  have hd := Polynomial.iterate_derivative_eq_zero_of_degree_lt
    (Polynomial.ofFn_degree_lt v)
  simp only [materialPolynomial, hd, eval_zero, mul_zero]

theorem finRadialCoefficients_coeff (N : ℕ) (v : Fin N → ℂ) (j : ℕ) :
    finRadialCoefficients N v j = (materialPolynomial N v).coeff j := by
  by_cases hj : j < N
  · rw [finRadialCoefficients_apply N v ⟨j, hj⟩]
    exact (Polynomial.ofFn_coeff_eq_val_of_lt v hj).symm
  · rw [finRadialCoefficients_outside N v j (by omega)]
    exact (Polynomial.ofFn_coeff_eq_zero_of_ge v (by omega)).symm

theorem finiteTrace0_polynomial (N : ℕ) (v : Fin N → ℂ) :
    finiteTrace0 (finRadialCoefficients N v) = (materialPolynomial N v).eval 0 := by
  rw [finiteTrace0, finRadialCoefficients_coeff, Polynomial.coeff_zero_eq_eval_zero]

theorem finiteTrace1_polynomial (N : ℕ) (v : Fin N → ℂ) (q : ℝ) :
    finiteTrace1 q (finRadialCoefficients N v) =
      (q : ℂ)⁻¹ * (materialPolynomial N v).derivative.eval 0 -
        (materialPolynomial N v).eval 0 := by
  unfold finiteTrace1
  simp only [finRadialCoefficients_coeff, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative, Nat.cast_zero, zero_add, mul_one]

theorem finiteTraces_from_entireEndpointChart (N k : ℕ) (v : Fin N → ℂ) (q : ℝ) :
    finiteTrace0 (finRadialCoefficients N v) =
      (endpointTaylorPolynomial N k (physicalEndpointJetInput N k v)).eval 0 ∧
    finiteTrace1 q (finRadialCoefficients N v) =
      (q : ℂ)⁻¹ * (endpointTaylorPolynomial N k (physicalEndpointJetInput N k v)).derivative.eval 0 -
        (endpointTaylorPolynomial N k (physicalEndpointJetInput N k v)).eval 0 := by
  rw [endpointTaylorPolynomial_encode]
  exact ⟨finiteTrace0_polynomial N v, finiteTrace1_polynomial N v q⟩

/-- Literal smallest original positive-position bracket, extended to four
coefficients. This is extracted from the material producer. -/
def firstMaterialBracketCoefficients : Fin 4 → ℂ :=
  fun j => (materialStencilPolynomial (centeredBracketStencil 2 1)).coeff j

theorem firstMaterialBracket_polynomial :
    materialPolynomial 4 firstMaterialBracketCoefficients = (1-X)^2 := by
  have hp := materialStencilPolynomial_bracket 0 1
  norm_num at hp
  have hv : firstMaterialBracketCoefficients = ![1,-2,1,0] := by
    funext j
    have hp' : materialStencilPolynomial (centeredBracketStencil 2 1) =
        1 - 2*X + X^2 := by rw [hp]; ring
    fin_cases j <;> norm_num [firstMaterialBracketCoefficients, hp',
      Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [hv, materialPolynomial, Polynomial.ofFn_eq_sum_monomial]
  simp [Fin.sum_univ_succ, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.C_ofNat]
  ring

theorem firstMaterialBracket_endpoint_canary (k : ℕ) :
    physicalEndpointJetInput 4 k firstMaterialBracketCoefficients =
      ![0,0,2/((k : ℂ)+1)^2,0] := by
  funext a
  change endpointGauge k a *
    ((Polynomial.derivative^[a.val]) (materialPolynomial 4 firstMaterialBracketCoefficients)).eval 1 = _
  rw [firstMaterialBracket_polynomial]
  fin_cases a <;>
    norm_num [Function.iterate_succ_apply, Polynomial.derivative_sub,
      Polynomial.derivative_pow, endpointGauge, nativeSourceJetOrderPhase,
      canonicalCompletedC3RadialSecondStep, canonicalGreenJetStep]
  rw [mul_pow, Complex.I_sq]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end
end CarrySelfAdjointOperator.PhysicalSewing
