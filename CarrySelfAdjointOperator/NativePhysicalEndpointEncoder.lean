import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Taylor

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators
open Polynomial
noncomputable section
set_option autoImplicit false

/-- The complete material polynomial, before the completed amplitude. -/
def materialPolynomial (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] ℂ[X] := Polynomial.ofFn N

def endpointGauge (k a : ℕ) : ℂ :=
  nativeSourceJetOrderPhase a * canonicalCompletedC3RadialSecondStep k ^ a

/-- Endpoint derivatives of polynomial representatives, not evaluation on Lp. -/
def physicalEndpointJetInput (N k : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun v a := endpointGauge k a *
    ((Polynomial.derivative^[a.val]) (materialPolynomial N v)).eval 1
  map_add' v w := by
    funext a
    simp only [map_add, ← Module.End.pow_apply, map_add, eval_add, mul_add, Pi.add_apply]
  map_smul' c v := by
    funext a
    simp only [map_smul, Polynomial.iterate_derivative_smul, eval_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem physicalEndpointJetInput_finite (N k : ℕ) (v : Fin N → ℂ) (a : Fin N) :
    physicalEndpointJetInput N k v a = endpointGauge k a *
      ∑ j : Fin N, (j.val.descFactorial a.val : ℂ) * v j := by
  change endpointGauge k a * _ = _
  rw [materialPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.iterate_derivative_sum]
  simp only [eval_finsetSum, ← C_mul_X_pow_eq_monomial,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem endpointDerivative_div_factorial (p : ℂ[X]) (a : ℕ) :
    ((Polynomial.derivative^[a]) p).eval 1 / (a.factorial : ℂ) =
      (Polynomial.taylor 1 p).coeff a := by
  rw [Polynomial.taylor_coeff]
  have h := congrArg (fun f : ℂ[X] → ℂ[X] => (f p).eval 1)
    (Polynomial.factorial_smul_hasseDeriv (R := ℂ) a)
  change (a.factorial • ((hasseDeriv a) p)).eval 1 = _ at h
  simp only [nsmul_eq_mul, eval_mul, eval_natCast] at h
  rw [← h]
  have hf : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  field_simp

theorem material_taylor_reconstruct (N : ℕ) (v : Fin N → ℂ) :
    (∑ a : Fin N, C ((taylor 1 (materialPolynomial N v)).coeff a) *
      (X - C 1)^a.val) = materialPolynomial N v := by
  have hs : (taylor 1 (materialPolynomial N v)).support ⊆ Finset.range N := by
    intro a ha
    have hd := Polynomial.le_degree_of_mem_supp a ha
    have hb : (materialPolynomial N v).degree < N := Polynomial.ofFn_degree_lt v
    rw [← Polynomial.degree_taylor (materialPolynomial N v) 1] at hb
    exact Finset.mem_range.mpr (by exact_mod_cast lt_of_le_of_lt hd hb)
  have h := Polynomial.sum_taylor_eq (materialPolynomial N v) (1 : ℂ)
  rw [Polynomial.sum_eq_of_subset (fun a c => C c * (X - C 1)^a)
    (by intro a; simp) hs] at h
  simpa only [← Fin.sum_univ_eq_sum_range] using h

theorem material_taylor_coeff (N : ℕ) (v : Fin N → ℂ) (j : Fin N) :
    (∑ a : Fin N, (taylor 1 (materialPolynomial N v)).coeff a *
      completedGreenForwardWeight a.val j.val) = v j := by
  have h := congrArg (fun p : ℂ[X] => p.coeff j.val) (material_taylor_reconstruct N v)
  simp only [finsetSum_coeff, coeff_C_mul] at h
  have hw (a : Fin N) : ((X - C 1 : ℂ[X])^a.val).coeff j.val =
      completedGreenForwardWeight a.val j.val := by
    rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
    simp [completedGreenForwardWeight]
  simp only [hw, materialPolynomial, ofFn_coeff_eq_val_of_lt v j.isLt] at h
  exact h

theorem nativeSourceJetOrderPhase_sq (a : ℕ) : nativeSourceJetOrderPhase a ^ 2 = 1 := by
  unfold nativeSourceJetOrderPhase
  rw [← Complex.ofReal_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem endpointGauge_ne_zero (k a : ℕ) : endpointGauge k a ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have hp := nativeSourceJetOrderPhase_sq a
    rw [h] at hp
    norm_num at hp
  · exact pow_ne_zero a (canonicalCompletedC3RadialSecondStep_ne_zero k)

/-- Reconstruction by the physical polynomial Taylor basis. -/
def endpointTaylorPolynomial (N k : ℕ) (x : Fin N → ℂ) : ℂ[X] :=
  ∑ a, C (x a / (endpointGauge k a * (a.val.factorial : ℂ))) * (X-C 1)^a.val

theorem endpointTaylorPolynomial_encode (N k : ℕ) (v : Fin N → ℂ) :
    endpointTaylorPolynomial N k (physicalEndpointJetInput N k v) = materialPolynomial N v := by
  rw [← material_taylor_reconstruct N v]
  unfold endpointTaylorPolynomial
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  change endpointGauge k a * _ / (endpointGauge k a * (a.val.factorial : ℂ)) = _
  rw [mul_div_mul_left _ _ (endpointGauge_ne_zero k a)]
  exact endpointDerivative_div_factorial _ a

theorem physicalEndpointJetInput_injective (N k : ℕ) :
    Function.Injective (physicalEndpointJetInput N k) := by
  intro v w h
  apply Polynomial.injective_ofFn N
  have he := congrArg (endpointTaylorPolynomial N k) h
  simpa only [endpointTaylorPolynomial_encode, materialPolynomial] using he

def decodedEndpointCoefficients (N k : ℕ) (x : Fin N → ℂ) : Fin N → ℂ :=
  fun j => (endpointTaylorPolynomial N k x).coeff j.val

theorem decodedEndpointCoefficients_encode (N k : ℕ) (v : Fin N → ℂ) :
    decodedEndpointCoefficients N k (physicalEndpointJetInput N k v) = v := by
  funext j
  simp only [decodedEndpointCoefficients, endpointTaylorPolynomial_encode, materialPolynomial,
    Polynomial.ofFn_coeff_eq_val_of_lt v j.isLt]

theorem physicalEndpointJetInput_decode (N k : ℕ) (x : Fin N → ℂ) :
    physicalEndpointJetInput N k (decodedEndpointCoefficients N k x) = x := by
  have hs : Function.Surjective (physicalEndpointJetInput N k) :=
    LinearMap.injective_iff_surjective.mp (physicalEndpointJetInput_injective N k)
  obtain ⟨v, rfl⟩ := hs x
  rw [decodedEndpointCoefficients_encode]

theorem physicalEndpointJetInput_factorials (N k : ℕ) (v : Fin N → ℂ) (a : Fin N) :
    physicalEndpointJetInput N k v a = endpointGauge k a *
      ∑ j : Fin N, if a.val ≤ j.val then
        (j.val.factorial : ℂ) / ((j.val-a.val).factorial : ℂ) * v j else 0 := by
  rw [physicalEndpointJetInput_finite]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a.val ≤ j.val
  · rw [if_pos hj]
    congr 1
    apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (j.val-a.val))).mpr
    rw [mul_comm]
    exact_mod_cast Nat.factorial_mul_descFactorial hj
  · rw [if_neg hj, Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hj)]
    simp

/-- Taylor, with the literal source phase and second-leg step. No amplitude
regularity or inverse source matrix enters this identity. -/
theorem physicalEndpointJetInput_nativeSourceInput (n k : ℕ) (v : Fin (2*n) → ℂ) :
    nativeSourceChiralJetInput n k (physicalEndpointJetInput (2*n) k v) =
      fun j : Fin (2*n) => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k j) * v j := by
  funext j
  change (∑ a : Fin (2*n), nativeSourceChiralJetInputMatrix n k j a *
    physicalEndpointJetInput (2*n) k v a) = _
  rw [← material_taylor_coeff (2*n) v j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hf : (a.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a.val
  have hh := pow_ne_zero a.val (canonicalCompletedC3RadialSecondStep_ne_zero k)
  have hp := nativeSourceJetOrderPhase_sq a.val
  have hd := endpointDerivative_div_factorial (materialPolynomial (2*n) v) a.val
  unfold nativeSourceChiralJetInputMatrix physicalEndpointJetInput endpointGauge
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hd]
  field_simp
  linear_combination
    completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j) *
      completedGreenForwardWeight a.val j.val *
      ((Polynomial.derivative^[a.val]) (materialPolynomial (2*n) v)).eval 1 * hp

def finiteProjectiveSource (N k : ℕ) (v : Fin N → ℂ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  ∑ j, v j • canonicalCompletedNativeRadialProjectiveChiralState k j

/-- Both original legs, with one occurrence of each completed amplitude. -/
theorem physicalEndpointJetInput_wholeSource (n k : ℕ) (v : Fin (2*n) → ℂ) :
    nativeSourceProjectiveBoundaryJetSynthesis n k
      (physicalEndpointJetInput (2*n) k v) = finiteProjectiveSource (2*n) k v := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    physicalEndpointJetInput_nativeSourceInput]
  unfold finiteProjectiveSource canonicalCompletedNativeRadialProjectiveChiralState
  simp only [smul_smul]
  apply Prod.ext
  · simp only [Prod.fst_sum, Prod.smul_fst, canonicalCompletedNativeRadialChiralDefectState,
      ChiralReturn.radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  · simp only [Prod.snd_sum, Prod.smul_snd, canonicalCompletedNativeRadialChiralDefectState,
      ChiralReturn.radialReturnedSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]

end
end CarrySelfAdjointOperator.PhysicalSewing
