import CarrySelfAdjointOperator.NativeCauchyLaguerreExactGram
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
open ChiralReturn
noncomputable section
set_option autoImplicit false

def matrixPairing {M : ℕ} (K : Matrix (Fin M) (Fin M) ℂ) (c d : Fin M → ℂ) : ℂ :=
  star c ⬝ᵥ (K *ᵥ d)

def laguerreReadout {M : ℕ} (r : ℕ) (c : Fin M → ℂ) : ℂ :=
  ∑ j : Fin M, (feature r j : ℂ) * c j

def returnedCoefficients (k : ℕ) {M : ℕ} (c : Fin M → ℂ) : Fin M → ℂ :=
  fun j => c j * completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k j)

def signedTail (R k : ℕ) {M : ℕ} (c d : Fin M → ℂ) : ℂ :=
  let K := tailDiagonal R M * cauchyMatrix M * tailDiagonal R M
  matrixPairing K c d - matrixPairing K (returnedCoefficients k c) (returnedCoefficients k d)

theorem head_matrixPairing (R M : ℕ) (c d : Fin M → ℂ) :
    matrixPairing ((featureMatrix R M)ᴴ * featureMatrix R M) c d =
      ∑ r : Fin (R+1), conj (laguerreReadout r c) * laguerreReadout r d := by
  unfold matrixPairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rfl

theorem matrixPairing_head_tail (R M : ℕ) (c d : Fin M → ℂ) :
    matrixPairing (cauchyMatrix M) c d =
      (∑ r : Fin (R+1), conj (laguerreReadout r c) * laguerreReadout r d) +
      matrixPairing (tailDiagonal R M * cauchyMatrix M * tailDiagonal R M) c d := by
  have h := congrArg (fun K => matrixPairing K c d) (exact_gram_head_tail R M)
  simp only [matrixPairing, Matrix.add_mulVec, dotProduct_add] at h
  change matrixPairing (cauchyMatrix M) c d =
    matrixPairing ((featureMatrix R M)ᴴ * featureMatrix R M) c d +
    matrixPairing (tailDiagonal R M * cauchyMatrix M * tailDiagonal R M) c d at h
  rw [head_matrixPairing] at h
  exact h

theorem incident_inner_eq_matrixPairing (k M : ℕ) (c d : Fin M → ℂ) :
    inner ℂ (radialIncidentSynthesis k M c) (radialIncidentSynthesis k M d) =
      ((k : ℂ)+1) * matrixPairing (cauchyMatrix M) c d := by
  simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_completedNativeRadialChiralCauchyState]
  simp only [matrixPairing, dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
    cauchyMatrix, cauchyEntry, Finset.mul_sum, Complex.ofReal_mul, Nat.cast_add,
    Nat.cast_ofNat, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Original signed form, independent inputs, both legs, and exact signed tail.
When `c` already contains the native amplitude, it is not applied again. -/
theorem original_signed_pairing_head_tail (R k M : ℕ) (c d : Fin M → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (radialIncidentSynthesis k M c, radialReturnedSynthesis k M c)
      (radialIncidentSynthesis k M d, radialReturnedSynthesis k M d) =
    (((k : ℂ)+1)/2) *
      ((∑ r : Fin (R+1),
        (conj (laguerreReadout r c) * laguerreReadout r d -
          conj (laguerreReadout r (returnedCoefficients k c)) *
            laguerreReadout r (returnedCoefficients k d))) + signedTail R k c d) := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  simp only [radialReturnedSynthesis_eq_incident_multiply]
  change (2 : ℂ)⁻¹ *
    (inner ℂ (radialIncidentSynthesis k M c) (radialIncidentSynthesis k M d) -
      inner ℂ (radialIncidentSynthesis k M (returnedCoefficients k c))
        (radialIncidentSynthesis k M (returnedCoefficients k d))) = _
  rw [incident_inner_eq_matrixPairing, incident_inner_eq_matrixPairing,
    matrixPairing_head_tail R M c d,
    matrixPairing_head_tail R M (returnedCoefficients k c) (returnedCoefficients k d)]
  rw [Finset.sum_sub_distrib]
  unfold signedTail
  ring

end
end CarrySelfAdjointOperator.NativeLaguerre
