import CarrySelfAdjointOperator.FiveFieldStokesAdjointPoleAlgebra

/-!
# Exact two-jump tangent reconstruction

The residue reconstruction in `native_carry_chiral_endpoint_theorem.py`,
`scalar_from_H`. This is an invertible finite Laurent-coefficient map when
the two marked points are distinct and nonzero. No identification with an
actual parameter derivative or a symplectic pullback is assumed here.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

/-- The first three Laurent coefficients of the varying simple-pole part. -/
def twoJumpResidueMoments (t1 t2 : ℂ) (A : Fin 3 → TwoByTwo) : Fin 3 → TwoByTwo :=
  ![A 0 + A 1 + A 2, t1 • A 1 + t2 • A 2,
    t1 ^ 2 • A 1 + t2 ^ 2 • A 2]

/-- Exact formulas for `dA0,dA1,dA2` from the notes. -/
def twoJumpReconstructResidues (t1 t2 : ℂ) (T : Fin 3 → TwoByTwo) :
    Fin 3 → TwoByTwo :=
  let d1 := (t1 * (t2 - t1))⁻¹ • (t2 • T 1 - T 2)
  let d2 := (t2 * (t2 - t1))⁻¹ • (T 2 - t1 • T 1)
  ![T 0 - d1 - d2, d1, d2]

theorem twoJumpResidueMoments_reconstruct (t1 t2 : ℂ)
    (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (T : Fin 3 → TwoByTwo) :
    twoJumpResidueMoments t1 t2 (twoJumpReconstructResidues t1 t2 T) = T := by
  have hd : t2 - t1 ≠ 0 := sub_ne_zero.mpr h12
  ext k i j
  fin_cases k <;> simp [twoJumpResidueMoments, twoJumpReconstructResidues]
  all_goals field_simp
  all_goals ring

theorem twoJumpReconstructResidues_moments (t1 t2 : ℂ)
    (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A : Fin 3 → TwoByTwo) :
    twoJumpReconstructResidues t1 t2 (twoJumpResidueMoments t1 t2 A) = A := by
  have hd : t2 - t1 ≠ 0 := sub_ne_zero.mpr h12
  ext k i j
  fin_cases k <;> simp [twoJumpResidueMoments, twoJumpReconstructResidues]
  all_goals field_simp
  all_goals ring

/-- The coefficient conditions determine the residues, rather than merely
    being conditions satisfied by a chosen reconstruction. -/
theorem twoJumpResidueMoments_eq_iff (t1 t2 : ℂ)
    (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A T : Fin 3 → TwoByTwo) :
    twoJumpResidueMoments t1 t2 A = T ↔ A = twoJumpReconstructResidues t1 t2 T := by
  constructor
  · intro h
    rw [← h, twoJumpReconstructResidues_moments t1 t2 h1 h2 h12]
  · rintro rfl
    exact twoJumpResidueMoments_reconstruct t1 t2 h1 h2 h12 T

/-- Complex linearity is exact and does not require separation hypotheses. -/
def twoJumpReconstructResiduesLinear (t1 t2 : ℂ) :
    (Fin 3 → TwoByTwo) →ₗ[ℂ] (Fin 3 → TwoByTwo) where
  toFun := twoJumpReconstructResidues t1 t2
  map_add' A B := by
    ext k i j
    fin_cases k <;> simp [twoJumpReconstructResidues] <;> ring
  map_smul' c A := by
    ext k i j
    fin_cases k <;> simp [twoJumpReconstructResidues] <;> ring

/-- Laurent coefficients `T0,T1,T2` computed from the three Cauchy moments
    `H0,H1,H2`, with the normalization `κ` left explicit. -/
def twoJumpTangentLaurentCoefficients (κ t1 t2 : ℂ)
    (A H : Fin 3 → TwoByTwo) : Fin 3 → TwoByTwo :=
  let σ3 : TwoByTwo := !![1, 0; 0, -1]
  let L1 := A 0 + A 1 + A 2
  let L2 := t1 • A 1 + t2 • A 2
  ![(κ / 2) • matrixCommutator (H 0) σ3,
    κ • (H 0 + (1 / 2 : ℂ) • matrixCommutator (H 1) σ3 -
      matrixCommutator (H 0) L1),
    κ • ((2 : ℂ) • H 1 + (1 / 2 : ℂ) • matrixCommutator (H 2) σ3 -
      matrixCommutator (H 1) L1 - matrixCommutator (H 0) L2)]

set_option maxHeartbeats 800000 in
def twoJumpTangentLaurentLinear (κ t1 t2 : ℂ) (A : Fin 3 → TwoByTwo) :
    (Fin 3 → TwoByTwo) →ₗ[ℂ] (Fin 3 → TwoByTwo) where
  toFun := twoJumpTangentLaurentCoefficients κ t1 t2 A
  map_add' H K := by
    ext k i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [twoJumpTangentLaurentCoefficients, matrixCommutator,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  map_smul' c H := by
    ext k i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [twoJumpTangentLaurentCoefficients, matrixCommutator,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

/-- The actual reconstruction pipeline from the three Cauchy moments. -/
def twoJumpTangentResiduesLinear (κ t1 t2 : ℂ) (A : Fin 3 → TwoByTwo) :
    (Fin 3 → TwoByTwo) →ₗ[ℂ] (Fin 3 → TwoByTwo) :=
  (twoJumpReconstructResiduesLinear t1 t2).comp
    (twoJumpTangentLaurentLinear κ t1 t2 A)

theorem twoJumpTangentResiduesLinear_moments (κ t1 t2 : ℂ)
    (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h12 : t2 ≠ t1)
    (A H : Fin 3 → TwoByTwo) :
    twoJumpResidueMoments t1 t2 (twoJumpTangentResiduesLinear κ t1 t2 A H) =
      twoJumpTangentLaurentCoefficients κ t1 t2 A H :=
  twoJumpResidueMoments_reconstruct t1 t2 h1 h2 h12 _

/-- The four native coordinate variations used by `scalar_from_H`.
Division is totalized, just as in Lean's scalar field; interpreting these
as logarithmic derivatives additionally requires the three chart entries
to be nonzero. -/
def twoJumpResidueCoordinateLinear (A : Fin 3 → TwoByTwo) :
    (Fin 3 → TwoByTwo) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun dA := ![dA 1 0 1 / A 1 0 1 - dA 0 0 1 / A 0 0 1,
    dA 2 0 1 / A 2 0 1 - dA 0 0 1 / A 0 0 1, dA 1 0 0, dA 2 0 0]
  map_add' dA dB := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c dA := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Bilinear, not Hermitian: this is half of `uᵀ Ω w` in the notes. -/
def twoJumpRadialPairingLinear (u : Fin 4 → ℂ) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun w := (u 0 * w 2 + u 1 * w 3 - u 2 * w 0 - u 3 * w 1) / 2
  map_add' v w := by simp; ring
  map_smul' c w := by simp; ring

/-- The concrete scalar functional of the Cauchy moments, with all three
    reconstruction stages explicit. -/
def twoJumpScalarFromMoments (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ) : (Fin 3 → TwoByTwo) →ₗ[ℂ] ℂ :=
  (twoJumpRadialPairingLinear u).comp
    ((twoJumpResidueCoordinateLinear A).comp (twoJumpTangentResiduesLinear κ t1 t2 A))

theorem twoJumpScalarFromMoments_sum {ι : Type*} (s : Finset ι)
    (κ t1 t2 : ℂ) (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (H : ι → Fin 3 → TwoByTwo) :
    twoJumpScalarFromMoments κ t1 t2 A u (∑ i ∈ s, H i) =
      ∑ i ∈ s, twoJumpScalarFromMoments κ t1 t2 A u (H i) := by
  exact map_sum _ _ _

theorem twoJumpScalarFromMoments_smul (κ t1 t2 c : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ) (H : Fin 3 → TwoByTwo) :
    twoJumpScalarFromMoments κ t1 t2 A u (c • H) =
      c * twoJumpScalarFromMoments κ t1 t2 A u H := by
  exact map_smul _ _ _

end

end NativeCarryFiveFieldCapstone
