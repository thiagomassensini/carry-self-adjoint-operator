import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import CarrySelfAdjointOperator.CompletedOperatorCharacteristic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# The pole atom and the rank-one Hankel perturbation

The reference completed characteristic is the *entire* Riemann `xi`, obtained
from `Lambda(s) = pi^{-s/2} Gamma(s/2) zeta(s)` by the archimedean prefactor
`(1/2) s (s-1)`.  In the centered height variable `s = 1/2 + i z`,

`(1/2) s (s-1) = -(1 + 4 z^2) / 8`,

so the characteristic factors as

`xi(z) = -(1 + 4 z^2) / 8 * Lambda(1/2 + i z)`.

The poles of `Lambda` at `s = 0, 1` sit at `z = ± i/2`, whose reciprocal square
is `1 / (i/2)^2 = -4`.  On the logarithmic-derivative moment side this pole pair
is a single **atom of mass 4 at the point `-4`**: the raw `Lambda` moments differ
from the dressed `xi` moments by the geometric sequence `4 (-4)^n`,

`h_n^Lambda = h_n^xi + 4 (-4)^n`.

Because `4 (-4)^{i+j} = 4 (-4)^i (-4)^j`, this atom is a rank-one perturbation of
each Hankel tower:

`G_N^Lambda = G_N^xi + 4 v_N v_Nᵀ`,   `K_N^Lambda = K_N^xi - 16 v_N v_Nᵀ`,

with `v_N = (1, -4, 16, …, (-4)^{N-1})ᵀ`.  The unshifted tower gains a positive
rank-one block (so raw `Lambda` stays positive there), while the shifted tower
loses one (so raw `Lambda` fails to be positive there — the atom sits at the
negative point `-4`).  Multiplying by `s (s-1)` to form `xi` cancels the poles
and removes the atom exactly; this is the concrete meaning of "dressing".

## Logical status

The scalar factorization and the rank-one Hankel/shifted-Hankel identities are
proved unconditionally here.  They are structural bookkeeping: they explain the
sign pattern observed numerically and pin down which sequence is the correct
target of positivity (the dressed `xi` moments, not the raw `Lambda` moments).
They do **not** prove positivity of either tower; the all-order positivity of the
dressed towers remains the RH-equivalent gate.
-/

open scoped ComplexConjugate Matrix

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## 1. The scalar pole factorization -/

/-- The uncompleted archimedean zeta characteristic `Lambda(1/2 + i z)`,
i.e. the completed characteristic with the `(1/2) s (s-1)` prefactor removed. -/
def completedRawZetaCharacteristic (z : ℂ) : ℂ :=
  Complex.exp (-(operatorHeightParameter z / 2) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (operatorHeightParameter z / 2) *
    nativeScalar (operatorHeightParameter z)

/-- The completed characteristic is the archimedean prefactor times the raw
`Lambda` characteristic. -/
theorem completedNativeOperatorCharacteristic_eq_prefactor_mul_raw (z : ℂ) :
    completedNativeOperatorCharacteristic z =
      (1 / 2 : ℂ) * operatorHeightParameter z *
          (operatorHeightParameter z - 1) *
        completedRawZetaCharacteristic z := by
  simp only [completedNativeOperatorCharacteristic, nativeXiCompletionFactor,
    completedRawZetaCharacteristic]
  ring

/-- In the centered height variable the archimedean prefactor is the pole
polynomial `-(1 + 4 z^2) / 8`. -/
theorem half_operatorHeightParameter_mul_sub_one (z : ℂ) :
    (1 / 2 : ℂ) * operatorHeightParameter z *
        (operatorHeightParameter z - 1) =
      -((1 + 4 * z ^ 2) / 8) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [operatorHeightParameter]
  linear_combination (z ^ 2 / 2) * hI

/-- **Scalar pole factorization.**  The completed characteristic is the pole
polynomial `-(1 + 4 z^2)/8` times the raw `Lambda` characteristic.  The pole
polynomial vanishes at `z = ± i/2`, the images of the `Lambda` poles `s = 0, 1`. -/
theorem completedNativeOperatorCharacteristic_eq_poleFactor_mul_raw (z : ℂ) :
    completedNativeOperatorCharacteristic z =
      -((1 + 4 * z ^ 2) / 8) * completedRawZetaCharacteristic z := by
  rw [completedNativeOperatorCharacteristic_eq_prefactor_mul_raw,
    half_operatorHeightParameter_mul_sub_one]

/-! ## 2. Geometric perturbation is a rank-one perturbation of both towers -/

/-- Outer product `v vᵀ` of a real vector with itself. -/
def outerSq {N : ℕ} (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => v i * v j

@[simp] theorem outerSq_apply {N : ℕ} (v : Fin N → ℝ) (i j : Fin N) :
    outerSq v i j = v i * v j :=
  rfl

/-- Adding a geometric sequence `c r^n` to a moment sequence adds a rank-one
block `c · v vᵀ` (with `v i = r^i`) to the unshifted Hankel tower. -/
theorem hankelGram_add_geometric
    (m : ℕ → ℝ) (c r : ℝ) (N : ℕ) :
    hankelGram (fun n => m n + c * r ^ n) N =
      hankelGram m N + c • outerSq (fun i : Fin N => r ^ (i : ℕ)) := by
  ext i j
  simp only [hankelGram_apply, Matrix.add_apply, Matrix.smul_apply, outerSq_apply,
    smul_eq_mul, pow_add]

/-- Adding a geometric sequence `c r^n` adds a rank-one block `(c r) · v vᵀ` to
the shifted Hankel tower: the shift multiplies the atom mass by its position `r`. -/
theorem shiftedHankel_add_geometric
    (m : ℕ → ℝ) (c r : ℝ) (N : ℕ) :
    shiftedHankel (fun n => m n + c * r ^ n) N =
      shiftedHankel m N + (c * r) • outerSq (fun i : Fin N => r ^ (i : ℕ)) := by
  ext i j
  simp only [shiftedHankel_apply, Matrix.add_apply, Matrix.smul_apply,
    outerSq_apply, smul_eq_mul, pow_add, pow_one]
  ring

/-- A nonnegative multiple of an outer square is positive semidefinite: it is
`A Aᴴ` for the rescaled column `A i _ = sqrt c · v i`. -/
theorem posSemidef_smul_outerSq {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (v : Fin N → ℝ) :
    (c • outerSq v).PosSemidef := by
  set A : Matrix (Fin N) (Fin 1) ℝ := fun i _ => Real.sqrt c * v i with hA
  have hAA : A * Aᴴ = c • outerSq v := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      Fin.sum_univ_one, hA, Matrix.smul_apply, outerSq_apply, smul_eq_mul]
    rw [show Real.sqrt c * v i * (Real.sqrt c * v j) =
        Real.sqrt c * Real.sqrt c * (v i * v j) by ring,
      Real.mul_self_sqrt hc]
  rw [← hAA]
  exact Matrix.posSemidef_self_mul_conjTranspose A

/-! ## 3. The pole factor's own logarithmic-derivative moment sequence -/

/-- Coefficient sequence of the pole polynomial `Phi(u) = 1 + 4 u`. -/
def poleFactorPhi : ℕ → ℝ
  | 0 => 1
  | 1 => 4
  | _ => 0

/-- The logarithmic-derivative moment sequence of the pole polynomial
`1 + 4 u` is exactly the geometric atom `-4 (-4)^n`.  This is the structural
source of the correction term: `-Phi'/Phi = -4/(1 + 4u) = -4 ∑ (-4)^n u^n`. -/
theorem isLogDerivativeMomentSequence_poleFactor :
    IsLogDerivativeMomentSequence poleFactorPhi (fun n => -4 * (-4 : ℝ) ^ n) := by
  intro n
  cases n with
  | zero => simp [poleFactorPhi]
  | succ j =>
    have hsum :
        ∑ k ∈ Finset.range (j + 1),
            (-4 * (-4 : ℝ) ^ k) * poleFactorPhi (j + 1 - k) =
          (-4 * (-4 : ℝ) ^ j) * 4 := by
      rw [Finset.sum_eq_single j]
      · have : j + 1 - j = 1 := by omega
        rw [this]; rfl
      · intro k hk hkj
        have hk' : k < j := by
          have := Finset.mem_range.mp hk; omega
        have : 2 ≤ j + 1 - k := by omega
        have hz : poleFactorPhi (j + 1 - k) = 0 := by
          rcases Nat.exists_eq_add_of_lt this with ⟨t, ht⟩
          rw [show j + 1 - k = t + 2 by omega]; rfl
        rw [hz, mul_zero]
      · intro hj; exact absurd (Finset.self_mem_range_succ j) hj
    have hpoleSucc : poleFactorPhi (j + 1 + 1) = 0 := by
      rw [show j + 1 + 1 = j + 2 by omega]; rfl
    have hpole0 : poleFactorPhi 0 = 1 := rfl
    rw [hpole0, hsum, hpoleSucc]
    ring

/-! ## 4. Raw vs dressed moments and their Hankel towers -/

/-- The raw `Lambda` logarithmic-derivative moments: the dressed `xi` moments
plus the pole atom of mass `4` at the point `-4`. -/
def completedRawLogDerivativeMoment (n : ℕ) : ℝ :=
  canonicalCompletedNativeLogDerivativeMoment n + 4 * (-4 : ℝ) ^ n

/-- Dressing removes the pole atom exactly, returning the canonical `xi`
moments. -/
@[simp] theorem completedRawLogDerivativeMoment_sub_atom (n : ℕ) :
    completedRawLogDerivativeMoment n - 4 * (-4 : ℝ) ^ n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  simp [completedRawLogDerivativeMoment]

/-- The canonical geometric vector `v_N = (1, -4, 16, …, (-4)^{N-1})ᵀ`. -/
def poleAtomVector (N : ℕ) : Fin N → ℝ := fun i => (-4 : ℝ) ^ (i : ℕ)

/-- **Rank-one identity, unshifted tower.**  `G_N^Lambda = G_N^xi + 4 v_N v_Nᵀ`. -/
theorem hankelGram_completedRaw_eq (N : ℕ) :
    hankelGram completedRawLogDerivativeMoment N =
      hankelGram canonicalCompletedNativeLogDerivativeMoment N +
        (4 : ℝ) • outerSq (poleAtomVector N) := by
  unfold completedRawLogDerivativeMoment poleAtomVector
  exact hankelGram_add_geometric _ 4 (-4) N

/-- **Rank-one identity, shifted tower.**  `K_N^Lambda = K_N^xi - 16 v_N v_Nᵀ`.
The shift multiplies the atom mass `4` by its position `-4`. -/
theorem shiftedHankel_completedRaw_eq (N : ℕ) :
    shiftedHankel completedRawLogDerivativeMoment N =
      shiftedHankel canonicalCompletedNativeLogDerivativeMoment N +
        (-16 : ℝ) • outerSq (poleAtomVector N) := by
  have h := shiftedHankel_add_geometric
    canonicalCompletedNativeLogDerivativeMoment 4 (-4) N
  rw [show ((4 : ℝ) * (-4)) = -16 by norm_num] at h
  unfold completedRawLogDerivativeMoment poleAtomVector
  exact h

/-- **Loewner consequence, unshifted tower.**  The raw `Lambda` unshifted
Hankel dominates the dressed `xi` one: the pole atom adds a positive rank-one
block, so positivity of the unshifted tower is *not* the discriminating gate. -/
theorem hankelGram_canonical_le_completedRaw (N : ℕ) :
    (hankelGram completedRawLogDerivativeMoment N -
      hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef := by
  rw [hankelGram_completedRaw_eq, add_sub_cancel_left]
  exact posSemidef_smul_outerSq (by norm_num : (0 : ℝ) ≤ 4) (poleAtomVector N)

/-- **Loewner consequence, shifted tower.**  The raw `Lambda` shifted Hankel is
dominated by the dressed `xi` one: the pole atom *subtracts* a positive rank-one
block.  This is the concrete reason raw `Lambda` fails shifted positivity while
dressed `xi` need not — the atom sits at the negative point `-4`. -/
theorem shiftedHankel_completedRaw_le_canonical (N : ℕ) :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N -
      shiftedHankel completedRawLogDerivativeMoment N).PosSemidef := by
  rw [shiftedHankel_completedRaw_eq]
  have heq : shiftedHankel canonicalCompletedNativeLogDerivativeMoment N -
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N +
        (-16 : ℝ) • outerSq (poleAtomVector N)) =
      (16 : ℝ) • outerSq (poleAtomVector N) := by
    module
  rw [heq]
  exact posSemidef_smul_outerSq (by norm_num : (0 : ℝ) ≤ 16) (poleAtomVector N)

end

end CarrySelfAdjointOperator
