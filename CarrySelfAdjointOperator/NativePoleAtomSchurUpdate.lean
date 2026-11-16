import CarrySelfAdjointOperator.NativePoleAtomCriticalEvaluation
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Tactic

/-!
# Schur pivots under the C2 pole-atom update

For an invertible prefix, a rank-one update changes both the last diagonal
and the prefix inverse. The exact pivot update is a fractional square. No
positivity hypothesis is used.
-/

namespace CarrySelfAdjointOperator

open scoped Matrix
noncomputable section
set_option autoImplicit false

/-- A not-necessarily-symmetric outer product. -/
def nativePoleOuterProduct {n : ℕ} (u v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * v j

private theorem nativePoleOuterProduct_mulVec {n : ℕ} (u v x : Fin n → ℝ) :
    nativePoleOuterProduct u v *ᵥ x = (dotProduct v x) • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, nativePoleOuterProduct, Pi.smul_apply]
  simp only [smul_eq_mul]
  change (∑ j : Fin n, (u i * v j) * x j) =
    (∑ j : Fin n, v j * x j) * u i
  calc
    _ = ∑ j : Fin n, (v j * x j) * u i := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [Finset.sum_mul]

private theorem nativePoleOuterSq_mulVec {n : ℕ} (u x : Fin n → ℝ) :
    outerSq u *ᵥ x = (dotProduct u x) • u := by
  change nativePoleOuterProduct u u *ᵥ x = _
  exact nativePoleOuterProduct_mulVec u u x

private theorem nativePoleMatrix_mulOuterProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    A * nativePoleOuterProduct u v =
      nativePoleOuterProduct (A *ᵥ u) v := by
  ext i j
  change (∑ k : Fin n, A i k * (u k * v j)) = _
  calc
    _ = (∑ k : Fin n, A i k * u k) * v j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (A *ᵥ u) i * v j := by simp [Matrix.mulVec, dotProduct]

private theorem nativePoleOuterProduct_mulMatrix {n : ℕ}
    (u v : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    nativePoleOuterProduct u v * A =
      nativePoleOuterProduct u (A.transpose *ᵥ v) := by
  ext i j
  change (∑ k : Fin n, (u i * v k) * A k j) = _
  calc
    _ = u i * (∑ k : Fin n, v k * A k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = u i * (A.transpose *ᵥ v) j := by
      change u i * (∑ k : Fin n, v k * A k j) =
        u i * (∑ k : Fin n, A k j * v k)
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The denominator in the Sherman--Morrison formula certifies that the
rank-one updated prefix remains invertible. -/
theorem nativePoleRankOneUpdate_isUnit {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (α : ℝ)
    (hA : IsUnit A) (hAsymm : A.transpose = A)
    (hden : 1 + α * dotProduct w (A⁻¹ *ᵥ w) ≠ 0) :
    IsUnit (A + α • outerSq w) := by
  letI := hA.invertible
  let z : Fin n → ℝ := A⁻¹ *ᵥ w
  let δ : ℝ := 1 + α * dotProduct w z
  let B : Matrix (Fin n) (Fin n) ℝ := A + α • outerSq w
  let C : Matrix (Fin n) (Fin n) ℝ :=
    A⁻¹ - (α / δ) • nativePoleOuterProduct z z
  have hδ : δ ≠ 0 := by simpa [δ, z] using hden
  have hsymmInv : A⁻¹.transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAsymm]
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_inv_of_invertible A
  have hAw : A *ᵥ z = w := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hOuterInv : outerSq w * A⁻¹ = nativePoleOuterProduct w z := by
    calc
      outerSq w * A⁻¹ = nativePoleOuterProduct w w * A⁻¹ := by
        change nativePoleOuterProduct w w * A⁻¹ = _
        rfl
      _ = nativePoleOuterProduct w (A⁻¹.transpose *ᵥ w) :=
        nativePoleOuterProduct_mulMatrix w w A⁻¹
      _ = nativePoleOuterProduct w z := by simp [z, hsymmInv]
  have hBw : B *ᵥ z = δ • w := by
    change (A + α • outerSq w) *ᵥ z = δ • w
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, nativePoleOuterSq_mulVec, hAw]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    simp [δ, z]
    ring
  have hBAinv : B * A⁻¹ = 1 + α • nativePoleOuterProduct w z := by
    change (A + α • outerSq w) * A⁻¹ = _
    rw [Matrix.add_mul, Matrix.smul_mul, hAAinv, hOuterInv]
  have hBOuter : B * nativePoleOuterProduct z z =
      δ • nativePoleOuterProduct w z := by
    change (A + α • outerSq w) * nativePoleOuterProduct z z = _
    rw [nativePoleMatrix_mulOuterProduct, hBw]
    ext i j
    simp [nativePoleOuterProduct, Pi.smul_apply]
    ring
  have hBC : B * C = 1 := by
    change B * (A⁻¹ - (α / δ) • nativePoleOuterProduct z z) = 1
    rw [Matrix.mul_sub, Matrix.mul_smul, hBAinv, hBOuter]
    simp only [smul_smul]
    have hscale : (α / δ) * δ = α := by
      field_simp [hδ]
    rw [hscale]
    module
  have hdet : B.det * C.det = 1 := by
    have h := congrArg Matrix.det hBC
    simpa [Matrix.det_mul] using h
  have hBdet : B.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdet
    norm_num at hdet
  apply (Matrix.isUnit_iff_isUnit_det B).2
  exact isUnit_iff_ne_zero.mpr hBdet

/-- Exact fractional change of the Schur pivot under a symmetric rank-one
update. The numerator uses the old critical direction; the denominator records
the change to the old prefix. -/
theorem nativePoleSchurRankOneUpdate
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b w : Fin n → ℝ)
    (d t α : ℝ) (hA : IsUnit A) (hAsymm : A.transpose = A)
    (hden : 1 + α * dotProduct w (A⁻¹ *ᵥ w) ≠ 0) :
    d + α * t ^ 2 -
        dotProduct (b + (α * t) • w)
          (((A + α • outerSq w)⁻¹) *ᵥ (b + (α * t) • w)) =
      (d - dotProduct b (A⁻¹ *ᵥ b)) +
        α * (t - dotProduct w (A⁻¹ *ᵥ b)) ^ 2 /
          (1 + α * dotProduct w (A⁻¹ *ᵥ w)) := by
  letI := hA.invertible
  let z : Fin n → ℝ := A⁻¹ *ᵥ w
  let u : Fin n → ℝ := A⁻¹ *ᵥ b
  let γ : ℝ := dotProduct w z
  let β : ℝ := dotProduct w u
  let δ : ℝ := 1 + α * γ
  let q : ℝ := t - β
  let A' : Matrix (Fin n) (Fin n) ℝ := A + α • outerSq w
  let b' : Fin n → ℝ := b + (α * t) • w
  let u' : Fin n → ℝ := u + (α * q / δ) • z
  have hδ : δ ≠ 0 := by simpa [δ, γ, z] using hden
  have hAu : A *ᵥ u = b := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hAz : A *ᵥ z = w := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hsymmInv : A⁻¹.transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAsymm]
  have hcross : dotProduct b z = β := by
    calc
      dotProduct b z = dotProduct w (A⁻¹.transpose *ᵥ b) :=
        (Matrix.dotProduct_transpose_mulVec A⁻¹ w b).symm
      _ = β := by simp [β, u, hsymmInv]
  have hA'unit := nativePoleRankOneUpdate_isUnit A w α hA hAsymm hden
  letI := hA'unit.invertible
  have hA'u : A' *ᵥ u = b + (α * β) • w := by
    change (A + α • outerSq w) *ᵥ u = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, nativePoleOuterSq_mulVec, hAu]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    simp [β, u]
    ring
  have hA'z : A' *ᵥ z = δ • w := by
    change (A + α • outerSq w) *ᵥ z = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, nativePoleOuterSq_mulVec, hAz]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    simp [δ, γ, z]
    ring
  have hkδ : (α * q / δ) * δ = α * q := by
    field_simp [hδ]
  have hsol : A' *ᵥ u' = b' := by
    change A' *ᵥ (u + (α * q / δ) • z) = b'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hA'u, hA'z]
    have hq : β + q = t := by simp [q]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_smul]
    dsimp [b']
    have hscalar : α * β * w i + (α * q / δ * δ) * w i = α * t * w i := by
      calc
        _ = α * (β + q) * w i := by rw [hkδ]; ring
        _ = _ := by rw [hq]
    calc
      _ = b i + (α * β * w i + (α * q / δ * δ) * w i) := by ring
      _ = _ := by rw [hscalar]
  have hsolve : A'⁻¹ *ᵥ b' = u' := by
    calc
      A'⁻¹ *ᵥ b' = A'⁻¹ *ᵥ (A' *ᵥ u') := by rw [hsol]
      _ = (A'⁻¹ * A') *ᵥ u' := by rw [Matrix.mulVec_mulVec]
      _ = u' := by rw [Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hschurEval :
      dotProduct b' (A'⁻¹ *ᵥ b') =
        dotProduct b u + (α * q / δ) * β +
          α * t * β + α * t * (α * q / δ) * γ := by
    rw [hsolve]
    change dotProduct (b + (α * t) • w) (u + (α * q / δ) • z) = _
    simp only [add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul]
    rw [hcross]
    simp only [β, γ, smul_eq_mul]
    ring
  have hq : β + q = t := by simp [q]
  calc
    _ = d + α * t ^ 2 -
          (dotProduct b u + (α * q / δ) * β +
            α * t * β + α * t * (α * q / δ) * γ) := by rw [hschurEval]
    _ = (d - dotProduct b u) + α * q ^ 2 / δ := by
      have hβ : β = t - q := by linarith [hq]
      rw [hβ]
      field_simp [hδ]
      ring
    _ = (d - dotProduct b (A⁻¹ *ᵥ b)) +
          α * (t - dotProduct w (A⁻¹ *ᵥ b)) ^ 2 /
            (1 + α * dotProduct w (A⁻¹ *ᵥ w)) := by
      simp [u, q, β, δ, γ, z]

/-- Sector mass of the raw pole atom. The shift by `s` multiplies its mass at
`-4` by `(-4)^s`; thus the two canonical sectors have coefficients `4` and
`-16`. -/
def nativePoleSectorMass (s : ℕ) : ℝ := 4 * (-4 : ℝ) ^ s

private theorem sourceMomentMatrix_add_nativePoleAtom
    (m : ℕ → ℝ) (s n : ℕ) :
    sourceMomentMatrix (fun k => m k + 4 * (-4 : ℝ) ^ k) s n =
      sourceMomentMatrix m s n +
        nativePoleSectorMass s • outerSq (poleAtomVector n) := by
  ext i j
  simp [sourceMomentMatrix, nativePoleSectorMass, poleAtomVector,
    outerSq, pow_add, Nat.add_assoc, smul_eq_mul]
  ring

private theorem sourceMomentCoupling_add_nativePoleAtom
    (m : ℕ → ℝ) (s n : ℕ) :
    sourceMomentCoupling (fun k => m k + 4 * (-4 : ℝ) ^ k) s n =
      sourceMomentCoupling m s n +
        (nativePoleSectorMass s * (-4 : ℝ) ^ n) • poleAtomVector n := by
  funext i
  simp [sourceMomentCoupling, nativePoleSectorMass, poleAtomVector,
    pow_add, Nat.add_assoc, smul_eq_mul]
  ring

private theorem sourceMomentDiagonal_add_nativePoleAtom
    (m : ℕ → ℝ) (s n : ℕ) :
    (fun k => m k + 4 * (-4 : ℝ) ^ k) (2*n+s) =
      m (2*n+s) + nativePoleSectorMass s * ((-4 : ℝ) ^ n) ^ 2 := by
  have hpow : (-4 : ℝ) ^ (2*n+s) = (-4 : ℝ) ^ s * ((-4 : ℝ) ^ n) ^ 2 := by
    have hexp : 2*n+s = s+n+n := by omega
    rw [hexp]
    calc
      (-4 : ℝ) ^ (s+n+n) = (-4 : ℝ) ^ (s+n) * (-4 : ℝ) ^ n := by
        rw [pow_add]
      _ = (-4 : ℝ) ^ s * ((-4 : ℝ) ^ n) ^ 2 := by
        rw [pow_add]
        ring
  change m (2*n+s) + 4 * (-4 : ℝ) ^ (2*n+s) = _
  rw [hpow]
  simp [nativePoleSectorMass]
  ring

/-- Exact change in the source Hankel Schur pivot after adding the raw C2 pole
atom. This is the pivot-level Sherman--Morrison identity: the critical
polynomial evaluation is squared, while the denominator records the update to
the prefix itself. The only assumptions are invertibility and symmetry of the
old prefix and nonvanishing of the update denominator; no positivity is used. -/
theorem sourceMomentSchur_add_nativePoleAtom
    (m : ℕ → ℝ) (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m s n))
    (hden : 1 + nativePoleSectorMass s *
        dotProduct (poleAtomVector n)
          ((sourceMomentMatrix m s n)⁻¹ *ᵥ poleAtomVector n) ≠ 0) :
    sourceMomentSchur (fun k => m k + 4 * (-4 : ℝ) ^ k) s n =
      sourceMomentSchur m s n +
        nativePoleSectorMass s *
          ((-4 : ℝ) ^ n - dotProduct (poleAtomVector n)
            ((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n)) ^ 2 /
          (1 + nativePoleSectorMass s *
            dotProduct (poleAtomVector n)
              ((sourceMomentMatrix m s n)⁻¹ *ᵥ poleAtomVector n)) := by
  let A := sourceMomentMatrix m s n
  let b := sourceMomentCoupling m s n
  let w := poleAtomVector n
  let t := (-4 : ℝ) ^ n
  let α := nativePoleSectorMass s
  have hdiag : 4 * (-4 : ℝ) ^ (s+n*2) = α * ((-4 : ℝ) ^ n) ^ 2 := by
    have hpow : (-4 : ℝ) ^ (2*n+s) = (-4 : ℝ) ^ s * ((-4 : ℝ) ^ n) ^ 2 := by
      have hexp : 2*n+s = s+n+n := by omega
      rw [hexp]
      calc
        (-4 : ℝ) ^ (s+n+n) = (-4 : ℝ) ^ (s+n) * (-4 : ℝ) ^ n := by
          rw [pow_add]
        _ = (-4 : ℝ) ^ s * ((-4 : ℝ) ^ n) ^ 2 := by
          rw [pow_add]
          ring
    rw [show s+n*2 = 2*n+s by omega]
    rw [hpow]
    simp [α, nativePoleSectorMass]
    ring
  have hAsymm : A.transpose = A := by
    ext i j
    simp [A, sourceMomentMatrix, add_comm]
  have hden' : 1 + α * dotProduct w (A⁻¹ *ᵥ w) ≠ 0 := by
    simpa [A, w, α] using hden
  have h := nativePoleSchurRankOneUpdate A b w (m (2*n+s)) t α hA hAsymm hden'
  simpa [sourceMomentSchur, A, b, w, t, α,
    hdiag,
    sourceMomentMatrix_add_nativePoleAtom,
    sourceMomentCoupling_add_nativePoleAtom,
    sourceMomentDiagonal_add_nativePoleAtom,
    mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h

@[simp] theorem nativePoleSectorMass_even : nativePoleSectorMass 0 = 4 := by
  norm_num [nativePoleSectorMass]

@[simp] theorem nativePoleSectorMass_odd : nativePoleSectorMass 1 = -16 := by
  norm_num [nativePoleSectorMass]

/-- Append the monic leading coefficient to a finite vector. -/
def nativePoleMonicVector {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  @Fin.snoc n (fun _ : Fin (n+1) => ℝ) x (1 : ℝ)

/-- The monic critical Schur direction associated to the old solve vector. -/
def nativePoleCriticalVector {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  nativePoleMonicVector (-x)

/-- Evaluation of the monic critical vector at the pole `-4`. -/
def nativePoleCriticalEvaluation {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin (n+1), nativePoleCriticalVector x i * (-4 : ℝ) ^ (i : ℕ)

/-- The monic critical vector `Fin.snoc x 1` evaluated at the pole `-4` is
the last monomial plus the old-prefix pairing with the geometric atom. -/
theorem nativePoleSnocPolynomialEvaluation {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin (n+1),
      nativePoleMonicVector x i * (-4 : ℝ) ^ (i : ℕ)) =
      (-4 : ℝ) ^ n + dotProduct (poleAtomVector n) x := by
  classical
  unfold nativePoleMonicVector
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    Fin.snoc_castSucc, Fin.snoc_last]
  simp [dotProduct, poleAtomVector]
  ring_nf

/-- Evaluation of the actual old critical direction
`(-A⁻¹ b, 1)` at `-4` is the fractional pivot numerator. -/
theorem nativePoleCriticalPolynomialEvaluation {n : ℕ} (x : Fin n → ℝ) :
    nativePoleCriticalEvaluation x =
      (-4 : ℝ) ^ n - dotProduct (poleAtomVector n) x := by
  unfold nativePoleCriticalEvaluation
  rw [show nativePoleCriticalVector x = nativePoleMonicVector (-x) by rfl]
  rw [nativePoleSnocPolynomialEvaluation]
  simp [dotProduct, poleAtomVector, Finset.sum_neg_distrib]
  ring_nf

/-- The raw `Lambda` pivot is the canonical `xi` pivot plus the exact
fractional rank-one correction. In the numerator, the old critical direction
appears through its evaluation at `-4`. -/
theorem canonicalRawSourceMomentSchur_update
    (s n : ℕ)
    (hA : IsUnit
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n))
    (hden : 1 + nativePoleSectorMass s *
        dotProduct (poleAtomVector n)
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
            poleAtomVector n) ≠ 0) :
    sourceMomentSchur completedRawLogDerivativeMoment s n =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n +
        nativePoleSectorMass s *
          ((-4 : ℝ) ^ n - dotProduct (poleAtomVector n)
            ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
              sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n)) ^ 2 /
          (1 + nativePoleSectorMass s *
            dotProduct (poleAtomVector n)
              ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
                poleAtomVector n)) := by
  change sourceMomentSchur
      (fun k => canonicalCompletedNativeLogDerivativeMoment k + 4 * (-4 : ℝ) ^ k) s n = _
  exact sourceMomentSchur_add_nativePoleAtom
    canonicalCompletedNativeLogDerivativeMoment s n hA hden

/-- The same raw-versus-canonical pivot identity, with the numerator written
as the evaluation of the existing monic critical Schur direction. -/
theorem canonicalRawSourceMomentSchur_update_criticalPolynomial
    (s n : ℕ)
    (hA : IsUnit
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n))
    (hden : 1 + nativePoleSectorMass s *
        dotProduct (poleAtomVector n)
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
            poleAtomVector n) ≠ 0) :
    sourceMomentSchur completedRawLogDerivativeMoment s n =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n +
        nativePoleSectorMass s *
          nativePoleCriticalEvaluation
            ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
              sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n) ^ 2 /
          (1 + nativePoleSectorMass s *
            dotProduct (poleAtomVector n)
              ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
                poleAtomVector n)) := by
  have h := canonicalRawSourceMomentSchur_update s n hA hden
  have heval := nativePoleCriticalPolynomialEvaluation
    ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
      sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n)
  rw [← heval] at h
  exact h

/-- Even-sector instance: the pole atom adds mass `4` at `-4`. -/
theorem canonicalRawSourceMomentSchur_even_update
    (n : ℕ)
    (hA : IsUnit
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n))
    (hden : 1 + 4 * dotProduct (poleAtomVector n)
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)⁻¹ *ᵥ
          poleAtomVector n) ≠ 0) :
    sourceMomentSchur completedRawLogDerivativeMoment 0 n =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 n +
        4 * nativePoleCriticalEvaluation
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)⁻¹ *ᵥ
            sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 0 n) ^ 2 /
          (1 + 4 * dotProduct (poleAtomVector n)
            ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)⁻¹ *ᵥ
              poleAtomVector n)) := by
  have hden' : 1 + nativePoleSectorMass 0 *
      dotProduct (poleAtomVector n)
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n)⁻¹ *ᵥ
          poleAtomVector n) ≠ 0 := by simpa using hden
  simpa using canonicalRawSourceMomentSchur_update_criticalPolynomial 0 n hA hden'

/-- Odd-sector instance: the shifted pole atom has mass `-16` at `-4`.
No sign of the resulting correction follows without the denominator's sign. -/
theorem canonicalRawSourceMomentSchur_odd_update
    (n : ℕ)
    (hA : IsUnit
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n))
    (hden : 1 - 16 * dotProduct (poleAtomVector n)
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
          poleAtomVector n) ≠ 0) :
    sourceMomentSchur completedRawLogDerivativeMoment 1 n =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 n -
        16 * nativePoleCriticalEvaluation
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
            sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 n) ^ 2 /
          (1 - 16 * dotProduct (poleAtomVector n)
            ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
              poleAtomVector n)) := by
  have hden' : 1 + nativePoleSectorMass 1 *
      dotProduct (poleAtomVector n)
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
          poleAtomVector n) ≠ 0 := by
    have heq : 1 + nativePoleSectorMass 1 *
        dotProduct (poleAtomVector n)
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
            poleAtomVector n) =
        1 - 16 * dotProduct (poleAtomVector n)
          ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
            poleAtomVector n) := by simp [nativePoleSectorMass]; ring
    rw [heq]
    exact hden
  have h := canonicalRawSourceMomentSchur_update_criticalPolynomial 1 n hA hden'
  convert h using 1
  norm_num [nativePoleSectorMass]
  ring_nf

/-- Border a square matrix by one scalar coordinate. -/
def nativePoleBorderedMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (d : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks A (Matrix.replicateCol Unit b)
    (Matrix.replicateRow Unit b) (fun _ _ => d)

/-- Rank-one border atom on `Fin n ⊕ Unit`. -/
def nativePoleBorderedAtomMatrix {n : ℕ} (w : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.of fun i j => Sum.elim w (fun _ : Unit => t) i * Sum.elim w (fun _ : Unit => t) j

/-- Three-column factor for the border and pole-atom update over the invertible
base `diag(A,1)`. -/
def nativePoleBorderedDetLeft {n : ℕ} (b w : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin 3) ℝ := fun i j =>
  match i with
  | Sum.inl k => if j = 0 then w k else if j = 1 then b k else 0
  | Sum.inr _ => if j = 0 then t else if j = 2 then 1 else 0

/-- Three-row factor paired with `nativePoleBorderedDetLeft`. -/
def nativePoleBorderedDetRight {n : ℕ}
    (b w : Fin n → ℝ) (d t α : ℝ) :
    Matrix (Fin 3) (Fin n ⊕ Unit) ℝ := fun i j =>
  if i = 0 then
    match j with
    | Sum.inl k => α * w k
    | Sum.inr _ => α * t
  else if i = 1 then
    match j with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  else
    match j with
    | Sum.inl k => b k
    | Sum.inr _ => d - 1

private theorem nativePoleBorderedMatrix_rankThree_decomp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b w : Fin n → ℝ) (d t α : ℝ) :
    nativePoleBorderedMatrix A b d +
        α • nativePoleBorderedAtomMatrix w t =
      Matrix.fromBlocks A 0 0 (1 : Matrix Unit Unit ℝ) +
        nativePoleBorderedDetLeft b w t * nativePoleBorderedDetRight b w d t α := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [nativePoleBorderedMatrix, nativePoleBorderedDetLeft,
            nativePoleBorderedDetRight, Matrix.mul_apply,
            nativePoleBorderedAtomMatrix, Sum.elim, Fin.sum_univ_three]
          ring
      | inr j =>
          simp [nativePoleBorderedMatrix, nativePoleBorderedDetLeft,
            nativePoleBorderedDetRight, Matrix.mul_apply,
            nativePoleBorderedAtomMatrix, Sum.elim, Fin.sum_univ_three]
          ring
  | inr i =>
      cases j with
      | inl j =>
          simp [nativePoleBorderedMatrix, nativePoleBorderedDetLeft,
            nativePoleBorderedDetRight, Matrix.mul_apply,
            nativePoleBorderedAtomMatrix, Sum.elim, Fin.sum_univ_three]
          ring
      | inr j =>
          simp [nativePoleBorderedMatrix, nativePoleBorderedDetLeft,
            nativePoleBorderedDetRight, Matrix.mul_apply,
            nativePoleBorderedAtomMatrix, Sum.elim, Fin.sum_univ_three]
          ring

private theorem nativePoleTransposeMulVec_sum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (∑ i, (∑ j, y j * M j i) * x i) = dotProduct y (M *ᵥ x) := by
  calc
    (∑ i, (∑ j, y j * M j i) * x i) =
        dotProduct x (M.transpose *ᵥ y) := by
          calc
            _ = ∑ i, ∑ j, x i * (M j i * y j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = dotProduct x (M.transpose *ᵥ y) := by
              simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
              calc
                _ = ∑ i, x i * ∑ j, M j i * y j := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact (Finset.mul_sum _ _ _).symm
                _ = _ := rfl
    _ = dotProduct y (M *ᵥ x) := Matrix.dotProduct_transpose_mulVec M x y

private theorem nativePoleTransposeMulVec_scaled_sum {n : ℕ} (a : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (∑ i, (∑ j, a * y j * M j i) * x i) = a * dotProduct y (M *ᵥ x) := by
  calc
    (∑ i, (∑ j, a * y j * M j i) * x i) =
        ∑ i, a * ((∑ j, y j * M j i) * x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑ j, a * y j * M j i) * x i =
                (a * (∑ j, y j * M j i)) * x i := by
                  congr 1
                  calc
                    _ = ∑ j, a * (y j * M j i) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                    _ = a * ∑ j, y j * M j i := (Finset.mul_sum _ _ _).symm
            _ = a * ((∑ j, y j * M j i) * x i) := by ring
    _ = a * ∑ i, (∑ j, y j * M j i) * x i := (Finset.mul_sum _ _ _).symm
    _ = a * dotProduct y (M *ᵥ x) := by rw [nativePoleTransposeMulVec_sum]

/-- Division-free determinant identity for a bordered rank-one update. It
remains valid when the updated prefix is singular (`δ = 0`): only the original
prefix `A` must be invertible. -/
theorem nativePoleBorderedDet_noDivision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b w : Fin n → ℝ)
    (d t α : ℝ) (hA : IsUnit A) (hAsymm : A.transpose = A) :
    (nativePoleBorderedMatrix A b d + α • nativePoleBorderedAtomMatrix w t).det =
      A.det *
        ((1 + α * dotProduct w (A⁻¹ *ᵥ w)) *
            (d - dotProduct b (A⁻¹ *ᵥ b)) +
          α * (t - dotProduct w (A⁻¹ *ᵥ b)) ^ 2) := by
  let D : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
    Matrix.fromBlocks A 0 0 (1 : Matrix Unit Unit ℝ)
  let U := nativePoleBorderedDetLeft b w t
  let V := nativePoleBorderedDetRight b w d t α
  let γ := dotProduct w (A⁻¹ *ᵥ w)
  let β := dotProduct w (A⁻¹ *ᵥ b)
  let η := dotProduct b (A⁻¹ *ᵥ b)
  let K : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1 + α * (γ + t^2), α * β, α * t;
       t, 1, 1;
       β + (d - 1) * t, η, d]
  letI := hA.invertible
  have hInvSymm : A⁻¹.transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAsymm]
  have hCross : dotProduct b (A⁻¹ *ᵥ w) = β := by
    calc
      dotProduct b (A⁻¹ *ᵥ w) =
          dotProduct w (A⁻¹.transpose *ᵥ b) :=
        (Matrix.dotProduct_transpose_mulVec A⁻¹ w b).symm
      _ = β := by simp [β, hInvSymm]
  have hDdet : D.det = A.det := by
    simp [D]
  have hDunit : IsUnit D :=
    (Matrix.isUnit_iff_isUnit_det D).mpr (by
      rw [hDdet]
      exact (Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hDdetUnit : IsUnit D.det :=
    (Matrix.isUnit_iff_isUnit_det D).mp hDunit
  have hDinv : D⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 (1 : Matrix Unit Unit ℝ) := by
    letI := hDunit.invertible
    letI : Invertible (1 : Matrix Unit Unit ℝ) := IsUnit.invertible isUnit_one
    change (Matrix.fromBlocks A 0 0 (1 : Matrix Unit Unit ℝ))⁻¹ = _
    rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks_zero₂₁_eq]
    simp
  have hdecomp := nativePoleBorderedMatrix_rankThree_decomp A b w d t α
  have hK : 1 + V * D⁻¹ * U = K := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [K, U, V, D, hDinv, γ, β, η, hCross, Matrix.mul_apply,
        nativePoleBorderedDetLeft, nativePoleBorderedDetRight,
        nativePoleTransposeMulVec_scaled_sum, nativePoleTransposeMulVec_sum,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    all_goals ring
  calc
    _ = (D + U * V).det := by rw [hdecomp]
    _ = D.det * (1 + V * D⁻¹ * U).det := Matrix.det_add_mul U V hDdetUnit
    _ = A.det * ((1 + α * γ) * (d - η) + α * (t - β)^2) := by
      rw [hDdet, hK, Matrix.det_fin_three]
      change
        A.det * ((1 + α * (γ + t ^ 2)) * 1 * d -
            (1 + α * (γ + t ^ 2)) * 1 * η -
            α * β * t * d + α * β * 1 * (β + (d - 1) * t) +
            α * t * t * η - α * t * 1 * (β + (d - 1) * t)) = _
      ring

/-- At the singular-prefix value `δ = 0`, the full bordered determinant is
the rank-one cross term, with no division by `δ`. -/
theorem nativePoleBorderedDet_singularPrefix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b w : Fin n → ℝ)
    (d t α : ℝ) (hA : IsUnit A) (hAsymm : A.transpose = A)
    (hδ : 1 + α * dotProduct w (A⁻¹ *ᵥ w) = 0) :
    (nativePoleBorderedMatrix A b d + α • nativePoleBorderedAtomMatrix w t).det =
      A.det * (α * (t - dotProduct w (A⁻¹ *ᵥ b)) ^ 2) := by
  rw [nativePoleBorderedDet_noDivision A b w d t α hA hAsymm, hδ]
  ring

/-- A singular updated prefix does not force the full bordered block to be
singular: at `δ = 0`, nonzero atom mass and nonzero critical evaluation make
the complete block invertible. -/
theorem nativePoleBorderedMatrix_isUnit_of_singularPrefix
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b w : Fin n → ℝ)
    (d t α : ℝ) (hA : IsUnit A) (hAsymm : A.transpose = A)
    (hδ : 1 + α * dotProduct w (A⁻¹ *ᵥ w) = 0)
    (hα : α ≠ 0) (hcritical : t - dotProduct w (A⁻¹ *ᵥ b) ≠ 0) :
    IsUnit (nativePoleBorderedMatrix A b d + α • nativePoleBorderedAtomMatrix w t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply (isUnit_iff_ne_zero).2
  rw [nativePoleBorderedDet_singularPrefix A b w d t α hA hAsymm hδ]
  have hdetA : A.det ≠ 0 := by
    intro hz
    have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    simp [hz] at hunit
  exact mul_ne_zero hdetA (mul_ne_zero hα (pow_ne_zero 2 hcritical))

private theorem nativePoleDotProduct_sub_left {ι : Type*} [Fintype ι]
    (u v w : ι → ℝ) : dotProduct (u - v) w = dotProduct u w - dotProduct v w := by
  calc
    dotProduct (u - v) w = dotProduct w (u - v) := dotProduct_comm _ _
    _ = dotProduct w u - dotProduct w v := dotProduct_sub _ _ _
    _ = dotProduct u w - dotProduct v w := by
      rw [dotProduct_comm w u, dotProduct_comm w v]

private theorem nativePoleDotProduct_smul_left {ι : Type*} [Fintype ι]
    (c : ℝ) (u v : ι → ℝ) : dotProduct (c • u) v = c * dotProduct u v := by
  calc
    dotProduct (c • u) v = dotProduct v (c • u) := dotProduct_comm _ _
    _ = c * dotProduct v u := by rw [dotProduct_smul]; simp
    _ = c * dotProduct u v := by rw [dotProduct_comm v u]

/-- In any positive-definite source prefix, a unit coordinate of the atom
forces its inverse quadratic mass to dominate the reciprocal diagonal entry.
This is the conditional matrix inequality behind the odd-sector signature test. -/
theorem nativePoleInverseQuadratic_lowerBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ) (i : ι) (a : ℝ)
    (hA : A.PosDef) (ha : A i i = a) (hw : w i = 1) (haPos : 0 < a) :
    1 / a ≤ dotProduct w (A⁻¹ *ᵥ w) := by
  letI := hA.isUnit.invertible
  have hAi : A⁻¹.PosDef := hA.inv
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hInvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hAsymm : A.transpose = A := by simpa using hA.isHermitian.eq
  have hInvSymm : A⁻¹.transpose = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAsymm]
  let e : ι → ℝ := Pi.single i 1
  let z : ι → ℝ := A *ᵥ e
  let v : ι → ℝ := w - (1 / a) • z
  have hAinvZ : A⁻¹ *ᵥ z = e := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, hInvA, Matrix.one_mulVec]
  have hwe : dotProduct w e = 1 := by
    change dotProduct w (Pi.single i 1) = 1
    rw [dotProduct_single]
    simp [hw]
  have hze : dotProduct z e = a := by
    change dotProduct (A *ᵥ Pi.single i 1) (Pi.single i 1) = a
    rw [dotProduct_single]
    simp [Matrix.mulVec_single, Matrix.col_apply, ha]
  have hcross : dotProduct z (A⁻¹ *ᵥ w) = 1 := by
    calc
      dotProduct z (A⁻¹ *ᵥ w) = dotProduct w (A⁻¹.transpose *ᵥ z) :=
        (Matrix.dotProduct_transpose_mulVec A⁻¹ w z).symm
      _ = dotProduct w e := by rw [hInvSymm, hAinvZ]
      _ = 1 := hwe
  have hquad : dotProduct v (A⁻¹ *ᵥ v) =
      dotProduct w (A⁻¹ *ᵥ w) - 1 / a := by
    change dotProduct (w - (1 / a) • z)
      (A⁻¹ *ᵥ (w - (1 / a) • z)) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAinvZ]
    rw [nativePoleDotProduct_sub_left, dotProduct_sub,
      nativePoleDotProduct_smul_left, dotProduct_sub, dotProduct_smul]
    simp [hwe, hze, hcross]
    field_simp [ne_of_gt haPos]
    all_goals simp
  have hnonneg : 0 ≤ dotProduct v (A⁻¹ *ᵥ v) := by
    by_cases hv : v = 0
    · simp [hv]
    · exact le_of_lt (hAi.dotProduct_mulVec_pos hv)
  rw [hquad] at hnonneg
  linarith

/-- Conditional odd-sector signature test. The source-level estimate
`1/h₁ ≤ wᵀ A⁻¹ w` together with `0 < h₁ < 16` forces the pole-atom update
denominator negative. The lower bound itself is a separate geometric obligation. -/
theorem nativePoleOddDelta_negative_of_lower_bound
    {h₁ q : ℝ} (h₁pos : 0 < h₁) (h₁lt : h₁ < 16)
    (hbound : 1 / h₁ ≤ q) : 1 - 16 * q < 0 := by
  have hrecip : (1 : ℝ) / 16 < 1 / h₁ :=
    (one_div_lt_one_div (by norm_num) h₁pos).2 h₁lt
  have hq : (1 : ℝ) / 16 < q := lt_of_lt_of_le hrecip hbound
  nlinarith

/-- Combining positive definiteness of a canonical prefix with the unit first
coordinate of the pole atom makes the odd rank-one denominator strictly
negative whenever the first diagonal moment lies in `(0,16)`. This detects the
signature change of the raw prefix, without asserting a sign for the canonical
Schur pivot. -/
theorem nativePoleOddDelta_negative_of_posDefPrefix {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (w : ι → ℝ)
    (i : ι) (h₁ : ℝ) (hA : A.PosDef) (hdiag : A i i = h₁)
    (hunitCoord : w i = 1) (h₁pos : 0 < h₁) (h₁lt : h₁ < 16) :
    1 - 16 * dotProduct w (A⁻¹ *ᵥ w) < 0 := by
  apply nativePoleOddDelta_negative_of_lower_bound h₁pos h₁lt
  exact nativePoleInverseQuadratic_lowerBound A w i h₁ hA hdiag hunitCoord h₁pos

/-- Odd canonical-source specialization: for every nonempty prefix, positive
definiteness and `0 < h₁ < 16` force the raw pole-atom update denominator to
be negative. This is a conditional signature statement; it assumes no Schur
pivot sign and does not assert all-order canonical positivity. -/
theorem canonicalOddPoleDenominator_negative_of_posDefPrefix
    (n : ℕ) (hn : 0 < n)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n).PosDef)
    (h₁pos : 0 < canonicalCompletedNativeLogDerivativeMoment 1)
    (h₁lt : canonicalCompletedNativeLogDerivativeMoment 1 < 16) :
    1 - 16 * dotProduct (poleAtomVector n)
      ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
        poleAtomVector n) < 0 := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hdiag :
      sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n i₀ i₀ =
        canonicalCompletedNativeLogDerivativeMoment 1 := by
    simp [sourceMomentMatrix, i₀]
  have hcoord : poleAtomVector n i₀ = 1 := by
    simp [poleAtomVector, i₀]
  exact nativePoleOddDelta_negative_of_posDefPrefix
    (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)
    (poleAtomVector n) i₀ (canonicalCompletedNativeLogDerivativeMoment 1)
    hA hdiag hcoord h₁pos h₁lt

end

end CarrySelfAdjointOperator
