import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiniteTransfer
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Exact algebraic Laguerre head and tail in the original radial Cauchy Gram.
`M` is the radial coefficient cutoff; `R` is the largest Laguerre order.
No assertion of Laguerre completeness or signed positivity is made here. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000

def rho (j : ℕ) : ℝ := (2 * j + 1) / (2 * j + 3)
def feature (r j : ℕ) : ℝ := 2 * rho j ^ r / (2 * j + 3)
def cauchyEntry (i j : ℕ) : ℝ := ((i : ℝ) + j + 2)⁻¹

theorem rho_pos (j : ℕ) : 0 < rho j := by unfold rho; positivity
theorem rho_lt_one (j : ℕ) : rho j < 1 := by
  unfold rho
  apply (div_lt_one (by positivity : (0 : ℝ) < 2 * j + 3)).mpr
  linarith

theorem rho_eq_original (j : ℕ) : rho j = ((j : ℝ) + 1/2) / (j + 3/2) := by
  unfold rho
  field_simp

theorem feature_eq_original (r j : ℕ) :
    feature r j = rho j ^ r / ((j : ℝ) + 3/2) := by
  unfold feature
  field_simp

theorem rho_eq_one_sub_inv (j : ℕ) :
    rho j = 1 - ((j : ℝ) + 3/2)⁻¹ := by
  rw [rho_eq_original]
  field_simp
  ring

/-- Finite polynomial moment identity; this is not yet an integral theorem. -/
theorem feature_polynomial_moment (r j : ℕ) :
    feature r j = ∑ a ∈ Finset.range (r+1),
      (-1 : ℝ)^a * (r.choose a : ℝ) * (((j : ℝ) + 3/2)⁻¹)^(a+1) := by
  rw [feature_eq_original, rho_eq_one_sub_inv, sub_eq_add_neg,
    add_comm (1 : ℝ), add_pow, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [neg_pow]
  simp only [one_pow, mul_one, pow_succ]
  ring

theorem cauchy_one_step (i j : ℕ) :
    cauchyEntry i j = feature 0 i * feature 0 j + rho i * rho j * cauchyEntry i j := by
  unfold cauchyEntry feature rho
  have hi : (2 * (i : ℝ) + 3) ≠ 0 := by positivity
  have hj : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  have hij : ((i : ℝ) + j + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem cauchy_head_tail_orders (n i j : ℕ) :
    cauchyEntry i j = (∑ r ∈ Finset.range n, feature r i * feature r j) +
      rho i ^ n * cauchyEntry i j * rho j ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs := cauchy_one_step i j
    have hf (a : ℕ) : feature n a = rho a ^ n * feature 0 a := by
      simp [feature]; ring
    rw [hf i, hf j, pow_succ, pow_succ]
    linear_combination ih + (rho i ^ n * rho j ^ n) * hs

def cauchyMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => (cauchyEntry i j : ℂ)
def featureMatrix (R M : ℕ) : Matrix (Fin (R+1)) (Fin M) ℂ :=
  fun r j => (feature r j : ℂ)
def tailDiagonal (R M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun j => (rho j ^ (R+1) : ℂ))

theorem cauchyMatrix_eq_gram (M : ℕ) :
    cauchyMatrix M = Matrix.gram ℂ (fun j : Fin M => completedNativeChiralCauchyFeature j) := by
  ext i j
  simp [cauchyMatrix, cauchyEntry, inner_completedNativeChiralCauchyFeature, Nat.cast_add]

theorem cauchyMatrix_posDef (M : ℕ) : (cauchyMatrix M).PosDef := by
  rw [cauchyMatrix_eq_gram]
  apply Matrix.posDef_gram_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have he : ChiralReturn.radialIncidentSynthesis 0 M c = 0 := by
    simpa [ChiralReturn.radialIncidentSynthesis, completedNativeRadialChiralCauchyState]
      using hc
  have hz := ChiralReturn.radialIncidentSynthesis_injective 0 M
    (he.trans (map_zero _).symm)
  intro i
  exact congrFun hz i

theorem exact_gram_head_tail (R M : ℕ) :
    cauchyMatrix M = (featureMatrix R M)ᴴ * featureMatrix R M +
      tailDiagonal R M * cauchyMatrix M * tailDiagonal R M := by
  ext i j
  simp [Matrix.mul_apply, tailDiagonal, featureMatrix, cauchyMatrix,
    RCLike.star_def, Matrix.diagonal_apply]
  have h := cauchy_head_tail_orders (R+1) i j
  exact_mod_cast (by simpa only [← Fin.sum_univ_eq_sum_range] using h)

theorem head_posSemidef (R M : ℕ) :
    ((featureMatrix R M)ᴴ * featureMatrix R M).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem tail_posSemidef (R M : ℕ) :
    (tailDiagonal R M * cauchyMatrix M * tailDiagonal R M).PosSemidef := by
  have h := (cauchyMatrix_posDef M).posSemidef.conjTranspose_mul_mul_same (tailDiagonal R M)
  have hd : (tailDiagonal R M)ᴴ = tailDiagonal R M := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [tailDiagonal, Matrix.conjTranspose_apply, RCLike.star_def]
    · simp [tailDiagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  simpa only [hd] using h

theorem tail_entry_tendsto_zero (i j : ℕ) :
    Tendsto (fun R : ℕ => rho i ^ (R+1) * cauchyEntry i j * rho j ^ (R+1)) atTop (nhds 0) := by
  have hi := (tendsto_pow_atTop_nhds_zero_of_lt_one (rho_pos i).le (rho_lt_one i)).comp
    (tendsto_add_atTop_nat 1)
  have hj := (tendsto_pow_atTop_nhds_zero_of_lt_one (rho_pos j).le (rho_lt_one j)).comp
    (tendsto_add_atTop_nat 1)
  simpa using (hi.mul_const (cauchyEntry i j)).mul hj

theorem head_entry_tendsto_cauchy (i j : ℕ) :
    Tendsto (fun R : ℕ => ∑ r ∈ Finset.range (R+1), feature r i * feature r j)
      atTop (nhds (cauchyEntry i j)) := by
  have he : (fun R : ℕ => ∑ r ∈ Finset.range (R+1), feature r i * feature r j) =
      (fun R => cauchyEntry i j - rho i ^ (R+1) * cauchyEntry i j * rho j ^ (R+1)) := by
    funext R
    linarith [cauchy_head_tail_orders (R+1) i j]
  rw [he]
  simpa using tendsto_const_nhds.sub (tail_entry_tendsto_zero i j)

end
end CarrySelfAdjointOperator.NativeLaguerre
