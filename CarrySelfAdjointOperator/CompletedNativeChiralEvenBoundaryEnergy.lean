import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Raw finite limiting Green boundary energy

This names exactly the existing alternating tower on zero-extended boundary
coordinates. It is not the finite-step storage and does not remove its
higher-coordinate crosses or analytic remainder. No new metric is defined.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The old raw alternating boundary expression, at arbitrary finite order. -/
def nativeSourceFiniteBoundaryEnergy (N : ℕ) (x : Fin N → ℂ) : ℝ :=
  let b : ℕ → ℂ := fun a => if ha : a < N then x ⟨a,ha⟩ else 0
  2 * (∑ j ∈ Finset.range N, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
    (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a * (conj (b a)*b (2*j-a)).re))

private theorem sum_even_antidiagonal (N : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ a b, N ≤ a ∨ N ≤ b → f a b = 0) :
    (∑ j ∈ Finset.range N, ∑ a ∈ Finset.range (2*j+1), f a (2*j-a)) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        if Even (a+b) then f a b else 0 := by
  classical
  let T := (Finset.range N).sigma (fun j => Finset.range (2*j+1))
  let L := T.filter (fun ja => ja.2 < N ∧ 2*ja.1-ja.2 < N)
  let R := ((Finset.range N) ×ˢ (Finset.range N)).filter (fun ab => Even (ab.1+ab.2))
  have hL : (∑ ja ∈ T, f ja.2 (2*ja.1-ja.2)) =
      ∑ ja ∈ L, f ja.2 (2*ja.1-ja.2) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ja hT hj
    have hn : ¬(ja.2 < N ∧ 2*ja.1-ja.2 < N) := by
      intro hh
      exact hj (Finset.mem_filter.mpr ⟨hT,hh⟩)
    apply hf
    omega
  have hb : (∑ ja ∈ L, f ja.2 (2*ja.1-ja.2)) = ∑ ab ∈ R, f ab.1 ab.2 := by
    apply Finset.sum_bij (fun ja _ => (ja.2,2*ja.1-ja.2))
    · intro ja hja
      have hj := (Finset.mem_filter.mp hja).1
      have hs := Finset.mem_sigma.mp hj
      have ha := Finset.mem_range.mp hs.2
      have hh := (Finset.mem_filter.mp hja).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hh.1,Finset.mem_range.mpr hh.2⟩,?_⟩
      exact ⟨ja.1, by omega⟩
    · intro ja hja jb hjb he
      have ha := Finset.mem_range.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp hja).1).2
      have hb := Finset.mem_range.mp (Finset.mem_sigma.mp (Finset.mem_filter.mp hjb).1).2
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      apply Sigma.ext
      · dsimp only at h1 h2
        omega
      · simpa using h1
    · intro ab hab
      obtain ⟨hmem,j,hj⟩ := Finset.mem_filter.mp hab
      have ha := Finset.mem_range.mp (Finset.mem_product.mp hmem).1
      have hb := Finset.mem_range.mp (Finset.mem_product.mp hmem).2
      refine ⟨⟨j,ab.1⟩,?_,?_⟩
      · apply Finset.mem_filter.mpr
        dsimp only
        refine ⟨Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by dsimp only; omega),Finset.mem_range.mpr (by dsimp only; omega)⟩,?_⟩
        constructor <;> omega
      · apply Prod.ext
        · rfl
        · dsimp only
          omega
    · intro ja _
      rfl
  calc
    _ = ∑ ja ∈ T, f ja.2 (2*ja.1-ja.2) := by rw [Finset.sum_sigma]
    _ = ∑ ja ∈ L, f ja.2 (2*ja.1-ja.2) := hL
    _ = ∑ ab ∈ R, f ab.1 ab.2 := hb
    _ = _ := by
      simp only [R, Finset.sum_filter, Finset.sum_product]

/-- Every ordered source cross is retained in the finite coefficient form. -/
theorem nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum (N : ℕ) (x : Fin N → ℂ) :
    nativeSourceFiniteBoundaryEnergy N x =
      ∑ a : Fin N, ∑ b : Fin N,
        if Even ((a : ℕ)+(b : ℕ)) then
          2 * (-1 : ℝ)^(((a : ℕ)+(b : ℕ))/2+(a : ℕ)) *
            nativeSourceOddBoundaryCoefficient (((a : ℕ)+(b : ℕ))/2) *
              (conj (x a)*x b).re else 0 := by
  let e : ℕ → ℂ := fun a => if ha : a < N then x ⟨a,ha⟩ else 0
  let f : ℕ → ℕ → ℝ := fun a b =>
    2 * (-1 : ℝ)^((a+b)/2+a) * nativeSourceOddBoundaryCoefficient ((a+b)/2) *
      (conj (e a)*e b).re
  have hz : ∀ a b, N ≤ a ∨ N ≤ b → f a b = 0 := by
    intro a b hab
    rcases hab with ha | hb
    · simp [f,e,show ¬a < N by omega]
    · simp [f,e,show ¬b < N by omega]
  have hs := sum_even_antidiagonal N f hz
  have he : nativeSourceFiniteBoundaryEnergy N x =
      ∑ j ∈ Finset.range N, ∑ a ∈ Finset.range (2*j+1), f a (2*j-a) := by
    unfold nativeSourceFiniteBoundaryEnergy
    dsimp only
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    have ht : a+(2*j-a)=2*j := by omega
    dsimp only [f]
    rw [ht,show 2*j/2=j by omega,pow_add]
    dsimp only [e]
    ring
  rw [he,hs]
  simp only [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a ha
  rw [dif_pos (Finset.mem_range.mp ha)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [dif_pos (Finset.mem_range.mp hb)]
  simp [f,e,Finset.mem_range.mp ha,Finset.mem_range.mp hb]
end
end CarrySelfAdjointOperator
