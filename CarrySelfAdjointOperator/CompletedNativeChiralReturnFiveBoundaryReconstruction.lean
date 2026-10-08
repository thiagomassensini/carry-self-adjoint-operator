import CarrySelfAdjointOperator.CompletedNativeChiralReturnFiveBoundaryFace

/-!
# Five-sample boundary reconstruction in the original radial geometry

The inverse is fixed by the radial node multipliers 1,2,3,4,5 and their Euler boundary
jets. No moment, metric fitting or source replacement enters this map.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false

/-- Arithmetic inverse of the Euler boundary map at nodes 1,2,3,4,5. -/
def radialFiveBoundaryInverseCoefficients : Fin 5 → Fin 5 → ℝ :=
  ![![5, -77/12, 71/24, -7/12, 1/24],
    ![-10, 107/6, -59/6, 13/6, -1/6],
    ![10, -39/2, 49/4, -3, 1/4],
    ![-5, 61/6, -41/6, 11/6, -1/6],
    ![1, -25/12, 35/24, -5/12, 1/24]]

/-- Reconstruction from all five boundary coordinates, without compression. -/
def radialFiveBoundaryReconstruct (x : Fin 5 → ℂ) (i : Fin 5) : ℂ :=
  ∑ a : Fin 5, (radialFiveBoundaryInverseCoefficients i a : ℂ) * x a

/-- The five boundary jets of the reconstructed source are exactly its input. -/
theorem radialFiveBoundaryReconstruct_jets (x : Fin 5 → ℂ) (a : Fin 5) :
    radialEulerBoundaryJet (radialFiveBoundaryReconstruct x) a = x a := by
  fin_cases a <;>
    norm_num [radialEulerBoundaryJet, radialFiveBoundaryReconstruct,
      radialFiveBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- Conversely no source coefficient is lost in the complete five-jet map. -/
theorem radialFiveBoundaryReconstruct_source (d : Fin 5 → ℂ) :
    radialFiveBoundaryReconstruct (fun a : Fin 5 => radialEulerBoundaryJet d a) = d := by
  funext i
  fin_cases i <;>
    norm_num [radialEulerBoundaryJet, radialFiveBoundaryReconstruct,
      radialFiveBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- The canonical small radial scale weights boundary order a by h^(a : ℕ).
This is a coordinate change, not a new metric on the Cauchy source carrier. -/
def radialFiveScaledBoundary (h : ℝ) (d : Fin 5 → ℂ) (a : Fin 5) : ℂ :=
  ((h^(a : ℕ) : ℝ) : ℂ) * radialEulerBoundaryJet d a

/-- Exact inverse for nonzero radial steps. -/
def radialFiveNormalizedBoundaryInput (h : ℝ) (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  radialFiveBoundaryReconstruct (fun a : Fin 5 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * x a)

theorem radialFiveScaledBoundary_input (h : ℝ) (hh : h ≠ 0) (x : Fin 5 → ℂ) :
    radialFiveScaledBoundary h (radialFiveNormalizedBoundaryInput h x) = x := by
  funext a
  rw [radialFiveScaledBoundary, radialFiveNormalizedBoundaryInput,
    radialFiveBoundaryReconstruct_jets]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
  simp [hp]

theorem radialFiveNormalizedBoundaryInput_scaled (h : ℝ) (hh : h ≠ 0) (d : Fin 5 → ℂ) :
    radialFiveNormalizedBoundaryInput h (radialFiveScaledBoundary h d) = d := by
  have he : (fun a : Fin 5 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
      radialFiveScaledBoundary h d a) = (fun a : Fin 5 => radialEulerBoundaryJet d a) := by
    funext a
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
    simp [radialFiveScaledBoundary, hp]
  rw [radialFiveNormalizedBoundaryInput, he, radialFiveBoundaryReconstruct_source]

/-- Higher Euler boundary coordinates are determined by the same inverse,
not discarded. -/
def radialFiveHigherBoundaryCoefficient (m : ℕ) (a : Fin 5) : ℝ :=
  ∑ i : Fin 5, (((i : ℕ)+1 : ℕ) : ℝ)^m * radialFiveBoundaryInverseCoefficients i a

/-- Continuous regularization of EVERY higher boundary coordinate. -/
def radialFiveRegularizedBoundary (h : ℝ) (x : Fin 5 → ℂ) (m : ℕ) : ℂ :=
  if hm : m < 5 then x ⟨m, hm⟩ else
    ∑ a : Fin 5, ((h^(m-(a : ℕ)) * radialFiveHigherBoundaryCoefficient m a : ℝ) : ℂ) * x a

/-- Polynomial regularization of the full coefficient vector: h^4 d. -/
def radialFiveRegularizedInput (h : ℝ) (x : Fin 5 → ℂ) (i : Fin 5) : ℂ :=
  ∑ a : Fin 5, ((radialFiveBoundaryInverseCoefficients i a * h^(4-(a : ℕ)) : ℝ) : ℂ) * x a

theorem radialFiveRegularizedInput_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 5 → ℂ) (i : Fin 5) :
    radialFiveRegularizedInput h x i =
      ((h^4 : ℝ) : ℂ) * radialFiveNormalizedBoundaryInput h x i := by
  unfold radialFiveRegularizedInput radialFiveNormalizedBoundaryInput radialFiveBoundaryReconstruct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : h^(4-(a : ℕ)) * h^(a : ℕ) = h^4 := by rw [← pow_add]; congr 1; omega
  have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
  have he : h^(4-(a : ℕ)) = h^4 * (h^(a : ℕ))⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hpa).mpr
    exact hp
  rw [he]
  push_cast
  ring

theorem radialFiveRegularizedBoundary_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 5 → ℂ) (m : ℕ) :
    radialFiveRegularizedBoundary h x m =
      ((h^m : ℝ) : ℂ) * radialEulerBoundaryJet (radialFiveNormalizedBoundaryInput h x) m := by
  unfold radialFiveRegularizedBoundary
  split_ifs with hm
  · have hs := congrFun (radialFiveScaledBoundary_input h hh x) ⟨m, hm⟩
    simpa only [radialFiveScaledBoundary, Fin.val_mk] using hs.symm
  · unfold radialEulerBoundaryJet radialFiveNormalizedBoundaryInput radialFiveBoundaryReconstruct
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold radialFiveHigherBoundaryCoefficient
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    have hp : h^(m-(a : ℕ)) * h^(a : ℕ) = h^m := by rw [← pow_add]; congr 1; omega
    have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
    have he : h^(m-(a : ℕ)) = h^m * (h^(a : ℕ))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hpa).mpr hp
    rw [he]
    push_cast
    ring

theorem radialFiveRegularizedBoundary_zero (x : Fin 5 → ℂ) (m : ℕ) :
    radialFiveRegularizedBoundary 0 x m = nativeSourceFiveBoundaryExtension x m := by
  unfold radialFiveRegularizedBoundary nativeSourceFiveBoundaryExtension
  split_ifs with hm
  · rfl
  · apply Finset.sum_eq_zero
    intro a _
    have hp : m-(a : ℕ) ≠ 0 := by omega
    simp [hp]

end
end CarrySelfAdjointOperator
