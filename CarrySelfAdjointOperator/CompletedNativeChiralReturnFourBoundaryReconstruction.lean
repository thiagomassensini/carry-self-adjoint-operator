import CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJets

/-!
# Four-sample boundary reconstruction in the original radial geometry

The inverse is fixed by the material nodes 1,2,3,4 and their Euler boundary
jets. No moment, metric fitting or source replacement enters this map.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false

/-- Arithmetic inverse of the Euler boundary map at nodes 1,2,3,4. -/
def radialFourBoundaryInverseCoefficients : Fin 4 → Fin 4 → ℝ :=
  ![![4, -13/3, 3/2, -1/6], ![-6, 19/2, -4, 1/2],
    ![4, -7, 7/2, -1/2], ![-1, 11/6, -1, 1/6]]

/-- Reconstruction from all four boundary coordinates, without compression. -/
def radialFourBoundaryReconstruct (x : Fin 4 → ℂ) (i : Fin 4) : ℂ :=
  ∑ a : Fin 4, (radialFourBoundaryInverseCoefficients i a : ℂ) * x a

/-- The four boundary jets of the reconstructed source are exactly its input. -/
theorem radialFourBoundaryReconstruct_jets (x : Fin 4 → ℂ) (a : Fin 4) :
    radialEulerBoundaryJet (radialFourBoundaryReconstruct x) a = x a := by
  fin_cases a <;>
    norm_num [radialEulerBoundaryJet, radialFourBoundaryReconstruct,
      radialFourBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- Conversely no source coefficient is lost in the complete four-jet map. -/
theorem radialFourBoundaryReconstruct_source (d : Fin 4 → ℂ) :
    radialFourBoundaryReconstruct (fun a : Fin 4 => radialEulerBoundaryJet d a) = d := by
  funext i
  fin_cases i <;>
    norm_num [radialEulerBoundaryJet, radialFourBoundaryReconstruct,
      radialFourBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- The canonical small radial scale weights boundary order a by h^(a : ℕ).
This is a coordinate change, not a new metric on the Cauchy source carrier. -/
def radialFourScaledBoundary (h : ℝ) (d : Fin 4 → ℂ) (a : Fin 4) : ℂ :=
  ((h^(a : ℕ) : ℝ) : ℂ) * radialEulerBoundaryJet d a

/-- Exact inverse for nonzero radial steps. -/
def radialFourNormalizedBoundaryInput (h : ℝ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  radialFourBoundaryReconstruct (fun a : Fin 4 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * x a)

theorem radialFourScaledBoundary_input (h : ℝ) (hh : h ≠ 0) (x : Fin 4 → ℂ) :
    radialFourScaledBoundary h (radialFourNormalizedBoundaryInput h x) = x := by
  funext a
  rw [radialFourScaledBoundary, radialFourNormalizedBoundaryInput,
    radialFourBoundaryReconstruct_jets]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
  simp [hp]

theorem radialFourNormalizedBoundaryInput_scaled (h : ℝ) (hh : h ≠ 0) (d : Fin 4 → ℂ) :
    radialFourNormalizedBoundaryInput h (radialFourScaledBoundary h d) = d := by
  have he : (fun a : Fin 4 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
      radialFourScaledBoundary h d a) = (fun a : Fin 4 => radialEulerBoundaryJet d a) := by
    funext a
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
    simp [radialFourScaledBoundary, hp]
  rw [radialFourNormalizedBoundaryInput, he, radialFourBoundaryReconstruct_source]

/-- Higher Euler boundary coordinates are determined by the same inverse,
not discarded. -/
def radialFourHigherBoundaryCoefficient (m : ℕ) (a : Fin 4) : ℝ :=
  ∑ i : Fin 4, (((i : ℕ)+1 : ℕ) : ℝ)^m * radialFourBoundaryInverseCoefficients i a

/-- Continuous regularization of EVERY higher boundary coordinate. -/
def radialFourRegularizedBoundary (h : ℝ) (x : Fin 4 → ℂ) (m : ℕ) : ℂ :=
  if hm : m < 4 then x ⟨m, hm⟩ else
    ∑ a : Fin 4, ((h^(m-(a : ℕ)) * radialFourHigherBoundaryCoefficient m a : ℝ) : ℂ) * x a

/-- Polynomial regularization of the full coefficient vector: h^3 d. -/
def radialFourRegularizedInput (h : ℝ) (x : Fin 4 → ℂ) (i : Fin 4) : ℂ :=
  ∑ a : Fin 4, ((radialFourBoundaryInverseCoefficients i a * h^(3-(a : ℕ)) : ℝ) : ℂ) * x a

theorem radialFourRegularizedInput_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 4 → ℂ) (i : Fin 4) :
    radialFourRegularizedInput h x i =
      ((h^3 : ℝ) : ℂ) * radialFourNormalizedBoundaryInput h x i := by
  unfold radialFourRegularizedInput radialFourNormalizedBoundaryInput radialFourBoundaryReconstruct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : h^(3-(a : ℕ)) * h^(a : ℕ) = h^3 := by rw [← pow_add]; congr 1; omega
  have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
  have he : h^(3-(a : ℕ)) = h^3 * (h^(a : ℕ))⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hpa).mpr
    exact hp
  rw [he]
  push_cast
  ring

theorem radialFourRegularizedBoundary_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 4 → ℂ) (m : ℕ) :
    radialFourRegularizedBoundary h x m =
      ((h^m : ℝ) : ℂ) * radialEulerBoundaryJet (radialFourNormalizedBoundaryInput h x) m := by
  unfold radialFourRegularizedBoundary
  split_ifs with hm
  · have hs := congrFun (radialFourScaledBoundary_input h hh x) ⟨m, hm⟩
    simpa only [radialFourScaledBoundary, Fin.val_mk] using hs.symm
  · unfold radialEulerBoundaryJet radialFourNormalizedBoundaryInput radialFourBoundaryReconstruct
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold radialFourHigherBoundaryCoefficient
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

theorem radialFourRegularizedBoundary_zero (x : Fin 4 → ℂ) (m : ℕ) :
    radialFourRegularizedBoundary 0 x m = nativeSourceFourBoundaryExtension x m := by
  unfold radialFourRegularizedBoundary nativeSourceFourBoundaryExtension
  split_ifs with hm
  · rfl
  · apply Finset.sum_eq_zero
    intro a _
    have hp : m-(a : ℕ) ≠ 0 := by omega
    simp [hp]

end
end CarrySelfAdjointOperator
