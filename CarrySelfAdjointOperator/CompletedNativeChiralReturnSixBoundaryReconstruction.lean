import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryFace

/-!
# Six-sample boundary reconstruction in the original radial geometry

The inverse is fixed by the radial node multipliers 1,2,3,4,5,6 and their Euler boundary
jets. No moment, metric fitting or source replacement enters this map.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false

/-- Arithmetic inverse of the Euler boundary map at nodes 1,2,3,4,5,6. -/
def radialSixBoundaryInverseCoefficients : Fin 6 → Fin 6 → ℝ :=
  ![![6, -87/10, 29/6, -31/24, 1/6, -1/120],
    ![-15, 117/4, -461/24, 137/24, -19/24, 1/24],
    ![20, -127/3, 31, -121/12, 3/2, -1/12],
    ![-15, 33, -307/12, 107/12, -17/12, 1/12],
    ![6, -27/2, 65/6, -95/24, 2/3, -1/24],
    ![-1, 137/60, -15/8, 17/24, -1/8, 1/120]]

/-- Reconstruction from all six boundary coordinates, without compression. -/
def radialSixBoundaryReconstruct (x : Fin 6 → ℂ) (i : Fin 6) : ℂ :=
  ∑ a : Fin 6, (radialSixBoundaryInverseCoefficients i a : ℂ) * x a

/-- The six boundary jets of the reconstructed source are exactly its input. -/
theorem radialSixBoundaryReconstruct_jets (x : Fin 6 → ℂ) (a : Fin 6) :
    radialEulerBoundaryJet (radialSixBoundaryReconstruct x) a = x a := by
  fin_cases a <;>
    norm_num [radialEulerBoundaryJet, radialSixBoundaryReconstruct,
      radialSixBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- Conversely no source coefficient is lost in the complete six-jet map. -/
theorem radialSixBoundaryReconstruct_source (d : Fin 6 → ℂ) :
    radialSixBoundaryReconstruct (fun a : Fin 6 => radialEulerBoundaryJet d a) = d := by
  funext i
  fin_cases i <;>
    norm_num [radialEulerBoundaryJet, radialSixBoundaryReconstruct,
      radialSixBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- The canonical small radial scale weights boundary order a by h^(a : ℕ).
This is a coordinate change, not a new metric on the Cauchy source carrier. -/
def radialSixScaledBoundary (h : ℝ) (d : Fin 6 → ℂ) (a : Fin 6) : ℂ :=
  ((h^(a : ℕ) : ℝ) : ℂ) * radialEulerBoundaryJet d a

/-- Exact inverse for nonzero radial steps. -/
def radialSixNormalizedBoundaryInput (h : ℝ) (x : Fin 6 → ℂ) : Fin 6 → ℂ :=
  radialSixBoundaryReconstruct (fun a : Fin 6 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * x a)

theorem radialSixScaledBoundary_input (h : ℝ) (hh : h ≠ 0) (x : Fin 6 → ℂ) :
    radialSixScaledBoundary h (radialSixNormalizedBoundaryInput h x) = x := by
  funext a
  rw [radialSixScaledBoundary, radialSixNormalizedBoundaryInput,
    radialSixBoundaryReconstruct_jets]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
  simp [hp]

theorem radialSixNormalizedBoundaryInput_scaled (h : ℝ) (hh : h ≠ 0) (d : Fin 6 → ℂ) :
    radialSixNormalizedBoundaryInput h (radialSixScaledBoundary h d) = d := by
  have he : (fun a : Fin 6 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
      radialSixScaledBoundary h d a) = (fun a : Fin 6 => radialEulerBoundaryJet d a) := by
    funext a
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
    simp [radialSixScaledBoundary, hp]
  rw [radialSixNormalizedBoundaryInput, he, radialSixBoundaryReconstruct_source]

/-- Higher Euler boundary coordinates are determined by the same inverse,
not discarded. -/
def radialSixHigherBoundaryCoefficient (m : ℕ) (a : Fin 6) : ℝ :=
  ∑ i : Fin 6, (((i : ℕ)+1 : ℕ) : ℝ)^m * radialSixBoundaryInverseCoefficients i a

/-- Continuous regularization of EVERY higher boundary coordinate. -/
def radialSixRegularizedBoundary (h : ℝ) (x : Fin 6 → ℂ) (m : ℕ) : ℂ :=
  if hm : m < 6 then x ⟨m, hm⟩ else
    ∑ a : Fin 6, ((h^(m-(a : ℕ)) * radialSixHigherBoundaryCoefficient m a : ℝ) : ℂ) * x a

/-- Polynomial regularization of the full coefficient vector: h^5 d. -/
def radialSixRegularizedInput (h : ℝ) (x : Fin 6 → ℂ) (i : Fin 6) : ℂ :=
  ∑ a : Fin 6, ((radialSixBoundaryInverseCoefficients i a * h^(5-(a : ℕ)) : ℝ) : ℂ) * x a

theorem radialSixRegularizedInput_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 6 → ℂ) (i : Fin 6) :
    radialSixRegularizedInput h x i =
      ((h^5 : ℝ) : ℂ) * radialSixNormalizedBoundaryInput h x i := by
  unfold radialSixRegularizedInput radialSixNormalizedBoundaryInput radialSixBoundaryReconstruct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : h^(5-(a : ℕ)) * h^(a : ℕ) = h^5 := by rw [← pow_add]; congr 1; omega
  have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
  have he : h^(5-(a : ℕ)) = h^5 * (h^(a : ℕ))⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hpa).mpr
    exact hp
  rw [he]
  push_cast
  ring

theorem radialSixRegularizedBoundary_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 6 → ℂ) (m : ℕ) :
    radialSixRegularizedBoundary h x m =
      ((h^m : ℝ) : ℂ) * radialEulerBoundaryJet (radialSixNormalizedBoundaryInput h x) m := by
  unfold radialSixRegularizedBoundary
  split_ifs with hm
  · have hs := congrFun (radialSixScaledBoundary_input h hh x) ⟨m, hm⟩
    simpa only [radialSixScaledBoundary, Fin.val_mk] using hs.symm
  · unfold radialEulerBoundaryJet radialSixNormalizedBoundaryInput radialSixBoundaryReconstruct
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold radialSixHigherBoundaryCoefficient
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

theorem radialSixRegularizedBoundary_zero (x : Fin 6 → ℂ) (m : ℕ) :
    radialSixRegularizedBoundary 0 x m = nativeSourceSixBoundaryExtension x m := by
  unfold radialSixRegularizedBoundary nativeSourceSixBoundaryExtension
  split_ifs with hm
  · rfl
  · apply Finset.sum_eq_zero
    intro a _
    have hp : m-(a : ℕ) ≠ 0 := by omega
    simp [hp]

end
end CarrySelfAdjointOperator
