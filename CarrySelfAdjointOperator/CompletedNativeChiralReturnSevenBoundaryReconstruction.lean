import CarrySelfAdjointOperator.CompletedNativeChiralReturnFirstSurvivingBoundary

/-!
# Seven-sample boundary reconstruction in the original radial geometry

The inverse is fixed by the radial node multipliers 1,2,3,4,5,6,7 and their Euler boundary
jets. No moment, metric fitting or source replacement enters this map.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false

/-- Arithmetic inverse of the Euler boundary map at nodes 1,2,3,4,5,6,7. -/
def radialSevenBoundaryInverseCoefficients : Fin 7 → Fin 7 → ℝ :=
  ![![7, -223/20, 319/45, -37/16, 59/144, -3/80, 1/720],
    ![-21, 879/20, -3929/120, 71/6, -9/4, 13/60, -1/120],
    ![35, -949/12, 389/6, -1219/48, 247/48, -25/48, 1/48],
    ![-35, 82, -2545/36, 88/3, -113/18, 2/3, -1/36],
    ![21, -201/4, 134/3, -925/48, 69/16, -23/48, 1/48],
    ![-7, 1019/60, -1849/120, 41/6, -19/12, 11/60, -1/120],
    ![1, -49/20, 203/90, -49/48, 35/144, -7/240, 1/720]]

/-- Reconstruction from all seven boundary coordinates, without compression. -/
def radialSevenBoundaryReconstruct (x : Fin 7 → ℂ) (i : Fin 7) : ℂ :=
  ∑ a : Fin 7, (radialSevenBoundaryInverseCoefficients i a : ℂ) * x a

/-- The seven boundary jets of the reconstructed source are exactly its input. -/
theorem radialSevenBoundaryReconstruct_jets (x : Fin 7 → ℂ) (a : Fin 7) :
    radialEulerBoundaryJet (radialSevenBoundaryReconstruct x) a = x a := by
  fin_cases a <;>
    norm_num [radialEulerBoundaryJet, radialSevenBoundaryReconstruct,
      radialSevenBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- Conversely no source coefficient is lost in the complete seven-jet map. -/
theorem radialSevenBoundaryReconstruct_source (d : Fin 7 → ℂ) :
    radialSevenBoundaryReconstruct (fun a : Fin 7 => radialEulerBoundaryJet d a) = d := by
  funext i
  fin_cases i <;>
    norm_num [radialEulerBoundaryJet, radialSevenBoundaryReconstruct,
      radialSevenBoundaryInverseCoefficients, Fin.sum_univ_succ] <;> ring
  all_goals rfl

/-- The canonical small radial scale weights boundary order a by h^(a : ℕ).
This is a coordinate change, not a new metric on the Cauchy source carrier. -/
def radialSevenScaledBoundary (h : ℝ) (d : Fin 7 → ℂ) (a : Fin 7) : ℂ :=
  ((h^(a : ℕ) : ℝ) : ℂ) * radialEulerBoundaryJet d a

/-- Exact inverse for nonzero radial steps. -/
def radialSevenNormalizedBoundaryInput (h : ℝ) (x : Fin 7 → ℂ) : Fin 7 → ℂ :=
  radialSevenBoundaryReconstruct (fun a : Fin 7 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * x a)

theorem radialSevenScaledBoundary_input (h : ℝ) (hh : h ≠ 0) (x : Fin 7 → ℂ) :
    radialSevenScaledBoundary h (radialSevenNormalizedBoundaryInput h x) = x := by
  funext a
  rw [radialSevenScaledBoundary, radialSevenNormalizedBoundaryInput,
    radialSevenBoundaryReconstruct_jets]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
  simp [hp]

theorem radialSevenNormalizedBoundaryInput_scaled (h : ℝ) (hh : h ≠ 0) (d : Fin 7 → ℂ) :
    radialSevenNormalizedBoundaryInput h (radialSevenScaledBoundary h d) = d := by
  have he : (fun a : Fin 7 => (((h^(a : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
      radialSevenScaledBoundary h d a) = (fun a : Fin 7 => radialEulerBoundaryJet d a) := by
    funext a
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hp : (h : ℂ)^(a : ℕ) ≠ 0 := pow_ne_zero _ hc
    simp [radialSevenScaledBoundary, hp]
  rw [radialSevenNormalizedBoundaryInput, he, radialSevenBoundaryReconstruct_source]

/-- Polynomial regularization of the same COMPLETE seven-coordinate input: h^6 d. -/
def radialSevenRegularizedInput (h : ℝ) (x : Fin 7 → ℂ) (i : Fin 7) : ℂ :=
  ∑ a : Fin 7, ((radialSevenBoundaryInverseCoefficients i a * h^(6-(a : ℕ)) : ℝ) : ℂ) * x a

theorem radialSevenRegularizedInput_eq (h : ℝ) (hh : h ≠ 0) (x : Fin 7 → ℂ) (i : Fin 7) :
    radialSevenRegularizedInput h x i =
      ((h^6 : ℝ) : ℂ) * radialSevenNormalizedBoundaryInput h x i := by
  unfold radialSevenRegularizedInput radialSevenNormalizedBoundaryInput radialSevenBoundaryReconstruct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : h^(6-(a : ℕ)) * h^(a : ℕ) = h^6 := by rw [← pow_add]; congr 1; omega
  have hpa : h^(a : ℕ) ≠ 0 := pow_ne_zero _ hh
  have he : h^(6-(a : ℕ)) = h^6 * (h^(a : ℕ))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hpa).mpr hp
  rw [he]
  push_cast
  ring

end
end CarrySelfAdjointOperator
