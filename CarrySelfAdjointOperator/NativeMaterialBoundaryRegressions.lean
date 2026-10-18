import CarrySelfAdjointOperator.NativeMaterialBoundarySourceTransport

namespace CarrySelfAdjointOperator.MaterialBoundarySewing
open CPFormal.Analytic.Cp MaterialCameraJets PhysicalSewing
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Limits
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem c2_border_regression (M : ℕ) :
    finiteStencil 2 M = cameraCoreStencil 2 M + atom (4*M+1) := by
  rw [finiteStencil_eq_core_add_border 2 M (by norm_num)]
  simp [cameraBorderStencil,unitBorderStencil,cameraSlope,cameraBoundaryWidth]

theorem c3_border_regression (M : ℕ) :
    finiteStencil 3 M = cameraCoreStencil 3 M + atom (3*M+1) := by
  rw [finiteStencil_eq_core_add_border 3 M (by norm_num)]
  simp [cameraBorderStencil,unitBorderStencil,cameraSlope,cameraBoundaryWidth]

theorem c4_border_regression (M : ℕ) :
    finiteStencil 4 M = cameraCoreStencil 4 M + (atom (4*M+1)+atom (4*M+2)) := by
  rw [finiteStencil_eq_core_add_border 4 M (by norm_num)]
  simp [cameraBorderStencil,unitBorderStencil,cameraSlope,cameraBoundaryWidth,
    Finset.sum_range_succ,Nat.add_assoc]

theorem c5_border_regression (M : ℕ) :
    finiteStencil 5 M = cameraCoreStencil 5 M + (atom (5*M+1)+atom (5*M+2)) := by
  rw [finiteStencil_eq_core_add_border 5 M (by norm_num)]
  simp [cameraBorderStencil,unitBorderStencil,cameraSlope,cameraBoundaryWidth,
    Finset.sum_range_succ,Nat.add_assoc]

def unitMaterialSamples (N : ℕ) : FiniteRealSpectralHilbert N := WithLp.toLp 2 (fun _ => 1)

/-- Already the first C2 border has a nonzero ordered cross with the
C5 core. This is the unchanged material metric, not the chiral signed form. -/
theorem first_mixed_material_border_cross :
    inner ℂ (borderMaterialJet 2 1 0 (unitMaterialSamples 8))
      (coreMaterialJet 5 1 0 (unitMaterialSamples 8)) = -4 := by
  rw [PiLp.inner_apply]
  norm_num [borderMaterialJet,coreMaterialJet,materialJet,stencilMaterialAction,
    cameraBorderStencil,unitBorderStencil_apply,cameraCoreStencil,coefficientPrefixStencil_apply,
    profile,oddProfile,dvdIndicator,cameraSlope,cameraBoundaryWidth,unitMaterialSamples,
    Fin.sum_univ_succ,RCLike.inner_apply]

/-- An explicit physical witness rules out discarding all mixed sectors. -/
theorem first_mixed_material_border_cross_ne_zero :
    inner ℂ (borderMaterialJet 2 1 0 (unitMaterialSamples 8))
      (coreMaterialJet 5 1 0 (unitMaterialSamples 8)) ≠ 0 := by
  rw [first_mixed_material_border_cross]
  norm_num

/-- This is derived from the finite operator's antipodal coefficient, not
defined by subtracting two unknown Green kernels. -/
theorem even_antipodal_source_difference (k b M : ℕ) (hb : 4 ≤ b) (he : Even b) :
    originalMaterialCompletedSource k
        (coefficientPrefixStencil (evenProfile b) (b*M+b/2)) -
      originalMaterialCompletedSource k (finiteStencil b M) =
      canonicalCompletedNativeRadialProjectiveChiralState k (b*M+b/2-1) := by
  rw [finiteStencil_even_eq_coefficientPrefixStencil_sub hb he M,map_sub]
  have hp : 1 ≤ b*M+b/2 := by omega
  have hs := originalMaterialCompletedSource_atom k (b*M+b/2-1)
  rw [Nat.sub_add_cancel hp] at hs
  rw [hs]
  abel

theorem radial_cauchy_column_ne_zero (k j : ℕ) :
    completedNativeRadialChiralCauchyState k j ≠ 0 := by
  intro hz
  have hi := inner_completedNativeRadialChiralCauchyState k j j
  rw [hz,inner_zero_left] at hi
  have hn : ((((k : ℝ)+1)*(((j+j+2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show ((k : ℝ)+1)*(((j+j+2 : ℕ) : ℝ)⁻¹) ≠ 0 by positivity)
  exact hn hi.symm

theorem original_completed_column_ne_zero (k j : ℕ)
    (hA : completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    canonicalCompletedNativeRadialProjectiveChiralState k j ≠ 0 := by
  intro hz
  have hf := congrArg Prod.fst hz
  change completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k j) • completedNativeRadialChiralCauchyState k j = 0 at hf
  exact (smul_ne_zero hA (radial_cauchy_column_ne_zero k j)) hf

/-- An omitted C4 antipodal unit is a nonzero whole-source error at all
sufficiently fine ORIGINAL radial grids, for every fixed material cutoff. -/
theorem c4_antipodal_source_error_eventually_ne_zero (M : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      originalMaterialCompletedSource k
          (coefficientPrefixStencil (evenProfile 4) (4*M+2)) ≠
        originalMaterialCompletedSource k (finiteStencil 4 M) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (4*M+2)]
    with k hk
  intro heq
  have hd := even_antipodal_source_difference k 4 M (by norm_num) (by decide)
  norm_num only [Nat.reduceDiv] at hd
  rw [show 4*M+2-1=4*M+1 by omega,heq,sub_self] at hd
  have hreg := hk (⟨4*M+1,by omega⟩ : Fin (4*M+2))
  exact original_completed_column_ne_zero k (4*M+1)
    (completedNativeNormalizedPositiveChiralAmplitude_ne_zero hreg.2.1 hreg.2.2) hd.symm

end
end CarrySelfAdjointOperator.MaterialBoundarySewing
