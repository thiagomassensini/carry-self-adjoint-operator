import CarrySelfAdjointOperator.NativeCauchyLaguerreHeadTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace lp unitInterval
open MeasureTheory Set
noncomputable section
set_option autoImplicit false

/-- The original continuous half-density, including the physical endpoint value. -/
def physicalHalfDensity (j : ℕ) (u : ℝ) : ℂ := (Real.sqrt u : ℂ) * (u : ℂ)^j

theorem physicalHalfDensity_rpow (j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    physicalHalfDensity j u = (u ^ ((j : ℝ)+1/2) : ℝ) := by
  rw [physicalHalfDensity, Real.rpow_add_of_nonneg hu (by positivity) (by norm_num),
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  push_cast
  ring

theorem integral_physicalHalfDensity (j : ℕ) {u : ℝ} (hu : 0 < u) :
    (∫ v in 0..u, physicalHalfDensity j v) =
      (u ^ ((j : ℝ)+3/2) / ((j : ℝ)+3/2) : ℝ) := by
  rw [intervalIntegral.integral_congr (fun v hv =>
    physicalHalfDensity_rpow j (by
      rw [uIcc_of_le hu.le] at hv
      exact hv.1)), intervalIntegral.integral_ofReal]
  have hj : -1 < (j : ℝ)+1/2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  rw [integral_rpow (Or.inl hj)]
  have he : (j : ℝ)+1/2+1 = (j : ℝ)+3/2 := by ring
  rw [he, Real.zero_rpow (by positivity), sub_zero]

/-- Direct integration certifies I-Hardy on every original half density. -/
theorem hardyStep_physicalHalfDensity (j : ℕ) {u : ℝ} (hu : 0 < u) :
    physicalHalfDensity j u - (u : ℂ)⁻¹ * (∫ v in 0..u, physicalHalfDensity j v) =
      (rho j : ℂ) * physicalHalfDensity j u := by
  rw [integral_physicalHalfDensity j hu, physicalHalfDensity_rpow j hu.le]
  have he : (j : ℝ)+3/2 = (j : ℝ)+1/2+1 := by ring
  rw [he, Real.rpow_add hu ((j : ℝ)+1/2) 1, Real.rpow_one]
  have h : u ^ ((j : ℝ)+1/2) - u⁻¹ *
      (u ^ ((j : ℝ)+1/2) * u / ((j : ℝ)+1/2+1)) =
      rho j * u ^ ((j : ℝ)+1/2) := by
    unfold rho
    field_simp [hu.ne']
    ring
  exact_mod_cast h

def physicalFiniteFunction (m : ℕ) (c : Fin m → ℂ) (u : ℝ) : ℂ :=
  ∑ j, c j * physicalHalfDensity j u

theorem hardyStep_physicalFiniteFunction (m : ℕ) (c : Fin m → ℂ)
    {u : ℝ} (hu : 0 < u) :
    physicalFiniteFunction m c u -
      (u : ℂ)⁻¹ * (∫ v in 0..u, physicalFiniteFunction m c v) =
      ∑ j, c j * (rho j : ℂ) * physicalHalfDensity j u := by
  unfold physicalFiniteFunction
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (show Continuous (fun v : ℝ => c j * physicalHalfDensity j v) by
      unfold physicalHalfDensity
      fun_prop).intervalIntegrable 0 u)]
  simp only [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = c j * (physicalHalfDensity j u -
        (u : ℂ)⁻¹ * ∫ v in 0..u, physicalHalfDensity j v) := by ring
    _ = _ := by rw [hardyStep_physicalHalfDensity j hu]; ring

theorem physicalFiniteSynthesis_ae (m : ℕ) (c : Fin m → ℂ) :
    ((physicalFiniteSynthesis m c : CanonicalCompletedNativeChiralCauchyCarrier) :
      unitInterval → ℂ) =ᵐ[volume] (fun u => physicalFiniteFunction m c u) := by
  classical
  have hc (j : Fin m) :
      (completedNativeChiralCauchyFeature j : unitInterval → ℂ) =ᵐ[volume]
        (fun u => physicalHalfDensity j u) := by
    simpa [completedNativeChiralCauchyFeature, completedNativeChiralCauchyContinuousFeature,
      physicalHalfDensity, Complex.ofReal_mul, Complex.ofReal_pow] using
      ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
        (completedNativeChiralCauchyContinuousFeature j)
  rw [physicalFiniteSynthesis_coe]
  simp only [ChiralReturn.radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    completedNativeRadialChiralCauchyState, Nat.cast_zero, zero_add,
    Real.sqrt_one, Complex.ofReal_one, one_smul]
  change ((∑ j, c j • completedNativeChiralCauchyFeature j :
    CanonicalCompletedNativeChiralCauchyCarrier) : unitInterval → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j : Fin m => c j • completedNativeChiralCauchyFeature j),
    (ae_all_iff).mpr (fun j : Fin m => Lp.coeFn_smul (c j) (completedNativeChiralCauchyFeature j)),
    (ae_all_iff).mpr hc] with u hsum hsmul hcol
  rw [hsum]
  simp only [Finset.sum_apply, physicalFiniteFunction]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsmul j]
  simp only [Pi.smul_apply, smul_eq_mul, hcol j]

/-- The completed step agrees a.e. with the independently integrated physical formula on the core. -/
theorem physicalCauchyShift_one_hardy_core (m : ℕ) (c : Fin m → ℂ) :
    ((physicalCauchyShift 1 (physicalFiniteSynthesis m c) :
      CanonicalCompletedNativeChiralCauchyCarrier) : unitInterval → ℂ) =ᵐ[volume]
      (fun u => physicalFiniteFunction m c u - (u : ℂ)⁻¹ *
        ∫ v in 0..(u : ℝ), physicalFiniteFunction m c v) := by
  have he : physicalCauchyShift 1 (physicalFiniteSynthesis m c) =
      physicalFiniteSynthesis m (fun j => c j * (rho j : ℂ)) := by
    simp only [physicalFiniteSynthesis, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
      physicalCauchyShift_feature, pow_one, smul_smul]
  rw [he]
  apply (physicalFiniteSynthesis_ae m _).trans
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : 0 < (u : ℝ)
  · exact (hardyStep_physicalFiniteFunction m c hu).symm
  · have hz : (u : ℝ) = 0 := le_antisymm (le_of_not_gt hu) u.property.1
    simp [physicalFiniteFunction, physicalHalfDensity, hz]

end
end CarrySelfAdjointOperator.NativeLaguerre
