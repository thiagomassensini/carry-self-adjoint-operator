import CarrySelfAdjointOperator.BR2BracketIncidenceIndependence
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import Mathlib.Tactic

/-!
# BR2 bracket independence through the exact TFVD analysis

The all-base center pivot gives linear independence before analysis. The
upstream enriched TFVD analysis has an exact continuous left inverse on the
whole vertical `ell^2` space, hence is injective. Mapping the bracket family
through this actual analysis therefore preserves its finite even and odd
linear independence.

This is the native strictness mechanism available before any identification
with the completed Green Taylor jets. The remaining bridge is a typed
transport from these faithful TFVD states to the completed normalized jets;
strict Hankel positivity is not claimed before that transport is proved.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open scoped lp

noncomputable section

/-- Complex `ell^2` realization of one centered bracket incidence. -/
def br2CameraBracketVerticalState
    (camera radius index : ℕ) : CarryVerticalL2 :=
  lp.single 2 (alignedCenter camera index - radius) (1 : ℂ) +
    lp.single 2 (alignedCenter camera index) (-2 : ℂ) +
      lp.single 2 (alignedCenter camera index + radius) (1 : ℂ)

/-- The same exclusive center pivot survives in the actual complex vertical
Hilbert state. -/
@[simp] theorem br2CameraBracketVerticalState_apply_alignedCenter
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (i j : ℕ) :
    br2CameraBracketVerticalState camera radius i (alignedCenter camera j) =
      if i = j then (-2 : ℂ) else 0 := by
  classical
  have hlegs :=
    bracketLegs_ne_any_alignedCenter
      (camera := camera) (index := i) (radius := radius)
      (otherIndex := j) hcamera hradius
  have hleft :
      alignedCenter camera i - radius ≠ alignedCenter camera j := hlegs.1
  have hright :
      alignedCenter camera i + radius ≠ alignedCenter camera j := hlegs.2
  have hleft' :
      alignedCenter camera j ≠ alignedCenter camera i - radius := hleft.symm
  have hright' :
      alignedCenter camera j ≠ alignedCenter camera i + radius := hright.symm
  by_cases hij : i = j
  · subst j
    simp only [br2CameraBracketVerticalState, lp.coeFn_add, Pi.add_apply]
    rw [lp.single_apply_ne 2 _ _ hleft', lp.single_apply_self,
      lp.single_apply_ne 2 _ _ hright']
    simp
  · have hcenter : alignedCenter camera i ≠ alignedCenter camera j :=
      fun h => hij (br2AlignedCenter_injective hcamera h)
    have hcenter' : alignedCenter camera j ≠ alignedCenter camera i :=
      hcenter.symm
    simp only [br2CameraBracketVerticalState, lp.coeFn_add, Pi.add_apply]
    rw [lp.single_apply_ne 2 _ _ hleft',
      lp.single_apply_ne 2 _ _ hcenter',
      lp.single_apply_ne 2 _ _ hright']
    simp [hij]

/-- Every injectively indexed finite bracket family is linearly independent
in the actual complex vertical Hilbert space. -/
theorem br2CameraBracketVerticalState_linearIndependent_of_injective
    {ι : Type*} [Fintype ι]
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    LinearIndependent ℂ
      (fun i : ι => br2CameraBracketVerticalState camera radius (index i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  have hdiag : ∀ j : ι,
      br2CameraBracketVerticalState camera radius (index j)
          (alignedCenter camera (index i)) =
        if j = i then (-2 : ℂ) else 0 := by
    intro j
    rw [br2CameraBracketVerticalState_apply_alignedCenter hcamera hradius]
    by_cases hji : j = i
    · simp [hji]
    · have hne : index j ≠ index i := fun h => hji (hindex h)
      simp [hji, hne]
  have heval :
      (∑ j : ι,
        coeff j *
          br2CameraBracketVerticalState camera radius (index j)
            (alignedCenter camera (index i))) = 0 := by
    have heval' := congrArg
      (fun v : CarryVerticalL2 => v (alignedCenter camera (index i))) hsum
    simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
      lp.coeFn_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using heval'
  simp_rw [hdiag] at heval
  have hscaled : coeff i * (-2 : ℂ) = 0 := by
    simpa using heval
  simpa using hscaled

/-- Even vertical bracket prefixes are complex-linearly independent. -/
theorem br2EvenCameraBracketVerticalState_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ) :
    LinearIndependent ℂ
      (fun i : Fin N =>
        br2CameraBracketVerticalState camera radius (2 * (i : ℕ))) :=
  br2CameraBracketVerticalState_linearIndependent_of_injective
    hcamera hradius _ (br2EvenParityIndex_injective N)

/-- Odd vertical bracket prefixes are complex-linearly independent. -/
theorem br2OddCameraBracketVerticalState_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ) :
    LinearIndependent ℂ
      (fun i : Fin N =>
        br2CameraBracketVerticalState camera radius (2 * (i : ℕ) + 1)) :=
  br2CameraBracketVerticalState_linearIndependent_of_injective
    hcamera hradius _ (br2OddParityIndex_injective N)

/-- An injective linear analysis preserves every linearly independent family. -/
theorem linearIndependent_map_of_injective
    {ι E F : Type*}
    [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    {v : ι → E} (hv : LinearIndependent ℂ v)
    (analysis : E →ₗ[ℂ] F)
    (hanalysis : Function.Injective analysis) :
    LinearIndependent ℂ (analysis ∘ v) := by
  have hker : LinearMap.ker analysis = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hanalysis
  exact hv.map' analysis hker

/-- The actual enriched TFVD analysis preserves bracket-family independence
because its exact reconstruction is a left inverse. -/
theorem br2CameraBracketTfvdState_linearIndependent_of_injective
    {ι : Type*} [Fintype ι]
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (index : ι → ℕ) (hindex : Function.Injective index)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    LinearIndependent ℂ
      (fun i : ι =>
        nativeGpreFiniteTfvdAnalysis q S
          (br2CameraBracketVerticalState camera radius (index i))) := by
  apply linearIndependent_map_of_injective
    (br2CameraBracketVerticalState_linearIndependent_of_injective
      hcamera hradius index hindex)
    (nativeGpreFiniteTfvdAnalysis q S).toLinearMap
  exact nativeGpreFiniteTfvdAnalysis_injective q hqpos hq1 S

/-- Even TFVD-analyzed bracket prefixes are complex-linearly independent. -/
theorem br2EvenCameraBracketTfvdState_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    LinearIndependent ℂ
      (fun i : Fin N =>
        nativeGpreFiniteTfvdAnalysis q S
          (br2CameraBracketVerticalState camera radius (2 * (i : ℕ)))) :=
  br2CameraBracketTfvdState_linearIndependent_of_injective
    hcamera hradius _ (br2EvenParityIndex_injective N)
    q hqpos hq1 S

/-- Odd TFVD-analyzed bracket prefixes are complex-linearly independent. -/
theorem br2OddCameraBracketTfvdState_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ)
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    LinearIndependent ℂ
      (fun i : Fin N =>
        nativeGpreFiniteTfvdAnalysis q S
          (br2CameraBracketVerticalState camera radius
            (2 * (i : ℕ) + 1))) :=
  br2CameraBracketTfvdState_linearIndependent_of_injective
    hcamera hradius _ (br2OddParityIndex_injective N)
    q hqpos hq1 S

end

end CarrySelfAdjointOperator
