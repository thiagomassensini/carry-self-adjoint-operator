import NativeCarryC3Crosswalk.GeometricCutoffCompleteness

/-!
# The exact completed native characteristic

The reference operator does not use a raw finite cutoff.  Its scalar input is
the finite camera head plus the analytic tail of all omitted complete center
cells.  The dependency theorem identifies that sum with the same native
scalar for every cutoff.  This file gives that already-proved ledger the
single function name used by the operator chain.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Camera-complete head plus the exact whole-center analytic tail. -/
def completedNativeCharacteristic
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  finiteBracketCharacteristic camera cutoff s +
    ∑' index : ℕ, centerBracketTerm camera s (index + cutoff)

/-- The completed head--tail presentation is literally the infinite camera
characteristic throughout the bracket domain. -/
theorem completedNativeCharacteristic_eq_bracketCharacteristic
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    completedNativeCharacteristic camera cutoff s =
      bracketCharacteristic camera s := by
  exact complete_head_add_complete_center_tail_of_mem_domain hcamera hs

/-- The completed characteristic is exactly the common native scalar dressed
by the camera factor.  No zero or critical-line hypothesis is used. -/
theorem completedNativeCharacteristic_eq_factor_mul_nativeScalar
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    completedNativeCharacteristic camera cutoff s =
      factor camera s * nativeScalar s := by
  exact complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
    hcamera hs

/-- Changing the geometric cutoff changes only the head/tail presentation,
not the completed analytic characteristic. -/
theorem completedNativeCharacteristic_cutoff_independent
    {camera cutoff₁ cutoff₂ : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    completedNativeCharacteristic camera cutoff₁ s =
      completedNativeCharacteristic camera cutoff₂ s := by
  rw [completedNativeCharacteristic_eq_factor_mul_nativeScalar hcamera hs,
    completedNativeCharacteristic_eq_factor_mul_nativeScalar hcamera hs]

end


end CarrySelfAdjointOperator
