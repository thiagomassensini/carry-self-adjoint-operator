import CarrySelfAdjointOperator.NativeCauchyLaguerreHeadTail
import CarrySelfAdjointOperator.NativeGammaCoupledCompletionObstruction

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate lp
open ChiralReturn GammaMaterialSewing CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem radialCauchyState_mem (k j : ℕ) :
    completedNativeRadialChiralCauchyState k j ∈ physicalCauchyClosure :=
  physicalCauchyClosure.smul_mem _ (by
    simpa only [physicalCauchyFeature_coe] using (physicalCauchyFeature j).property)

private theorem radialCombination_mem (k : ℕ) {N : ℕ} (a : Fin N → ℂ) :
    (∑ j, a j • completedNativeRadialChiralCauchyState k j) ∈ physicalCauchyClosure :=
  physicalCauchyClosure.sum_mem fun j _ =>
    physicalCauchyClosure.smul_mem _ (radialCauchyState_mem k j)

theorem sourceValue_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    sourceValue k c r ∈ physicalCauchyClosure := radialCombination_mem k _

theorem sourceCompanion_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    sourceCompanion k c r ∈ physicalCauchyClosure := radialCombination_mem k _

theorem nativeDressedCompanion_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    nativeDressedCompanion k c r ∈ physicalCauchyClosure := radialCombination_mem k _

theorem completionCompanion_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    completionCompanion k c r ∈ physicalCauchyClosure := radialCombination_mem k _

theorem originalIncident_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    (∑ j, (c j * (r : ℂ)^((j : ℕ)+1)) • completedNativeRadialChiralCauchyState k j)
      ∈ physicalCauchyClosure := radialCombination_mem k _

theorem originalReturned_mem (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    (∑ j, (c j * (r : ℂ)^((j : ℕ)+1)) • completedNativeRadialChiralMultiplierState k j)
      ∈ physicalCauchyClosure := by
  apply physicalCauchyClosure.sum_mem
  intro j _
  apply physicalCauchyClosure.smul_mem
  exact physicalCauchyClosure.smul_mem _ (radialCauchyState_mem k j)

def physicalSourceValue (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨sourceValue k c r, sourceValue_mem k c r⟩

def physicalSourceCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨sourceCompanion k c r, sourceCompanion_mem k c r⟩

def physicalNativeCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨nativeDressedCompanion k c r, nativeDressedCompanion_mem k c r⟩

def physicalCompletionCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨completionCompanion k c r, completionCompanion_mem k c r⟩

def physicalOriginalIncident (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨∑ j, (c j * (r : ℂ)^((j : ℕ)+1)) • completedNativeRadialChiralCauchyState k j,
    originalIncident_mem k c r⟩

def physicalOriginalReturned (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : PhysicalCauchySpace :=
  ⟨∑ j, (c j * (r : ℂ)^((j : ℕ)+1)) • completedNativeRadialChiralMultiplierState k j,
    originalReturned_mem k c r⟩

/-- The physical sqrt(k+1) is carried into the dictionary exactly once. -/
theorem cauchyLaguerreIsometry_radial (k j : ℕ) :
    cauchyLaguerreIsometry ⟨completedNativeRadialChiralCauchyState k j, radialCauchyState_mem k j⟩ =
      (Real.sqrt ((k : ℝ)+1) : ℂ) • laguerreColumn j := by
  have he : (⟨completedNativeRadialChiralCauchyState k j, radialCauchyState_mem k j⟩ :
      PhysicalCauchySpace) = (Real.sqrt ((k : ℝ)+1) : ℂ) • physicalCauchyFeature j := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, physicalCauchyFeature_coe]
    rfl
  rw [he, map_smul, cauchyLaguerreIsometry_feature]

/-- Original source theorem applied before mapping: both full legs and all denominators remain. -/
theorem cauchyLaguerre_originalSource_legs (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ j : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip)
    (hp : ∀ j : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    cauchyLaguerreIsometry (physicalOriginalIncident k c r) =
      cauchyLaguerreIsometry (physicalNativeCompanion k c r) +
        cauchyLaguerreIsometry (physicalCompletionCompanion k c r) +
        Complex.I • cauchyLaguerreIsometry (physicalSourceValue k c r) ∧
    cauchyLaguerreIsometry (physicalOriginalReturned k c r) =
      cauchyLaguerreIsometry (physicalNativeCompanion k c r) +
        cauchyLaguerreIsometry (physicalCompletionCompanion k c r) -
        Complex.I • cauchyLaguerreIsometry (physicalSourceValue k c r) := by
  have h := nativeCoupledCompletion_originalSource_legs k c r hs hp
  have hi : physicalOriginalIncident k c r = physicalNativeCompanion k c r +
      physicalCompletionCompanion k c r + Complex.I • physicalSourceValue k c r :=
    Subtype.ext h.2.1
  have ho : physicalOriginalReturned k c r = physicalNativeCompanion k c r +
      physicalCompletionCompanion k c r - Complex.I • physicalSourceValue k c r :=
    Subtype.ext h.2.2
  constructor
  · rw [hi, map_add, map_add, map_smul]
  · rw [ho, map_sub, map_add, map_smul]

def physicalSourceChannels (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) : Fin 3 → PhysicalCauchySpace :=
  ![physicalSourceValue k c r, physicalNativeCompanion k c r, physicalCompletionCompanion k c r]

/-- All nine ordered crosses, with independent dimensions, depths, radii and coefficients. -/
theorem cauchyLaguerre_nine_source_crossings (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ) (a b : Fin 3) :
    inner ℂ (cauchyLaguerreIsometry (physicalSourceChannels k c r a))
      (cauchyLaguerreIsometry (physicalSourceChannels l d s b)) =
    inner ℂ (physicalSourceChannels k c r a : CanonicalCompletedNativeChiralCauchyCarrier)
      (physicalSourceChannels l d s b : CanonicalCompletedNativeChiralCauchyCarrier) :=
  cauchyLaguerreIsometry_inner _ _

theorem cauchyLaguerre_nine_source_crossings_headTail (R k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ) (a b : Fin 3) :
    inner ℂ (physicalSourceChannels k c r a : CanonicalCompletedNativeChiralCauchyCarrier)
      (physicalSourceChannels l d s b : CanonicalCompletedNativeChiralCauchyCarrier) =
      inner ℂ (laguerreHead R (cauchyLaguerreIsometry (physicalSourceChannels k c r a)))
        (laguerreHead R (cauchyLaguerreIsometry (physicalSourceChannels l d s b))) +
      inner ℂ (physicalCauchyShift (R+1) (physicalSourceChannels k c r a))
        (physicalCauchyShift (R+1) (physicalSourceChannels l d s b)) :=
  physicalCauchy_head_tail_inner R _ _

/-- Specialization of the existing chiral conservation theorem. -/
theorem cauchyLaguerre_originalSource_chiral_balance (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ) :
    inner ℂ (cauchyLaguerreIsometry (physicalSourceCompanion k c r + Complex.I • physicalSourceValue k c r))
      (cauchyLaguerreIsometry (physicalSourceCompanion l d s + Complex.I • physicalSourceValue l d s)) -
    inner ℂ (cauchyLaguerreIsometry (physicalSourceCompanion k c r - Complex.I • physicalSourceValue k c r))
      (cauchyLaguerreIsometry (physicalSourceCompanion l d s - Complex.I • physicalSourceValue l d s)) =
      -2 * Complex.I * (inner ℂ (sourceValue k c r) (sourceCompanion l d s) -
        inner ℂ (sourceCompanion k c r) (sourceValue l d s)) :=
  chiral_pairing_balance_isometry cauchyLaguerreIsometry _ _ _ _

/-- The old polarized product sum applied to the literal all-order dictionary. -/
theorem cauchyLaguerre_source_polarized_product_sum (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (ht : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let w := fun j : Fin M => canonicalCompletedC3RadialTiltPoint l j
    let a := fun i : Fin N => c i * (r : ℂ)^((i : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun j : Fin M => d j * (s : ℂ)^((j : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (w j)
    inner ℂ (cauchyLaguerreIsometry (physicalSourceValue k c r))
      (cauchyLaguerreIsometry (physicalSourceCompanion l d s)) -
    inner ℂ (cauchyLaguerreIsometry (physicalSourceCompanion k c r))
      (cauchyLaguerreIsometry (physicalSourceValue l d s)) =
    ∑ i, ∑ j, conj (a i) * b j *
      inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState l j) *
      (conj (nativeXiCompletionFactor (z i)) * nativeXiCompletionFactor (w j) *
        canonicalNativeUndressedGreenForm (z i) (w j) + canonicalArchimedeanBoundaryGreenCorrection (z i) (w j)) := by
  dsimp only
  rw [cauchyLaguerreIsometry_inner, cauchyLaguerreIsometry_inner]
  exact nativeCoupledCompletion_source_polarized_product_sum k l c d r s hs ht

end
end CarrySelfAdjointOperator.NativeLaguerre
