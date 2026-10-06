import CarrySelfAdjointOperator.CompletedNativeChiralReturnStorage

/-!
# Complete source-trace frontier of chiral return storage

Undo the existing chiral coordinates in the unchanged radial Cauchy carrier.
Both vector syntheses come from the completed value/companion trace, before
its signed scalar contraction. The normalization is exactly division by the
existing positive chiral coordinate. No sign, complement or dilation is
constructed from the value of storage.
-/

namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
noncomputable section
set_option autoImplicit false

/-- Complete value-channel synthesis in the existing Cauchy Hilbert carrier. -/
def sourceValue (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
    completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)) •
    completedNativeRadialChiralCauchyState k i

/-- Complete companion-channel synthesis; the companion is literally -F'. -/
def sourceCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
    (-deriv completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)) •
    completedNativeRadialChiralCauchyState k i

/-- At every cutoff these vectors are the exact completed TFVD value and
companion readouts. All tails/completion are those already present upstream. -/
theorem source_pair_eq_bracketTfvd (M k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip) :
    (sourceValue k c r, sourceCompanion k c r) =
      (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
        (canonicalC3BracketTfvdCompletedTracePair M (canonicalCompletedC3RadialTiltPoint k i)).1 /
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i)) • completedNativeRadialChiralCauchyState k i,
       ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
        (canonicalC3BracketTfvdCompletedTracePair M (canonicalCompletedC3RadialTiltPoint k i)).2 /
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i)) • completedNativeRadialChiralCauchyState k i) := by
  simp only [sourceValue, sourceCompanion,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M (hstrip _)]

/-- Incident synthesis reconstructed from both complete source channels. -/
theorem incident_synthesis_eq_source (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralCauchyState k i) =
      sourceCompanion k c r + Complex.I • sourceValue k c r := by
  unfold sourceValue sourceCompanion
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← add_smul]
  congr 1
  have hp := hpositive i
  field_simp
  unfold completedNativePositiveHermiteBiehlerCoordinate
  ring

/-- Return synthesis reconstructed from those same channels, with the
opposite chiral orientation. No operator contractivity is used. -/
theorem returned_synthesis_eq_source (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralMultiplierState k i) =
      sourceCompanion k c r - Complex.I • sourceValue k c r := by
  unfold sourceValue sourceCompanion
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [completedNativeRadialChiralMultiplierState, smul_smul, smul_smul, ← sub_smul]
  congr 1
  have hp := hpositive i
  unfold completedNativeHermiteBiehlerChiralQuotient
  field_simp
  unfold completedNativeNegativeHermiteBiehlerCoordinate
  ring

/-- The signed chiral norm balance is a mixed orientation, not a sum of
squares. The first argument of the inner product is conjugate-linear. -/
theorem norm_chiral_balance_eq_source_cross
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V C : E) :
    ‖C + Complex.I • V‖ ^ 2 - ‖C - Complex.I • V‖ ^ 2 =
      4 * (inner ℂ V C).im := by
  rw [@norm_add_sq ℂ, @norm_sub_sq ℂ, inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    RCLike.re_to_complex]
  have him : -(inner ℂ C V).im = (inner ℂ V C).im := by
    simpa only [Complex.conj_im] using congrArg Complex.im (inner_conj_symm V C)
  rw [him]
  ring

/-- Exact total-energy identity of the two source orientations. It controls
the sum of incident and returned energies, not their order. -/
theorem source_total_energy (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ‖∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralCauchyState k i‖ ^ 2 +
      ‖∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralMultiplierState k i‖ ^ 2 =
      2 * (‖sourceCompanion k c r‖ ^ 2 + ‖sourceValue k c r‖ ^ 2) := by
  rw [incident_synthesis_eq_source k c r hpositive, returned_synthesis_eq_source k c r hpositive,
    @norm_add_sq ℂ, @norm_sub_sq ℂ]
  simp only [norm_smul, Complex.norm_I, one_mul]
  ring

/-- All cross terms of the actual storage are the oriented complete-source
pairing. No nonnegativity of that pairing is asserted. -/
theorem storage_re_eq_source_cross (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c r).re = 4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im := by
  rw [storage_re_eq_norm_balance, incident_synthesis_eq_source k c r hpositive,
    returned_synthesis_eq_source k c r hpositive, norm_chiral_balance_eq_source_cross]

/-- The same source orientation is the accumulated flux, rather than a
pointwise nonnegative integrand. -/
theorem integral_flux_re_eq_source_cross (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (∫ x in (0 : ℝ)..r, ((k : ℝ) + 1 : ℂ) * (x : ℂ) *
      ((Complex.normSq (incident c x) : ℂ) - (Complex.normSq (returned k c x) : ℂ))).re =
      4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im := by
  rw [integral_flux_eq_storage, storage_re_eq_source_cross k c r hpositive]

/-- The denominators of the source reconstruction require no new global
hypothesis: all coefficients and internal radii share the same eventual
regularity on each finite sample family. -/
theorem storage_eventually_eq_source_cross (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ, ∀ r : ℝ,
      (storage k c r).re = 4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk c r
  exact storage_re_eq_source_cross k c r (fun i => (hk i).2.2)

/-- The exact all-order integrated frontier at the upper endpoint. This is
an identity, not a proof that either side has nonnegative sign. -/
theorem storage_one_eventually_eq_source_cross (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ,
      (storage k c 1).re = 4 * (inner ℂ (sourceValue k c 1) (sourceCompanion k c 1)).im := by
  filter_upwards [storage_eventually_eq_source_cross N] with k hk c
  exact hk c 1

end
end CarrySelfAdjointOperator.ChiralReturn
