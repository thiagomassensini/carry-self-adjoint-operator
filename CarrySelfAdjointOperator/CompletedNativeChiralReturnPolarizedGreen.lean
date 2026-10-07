import CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplit

/-!
# Polarized Green balance after complete source synthesis

Independent coefficient families are synthesized in the unchanged Cauchy
carrier before contracting their inner products. This exposes the full
Hermitian balance and its corrected Green ledger. It constructs no positive
complement or new metric. A conservative split requires an additional
source-derived orthogonal return channel, not just linear reconstruction.
-/

namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter NativeCarrySpectralWeyl.Boundary CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- Polarization of the existing incident-minus-return energy, with the
first Hilbert argument conjugate-linear. -/
theorem chiral_pairing_balance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V C W D : E) :
    inner ℂ (C + Complex.I • V) (D + Complex.I • W) -
      inner ℂ (C - Complex.I • V) (D - Complex.I • W) =
      -2 * Complex.I * (inner ℂ V D - inner ℂ C W) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  ring

/-- The conservative total-energy law has its own full polarization.
It controls the sum of the channel energies, not their order. -/
theorem chiral_pairing_total
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V C W D : E) :
    inner ℂ (C + Complex.I • V) (D + Complex.I • W) +
      inner ℂ (C - Complex.I • V) (D - Complex.I • W) =
      2 * (inner ℂ C D + inner ℂ V W) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

/-- Independent complete value/companion syntheses precede this contraction.
No coefficients or vectors are selected from a prescribed kernel. -/
def polarizedSourceBalance (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ) : ℂ :=
  inner ℂ (sourceCompanion k c r + Complex.I • sourceValue k c r)
    (sourceCompanion k d s + Complex.I • sourceValue k d s) -
  inner ℂ (sourceCompanion k c r - Complex.I • sourceValue k c r)
    (sourceCompanion k d s - Complex.I • sourceValue k d s)

/-- The balance is exactly the existing symplectic Green form, with its
orientation and factor retained. It is not a positive Hilbert form. -/
theorem polarizedSourceBalance_eq_greenForm (k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ) :
    polarizedSourceBalance k c d r s = 2 * Complex.I *
      greenForm (𝕜 := ℂ) (sourceValue k c r, sourceCompanion k c r)
        (sourceValue k d s, sourceCompanion k d s) := by
  unfold polarizedSourceBalance
  rw [chiral_pairing_balance]
  simp only [greenForm]
  ring

/-- Its diagonal is the unchanged real accumulated storage. -/
theorem polarizedSourceBalance_self_eq_storage (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hpositive : ∀ i : Fin N,
      completedNativePositiveHermiteBiehlerCoordinate
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    polarizedSourceBalance k c c r r = ((storage k c r).re : ℂ) := by
  unfold polarizedSourceBalance
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  have hr := (norm_chiral_balance_eq_source_cross
    (sourceValue k c r) (sourceCompanion k c r)).trans
      (storage_re_eq_source_cross k c r hpositive).symm
  rw [← RCLike.ofReal_pow, ← RCLike.ofReal_pow, ← RCLike.ofReal_sub]
  exact congrArg (fun x : ℝ => (x : ℂ)) hr

/-- The full Hermitian symmetry follows from the two actual Hilbert pairings. -/
theorem polarizedSourceBalance_conj_symm (k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ) :
    star (polarizedSourceBalance k c d r s) = polarizedSourceBalance k d c s r := by
  simp only [polarizedSourceBalance, star_sub, Complex.star_def, inner_conj_symm]

/-- A common isometric repackaging preserves the signed balance exactly.
Conservation alone cannot identify the return with an orthogonal component. -/
theorem chiral_pairing_balance_isometry
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : E →ₗᵢ[ℂ] H) (V C W D : E) :
    inner ℂ (U (C + Complex.I • V)) (U (D + Complex.I • W)) -
      inner ℂ (U (C - Complex.I • V)) (U (D - Complex.I • W)) =
      -2 * Complex.I * (inner ℂ V D - inner ℂ C W) := by
  rw [U.inner_map_map, U.inner_map_map]
  exact chiral_pairing_balance V C W D

/-- Expansion with independent left/right coefficients: every ordered
sample pairing survives, including both off-diagonal entries. -/
theorem polarized_mixed_synthesis_eq_wronskian_sum
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (u : ι → E) (a b F C : ι → ℂ) :
    inner ℂ (∑ i, (a i * F i) • u i) (∑ j, (b j * C j) • u j) -
      inner ℂ (∑ i, (a i * C i) • u i) (∑ j, (b j * F j) • u j) =
      ∑ i, ∑ j, star (a i) * b j * inner ℂ (u i) (u j) *
        mixedScalarBoundaryWedge (F j) (C j) (F i) (C i) := by
  simp_rw [sum_inner, inner_sum]
  simp only [inner_smul_left, inner_smul_right, map_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold mixedScalarBoundaryWedge
  simp only [starRingEnd_apply]
  ring

/-- At every cutoff the polarized balance uses the already synthesized,
tail-completed TFVD Wronskian, not a bracket-only projection. -/
theorem polarizedSourceBalance_eq_bracketTfvd_sum (M k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let a := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun i : Fin N => d i * (s : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    polarizedSourceBalance k c d r s = -2 * Complex.I *
      (∑ i : Fin N, ∑ j : Fin N, star (a i) * b j *
        inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        canonicalC3BracketTfvdCompletedWronskianReadout M (z j) (z i)) := by
  dsimp only
  unfold polarizedSourceBalance
  rw [chiral_pairing_balance]
  congr 1
  have hs := polarized_mixed_synthesis_eq_wronskian_sum
    (fun i : Fin N => completedNativeRadialChiralCauchyState k i)
    (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => d i * (s : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => -deriv completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i))
  simpa only [greenForm, sourceValue, sourceCompanion, div_mul_eq_mul_div,
    canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime M
      (hstrip _) (hstrip _), mixedScalarBoundaryWedge, completedGreenWronskian] using hs

/-- The existing full corrected ledger remains intact for independent
syntheses. Boundary/provenance, off-diagonal, residual, tail and completion
are retained; there is no sign claim on any of these terms. -/
theorem polarizedSourceBalance_eq_corrected_green_ledger (M k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let a := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun i : Fin N => d i * (s : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let L := fun i j : Fin N => canonicalCompletedC3FiniteFNegFPrimeMixedChannels M (z j) (z i)
    polarizedSourceBalance k c d r s = -2 * Complex.I *
      (∑ i : Fin N, ∑ j : Fin N, star (a i) * b j *
        inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        ((mixedHermitianWeight nativeXiCompletionFactor (z j) (z i) *
          canonicalC3BracketTfvdMixedGreenReadout M
            (operatorHeightParameter (z j)) (operatorHeightParameter (z i)) +
          (L i j).greenProvenance + (L i j).offDiagonal +
          (L i j).readoutResidual + (L i j).tailCompletion +
          (L i j).archimedeanChart) /
          mixedHermitianWeight canonicalC3ChartFactorHeight (z j) (z i))) := by
  dsimp only
  rw [polarizedSourceBalance_eq_bracketTfvd_sum M k c d r s hstrip]
  simp_rw [bracketTfvd_wronskian_eq_corrected_green_ledger M (hstrip _) (hstrip _)]

/-- Product-rule separation is performed at vector level on both sides
before the Green contraction. These channels are not declared orthogonal. -/
theorem polarizedSourceBalance_eq_native_add_completion (k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      -2 * Complex.I * (inner ℂ (sourceValue k c r) (nativeDressedCompanion k d s) -
        inner ℂ (nativeDressedCompanion k c r) (sourceValue k d s)) +
      -2 * Complex.I * (inner ℂ (sourceValue k c r) (completionCompanion k d s) -
        inner ℂ (completionCompanion k c r) (sourceValue k d s)) := by
  unfold polarizedSourceBalance
  rw [chiral_pairing_balance]
  simp only [sourceCompanion_eq_native_add_completion k c r hstrip,
    sourceCompanion_eq_native_add_completion k d s hstrip, inner_add_left, inner_add_right]
  ring

/-- All coefficient families and both internal radii share the same
shrinking-grid regularity threshold. Its diagonal is real storage. -/
theorem polarizedSourceBalance_eventually_complete (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ M : ℕ, ∀ c d : Fin N → ℂ, ∀ r s : ℝ,
      polarizedSourceBalance k c c r r = ((storage k c r).re : ℂ) ∧
      polarizedSourceBalance k c d r s = -2 * Complex.I *
        (∑ i : Fin N, ∑ j : Fin N,
          star (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
            completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
          (d j * (s : ℂ) ^ ((j : ℕ) + 1) /
            completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
          inner ℂ (completedNativeRadialChiralCauchyState k i)
            (completedNativeRadialChiralCauchyState k j) *
          canonicalC3BracketTfvdCompletedWronskianReadout M
            (canonicalCompletedC3RadialTiltPoint k j)
            (canonicalCompletedC3RadialTiltPoint k i)) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk M c d r s
  exact ⟨polarizedSourceBalance_self_eq_storage k c r (fun i => (hk i).2.2),
    polarizedSourceBalance_eq_bracketTfvd_sum M k c d r s (fun i => (hk i).1)⟩

end
end CarrySelfAdjointOperator.ChiralReturn
