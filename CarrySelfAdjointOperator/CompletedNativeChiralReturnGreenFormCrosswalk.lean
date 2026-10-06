import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace

/-!
# Complete chiral source orientation and the corrected Green ledger

The existing Cauchy syntheses are expanded before evaluating the signed
orientation. Each ordered pair uses the existing completed TFVD Wronskian
and its full Green ledger. This does not identify the Cauchy carrier with the
finite C3 port or with the all-bases material stencil carrier.
-/

namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open NativeCarrySpectralWeyl.Boundary
open CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- The existing Green form specializes to the signed source orientation.
It is skew-Hermitian, with no nonnegative sign asserted. -/
theorem source_cross_eq_cauchy_greenForm (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im =
      -2 * (greenForm (𝕜 := ℂ)
        (sourceValue k c r, sourceCompanion k c r)
        (sourceValue k c r, sourceCompanion k c r)).im := by
  have h := congrArg Complex.im
    (inner_conj_symm (sourceValue k c r) (sourceCompanion k c r))
  simp only [Complex.conj_im] at h
  simp only [greenForm, Complex.sub_im]
  linarith

/-- Expansion of both source channels, with all ordered cross terms retained.
The Wronskian uses the right sample first, as required by conjugate-linearity
in the first Hilbert argument. -/
theorem mixed_synthesis_eq_wronskian_sum
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (u : ι → E) (d F C : ι → ℂ) :
    inner ℂ (∑ i, (d i * F i) • u i) (∑ j, (d j * C j) • u j) -
      inner ℂ (∑ i, (d i * C i) • u i) (∑ j, (d j * F j) • u j) =
      ∑ i, ∑ j, star (d i) * d j * inner ℂ (u i) (u j) *
        mixedScalarBoundaryWedge (F j) (C j) (F i) (C i) := by
  simp_rw [sum_inner]
  simp_rw [inner_sum]
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

/-- Exact completed TFVD Wronskian realization of the Cauchy mixed pairing,
at every cutoff. No inversion of the trace projection is used. -/
theorem source_cross_eq_bracketTfvd_wronskian_sum (M k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im =
      2 * (∑ i : Fin N, ∑ j : Fin N,
        star (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
        (c j * (r : ℂ) ^ ((j : ℕ) + 1) /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
        inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        canonicalC3BracketTfvdCompletedWronskianReadout M
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint k i)).im := by
  have hsum := mixed_synthesis_eq_wronskian_sum
    (fun i : Fin N => completedNativeRadialChiralCauchyState k i)
    (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => -deriv completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i))
  simp only [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime M
    (hstrip _) (hstrip _), completedGreenWronskian, mixedScalarBoundaryWedge] at *
  have hV : (∑ i : Fin N, (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)) •
      completedNativeRadialChiralCauchyState k i) = sourceValue k c r := by
    simp only [sourceValue, div_mul_eq_mul_div]
  have hC : (∑ i : Fin N, (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
      (-deriv completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i))) •
      completedNativeRadialChiralCauchyState k i) = sourceCompanion k c r := by
    simp only [sourceCompanion, div_mul_eq_mul_div]
  rw [hV, hC] at hsum
  rw [← hsum, Complex.sub_im]
  have h := congrArg Complex.im
    (inner_conj_symm (sourceValue k c r) (sourceCompanion k c r))
  simp only [Complex.conj_im] at h
  linarith

/-- The exact Green-port contribution plus all five existing correction
channels. The chart denominator is certified upstream on the strip. -/
theorem bracketTfvd_wronskian_eq_corrected_green_ledger (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalC3BracketTfvdCompletedWronskianReadout M z w =
      (mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalC3BracketTfvdMixedGreenReadout M
          (operatorHeightParameter z) (operatorHeightParameter w) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w).archimedeanChart) /
        mixedHermitianWeight canonicalC3ChartFactorHeight z w := by
  have hn : mixedHermitianWeight canonicalC3ChartFactorHeight z w ≠ 0 := by
    unfold mixedHermitianWeight
    exact mul_ne_zero (canonicalC3ChartFactorHeight_ne_zero hz)
      ((map_ne_zero (starRingEnd ℂ)).2 (canonicalC3ChartFactorHeight_ne_zero hw))
  apply (eq_div_iff hn).2
  simpa only [mul_comm] using
    completedWronskian_factors_through_bracketTfvd_then_green M hz hw

/-- Complete crosswalk to the geometric Green port with its unchanged
correction ledger. No term of either finite synthesis is dropped. -/
theorem source_cross_eq_corrected_green_ledger (M k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let L := fun i j : Fin N => canonicalCompletedC3FiniteFNegFPrimeMixedChannels M (z j) (z i)
    4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im =
      2 * (∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        ((mixedHermitianWeight nativeXiCompletionFactor (z j) (z i) *
          canonicalC3BracketTfvdMixedGreenReadout M
            (operatorHeightParameter (z j)) (operatorHeightParameter (z i)) +
          (L i j).greenProvenance + (L i j).offDiagonal +
          (L i j).readoutResidual + (L i j).tailCompletion +
          (L i j).archimedeanChart) /
          mixedHermitianWeight canonicalC3ChartFactorHeight (z j) (z i))).im := by
  dsimp only
  rw [source_cross_eq_bracketTfvd_wronskian_sum M k c r hstrip]
  simp_rw [bracketTfvd_wronskian_eq_corrected_green_ledger M (hstrip _) (hstrip _)]

/-- No new global regularity premise: on each finite family the same
shrinking-grid threshold works for all cutoffs, coefficients and radii. -/
theorem source_cross_eventually_eq_corrected_green_ledger (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ M : ℕ, ∀ c : Fin N → ℂ, ∀ r : ℝ,
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let L := fun i j : Fin N => canonicalCompletedC3FiniteFNegFPrimeMixedChannels M (z j) (z i)
    4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im =
      2 * (∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        ((mixedHermitianWeight nativeXiCompletionFactor (z j) (z i) *
          canonicalC3BracketTfvdMixedGreenReadout M
            (operatorHeightParameter (z j)) (operatorHeightParameter (z i)) +
          (L i j).greenProvenance + (L i j).offDiagonal +
          (L i j).readoutResidual + (L i j).tailCompletion +
          (L i j).archimedeanChart) /
          mixedHermitianWeight canonicalC3ChartFactorHeight (z j) (z i))).im := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk M c r
  exact source_cross_eq_corrected_green_ledger M k c r (fun i => (hk i).1)

end
end CarrySelfAdjointOperator.ChiralReturn
