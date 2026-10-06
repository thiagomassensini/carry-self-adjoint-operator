import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralCarrier
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence

/-!
# Signed projective/chiral forward-difference pairing

The vectors are finite combinations of the existing radial projective graph
states. The shifted grid and factorial normalization are those of the existing
scalar coefficient extractor. Both channels stay explicit. No positive Hilbert
Gram, state convergence, contractivity or prime-depth carrier identification is
asserted.
-/

namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section

/-- Sesquilinearity with Mathlib's conjugate-linear first argument. -/
theorem projectiveChiralForm_smul (c d : ℂ)
    (u v : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (c • u) (d • v) =
      conj c * d * canonicalCompletedNativeProjectiveChiralForm u v := by
  simp only [canonicalCompletedNativeProjectiveChiralForm,
    Prod.smul_fst, Prod.smul_snd, inner_smul_left, inner_smul_right]
  ring

private theorem form_add_left
    (u v w : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (u + v) w =
      canonicalCompletedNativeProjectiveChiralForm u w +
        canonicalCompletedNativeProjectiveChiralForm v w := by
  simp only [canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

private theorem form_add_right
    (u v w : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm u (v + w) =
      canonicalCompletedNativeProjectiveChiralForm u v +
        canonicalCompletedNativeProjectiveChiralForm u w := by
  simp only [canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

private theorem form_sum_left {ι : Type*}
    (s : Finset ι) (u : ι → CanonicalCompletedNativeProjectiveChiralCarrier)
    (v : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (∑ i ∈ s, u i) v =
      ∑ i ∈ s, canonicalCompletedNativeProjectiveChiralForm (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [canonicalCompletedNativeProjectiveChiralForm]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, form_add_left, ih]

private theorem form_sum_right {ι : Type*}
    (s : Finset ι) (u : CanonicalCompletedNativeProjectiveChiralCarrier)
    (v : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm u (∑ i ∈ s, v i) =
      ∑ i ∈ s, canonicalCompletedNativeProjectiveChiralForm u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [canonicalCompletedNativeProjectiveChiralForm]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, form_add_right, ih]

/-- Factorial-normalized difference on the existing shifted radial grid.
The order-zero vector is the first nonzero radial sample, not the origin. -/
def projectiveChiralDifferenceJet (k order : ℕ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  (((order.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ order)⁻¹) •
    ∑ r ∈ Finset.range (order + 1), completedGreenForwardWeight order r •
      canonicalCompletedNativeRadialProjectiveChiralState k r

private theorem conj_forwardWeight (order r : ℕ) :
    conj (completedGreenForwardWeight order r) = completedGreenForwardWeight order r := by
  simp [completedGreenForwardWeight]

/-- Exact pairing of the finite vector combinations, before any regularity
or scalar-kernel identification. -/
theorem projectiveChiralDifferenceJet_pairing_eq_weightedSum (k p q : ℕ) :
    canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q) =
    conj (((p.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ p)⁻¹) *
      (((q.factorial : ℂ) * canonicalCompletedC3RadialSecondStep k ^ q)⁻¹) *
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        completedGreenForwardWeight p i * completedGreenForwardWeight q j *
          canonicalCompletedNativeProjectiveChiralForm
            (canonicalCompletedNativeRadialProjectiveChiralState k i)
            (canonicalCompletedNativeRadialProjectiveChiralState k j) := by
  unfold projectiveChiralDifferenceJet
  rw [projectiveChiralForm_smul, form_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [form_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [projectiveChiralForm_smul, conj_forwardWeight]

/-- On a regular finite section the signed vector pairing is exactly the
existing shifted mixed forward difference of the polarized dslope kernel. -/
theorem projectiveChiralDifferenceJet_pairing_eq_dslope
    (k p q : ℕ)
    (hregular : ∀ i : Fin (p + q + 1),
      canonicalCompletedC3RadialTiltPoint k i ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q) =
    completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q := by
  rw [projectiveChiralDifferenceJet_pairing_eq_weightedSum]
  unfold completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i hi
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i < p + q + 1 := by have := Finset.mem_range.mp hi; omega
  have hj' : j < p + q + 1 := by have := Finset.mem_range.mp hj; omega
  have heq := canonicalCompletedNativeRadialProjectiveChiralForm_eq_dslope
    k (p + q + 1) hregular ⟨i, hi'⟩ ⟨j, hj'⟩
  change canonicalCompletedNativeProjectiveChiralForm
    (canonicalCompletedNativeRadialProjectiveChiralState k i)
    (canonicalCompletedNativeRadialProjectiveChiralState k j) =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
    at heq
  rw [heq, canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul,
    canonicalCompletedC3RadialTiltPoint_eq_step_add_nsmul]
  simp [completedGreenForwardWeight, zsmul_eq_mul]
  ring

/-- No regularity hypothesis is imposed globally: it holds eventually for
each finite stencil by the already established centered germ. -/
theorem projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope (p q : ℕ) :
    (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q)) =ᶠ[atTop]
    (fun k => completedGreenKernelTwoStepShiftedForwardDifference
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k)
      (canonicalCompletedC3RadialSecondStep k) p q) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (p + q + 1)]
    with k hk
  exact projectiveChiralDifferenceJet_pairing_eq_dslope k p q hk

/-- Low-order finite stencil canaries, with regularity discharged eventually. -/
theorem projectiveChiralDifferenceJet_pairing_canaries :
    (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 0) (projectiveChiralDifferenceJet k 0)) =ᶠ[atTop]
      (fun k => completedGreenKernelTwoStepShiftedForwardDifference
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k) 0 0) ∧
    (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 0) (projectiveChiralDifferenceJet k 1)) =ᶠ[atTop]
      (fun k => completedGreenKernelTwoStepShiftedForwardDifference
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k) 0 1) ∧
    (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 1) (projectiveChiralDifferenceJet k 1)) =ᶠ[atTop]
      (fun k => completedGreenKernelTwoStepShiftedForwardDifference
        canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialSecondStep k) (canonicalCompletedC3RadialSecondStep k) 1 1) :=
  ⟨projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope 0 0,
   projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope 0 1,
   projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope 1 1⟩

/-- First extract the existing polarized canonical coefficient. No vector
limit or positivity hypothesis is required. -/
theorem projectiveChiralDifferenceJet_pairing_tendsto_coefficient (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q))
      atTop (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hdiag : Tendsto (fun k : ℕ => (k, k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have hlimit := (completedNativePolarizedDslope_shiftedRadial_tendsto p q).comp hdiag
  exact hlimit.congr' (projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope p q).symm

private theorem pairing_tendsto_geometric (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q))
      atTop (nhds (polarizedGreenMomentCoefficient primeDepthGeometricMoment p q)) := by
  rw [primeDepthGeometricMoment_eq_canonical]
  exact projectiveChiralDifferenceJet_pairing_tendsto_coefficient p q

/-- Literal derivative-order canaries have targets g0, zero, g1.
They are not three consecutive entries g0,g1,g2. -/
theorem projectiveChiralDifferenceJet_pairing_canary_limits :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 0) (projectiveChiralDifferenceJet k 0))
      atTop (nhds (primeDepthGeometricMoment 0 : ℂ)) ∧
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 0) (projectiveChiralDifferenceJet k 1))
      atTop (nhds (0 : ℂ)) ∧
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 1) (projectiveChiralDifferenceJet k 1))
      atTop (nhds (primeDepthGeometricMoment 1 : ℂ)) := by
  have h00 := pairing_tendsto_geometric 0 0
  have h01 := pairing_tendsto_geometric 0 1
  have h11 := pairing_tendsto_geometric 1 1
  simpa [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using
    And.intro h00 (And.intro h01 h11)

/-- All orders of the signed geometric pairing converge to the prime-depth
polarized coefficient. The identification by uniqueness is used only after
extracting the existing scalar-kernel coefficient. -/
theorem projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k p) (projectiveChiralDifferenceJet k q))
      atTop (nhds (polarizedGreenMomentCoefficient primeDepthGeometricMoment p q)) :=
  pairing_tendsto_geometric p q

/-- Even-even orders read g_(p+q). -/
theorem projectiveChiralDifferenceJet_even_even_tendsto (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (2 * p)) (projectiveChiralDifferenceJet k (2 * q)))
      atTop (nhds (primeDepthGeometricMoment (p + q) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_even] using
    projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (2 * p) (2 * q)

/-- Odd-odd orders read g_(p+q+1). -/
theorem projectiveChiralDifferenceJet_odd_odd_tendsto (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (2 * p + 1))
      (projectiveChiralDifferenceJet k (2 * q + 1)))
      atTop (nhds (primeDepthGeometricMoment (p + q + 1) : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_odd_odd] using
    projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (2 * p + 1) (2 * q + 1)

/-- Mixed even-odd pairing tends to zero; no finite-step orthogonality is
assumed. -/
theorem projectiveChiralDifferenceJet_even_odd_tendsto (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (2 * p))
      (projectiveChiralDifferenceJet k (2 * q + 1)))
      atTop (nhds (0 : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_even_odd] using
    projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (2 * p) (2 * q + 1)

/-- Mixed odd-even pairing tends to zero. -/
theorem projectiveChiralDifferenceJet_odd_even_tendsto (p q : ℕ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k (2 * p + 1))
      (projectiveChiralDifferenceJet k (2 * q)))
      atTop (nhds (0 : ℂ)) := by
  simpa only [polarizedGreenMomentCoefficient_odd_even] using
    projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient (2 * p + 1) (2 * q)

/-- The g2 low-order check uses literal orders (2,2). -/
theorem projectiveChiralDifferenceJet_two_two_tendsto :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k 2) (projectiveChiralDifferenceJet k 2))
      atTop (nhds (primeDepthGeometricMoment 2 : ℂ)) := by
  simpa using projectiveChiralDifferenceJet_even_even_tendsto 1 1

end
end CarrySelfAdjointOperator
