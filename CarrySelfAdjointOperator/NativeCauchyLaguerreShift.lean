import CarrySelfAdjointOperator.NativeCauchyLaguerreIsometry
import CPFormal.Analytic.CpCarryL2UnilateralShift
import GreenFrame.Concrete.Finite.L2CoordinateMaskLimit

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate lp ENNReal
open Filter Topology CPFormal.Analytic.Cp GreenFrame.Concrete
noncomputable section
set_option autoImplicit false

/-- The existing backward shift acts on the literal physical columns. -/
theorem backwardShift_laguerreColumn (n j : ℕ) :
    carryVerticalL2BackwardShift n (laguerreColumn j) =
      (rho j ^ n : ℂ) • laguerreColumn j := by
  ext r
  simp only [carryVerticalL2BackwardShift_apply, laguerreColumn_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [feature, pow_add]
  push_cast
  ring

/-- Diagonal action on the ORIGINAL physical half densities, before completion. -/
def physicalShiftSynthesis (n : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalCauchySpace :=
  Finsupp.linearCombination ℂ (fun j => (rho j ^ n : ℂ) • physicalCauchyFeature j)

theorem physicalShiftSynthesis_intertwines (n : ℕ) (c : ℕ →₀ ℂ) :
    cauchyLaguerreIsometry (physicalShiftSynthesis n c) =
      carryVerticalL2BackwardShift n (laguerreColumnSynthesis c) := by
  classical
  simp only [physicalShiftSynthesis, laguerreColumnSynthesis,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    cauchyLaguerreIsometry_feature, backwardShift_laguerreColumn]

private theorem physicalShiftSynthesis_bound (n : ℕ) (c : ℕ →₀ ℂ) :
    ‖physicalShiftSynthesis n c‖ ≤ 1 * ‖physicalCauchyEmbedding c‖ := by
  rw [← cauchyLaguerreIsometry.norm_map, physicalShiftSynthesis_intertwines]
  change ‖carryVerticalL2BackwardShiftLinear n (laguerreColumnSynthesis c)‖ ≤ _
  rw [one_mul]
  exact (carryVerticalL2BackwardShiftLinear_norm_le n _).trans_eq
    (laguerreColumnSynthesis_norm c)

/-- Contractive extension of the physical diagonal action, with its original metric. -/
def physicalCauchyShift (n : ℕ) : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  (physicalShiftSynthesis n).extendOfNorm physicalCauchyEmbedding

theorem physicalCauchyShift_synthesis (n : ℕ) (c : ℕ →₀ ℂ) :
    physicalCauchyShift n (physicalCauchyEmbedding c) = physicalShiftSynthesis n c :=
  LinearMap.extendOfNorm_eq physicalCauchyEmbedding_dense
    ⟨1, physicalShiftSynthesis_bound n⟩ c

theorem physicalCauchyShift_intertwines (n : ℕ) (x : PhysicalCauchySpace) :
    cauchyLaguerreIsometry (physicalCauchyShift n x) =
      carryVerticalL2BackwardShift n (cauchyLaguerreIsometry x) := by
  refine physicalCauchyEmbedding_dense.induction_on x
    (isClosed_eq (cauchyLaguerreIsometry.continuous.comp (physicalCauchyShift n).continuous)
      ((carryVerticalL2BackwardShift n).continuous.comp cauchyLaguerreIsometry.continuous)) ?_
  intro c
  rw [physicalCauchyShift_synthesis, cauchyLaguerreIsometry_synthesis,
    physicalShiftSynthesis_intertwines]

theorem physicalCauchyShift_feature (n j : ℕ) :
    physicalCauchyShift n (physicalCauchyFeature j) =
      (rho j ^ n : ℂ) • physicalCauchyFeature j := by
  rw [physicalCauchyFeature, physicalCauchyShift_synthesis]
  simp [physicalShiftSynthesis, physicalCauchyFeature]

theorem physicalCauchyShift_norm_le (n : ℕ) (x : PhysicalCauchySpace) :
    ‖physicalCauchyShift n x‖ ≤ ‖x‖ := by
  rw [← cauchyLaguerreIsometry.norm_map, physicalCauchyShift_intertwines,
    ← cauchyLaguerreIsometry.norm_map x]
  exact carryVerticalL2BackwardShiftLinear_norm_le n _

theorem physicalCauchyShift_opNorm_le_one (n : ℕ) : ‖physicalCauchyShift n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using physicalCauchyShift_norm_le n x

theorem physicalCauchyShift_zero : physicalCauchyShift 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply cauchyLaguerreIsometry.injective
  rw [physicalCauchyShift_intertwines]
  ext r
  simp

theorem physicalCauchyShift_add (n m : ℕ) :
    physicalCauchyShift (n + m) = (physicalCauchyShift n).comp (physicalCauchyShift m) := by
  apply ContinuousLinearMap.ext
  intro x
  apply cauchyLaguerreIsometry.injective
  simp only [ContinuousLinearMap.comp_apply, physicalCauchyShift_intertwines]
  ext r
  simp [Nat.add_comm, Nat.add_left_comm]

theorem physicalCauchyShift_eq_pow (n : ℕ) :
    physicalCauchyShift n = physicalCauchyShift 1 ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact physicalCauchyShift_zero
  | succ n ih =>
    rw [pow_succ', ← ih, Nat.add_comm n 1, physicalCauchyShift_add]
    rfl

/-- Closed range invariance follows from the completed intertwiner, without surjectivity. -/
theorem backwardShift_preserves_physicalRange (n : ℕ) {y : ℓ²(ℕ, ℂ)}
    (hy : y ∈ cauchyLaguerreIsometry.toLinearMap.range) :
    carryVerticalL2BackwardShift n y ∈ cauchyLaguerreIsometry.toLinearMap.range := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨physicalCauchyShift n x, physicalCauchyShift_intertwines n x⟩

/-- The head is the existing orthogonal coordinate mask. -/
def laguerreHead (R : ℕ) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  l2CoordinateMaskCLM (fun r : ℕ => r ≤ R)

@[simp] theorem laguerreHead_apply (R : ℕ) (x : ℓ²(ℕ, ℂ)) (r : ℕ) :
    laguerreHead R x r = if r ≤ R then x r else 0 := rfl

theorem laguerreHead_idempotent (R : ℕ) :
    (laguerreHead R).comp (laguerreHead R) = laguerreHead R :=
  l2CoordinateMask_idempotent _

theorem laguerreHead_isSelfAdjoint (R : ℕ) : IsSelfAdjoint (laguerreHead R) :=
  l2CoordinateMask_isSelfAdjoint _

theorem laguerreHead_tendsto (x : ℓ²(ℕ, ℂ)) :
    Tendsto (fun R => laguerreHead R x) atTop (nhds x) :=
  l2CoordinateMask_tendsto (fun R r : ℕ => r ≤ R)
    (fun r => eventually_atTop.2 ⟨r, fun _R hR => hR⟩) x

theorem laguerreHead_residual_energy_tendsto_zero (x : ℓ²(ℕ, ℂ)) :
    Tendsto (fun R => ‖laguerreHead R x - x‖ ^ 2) atTop (nhds 0) :=
  l2CoordinateMask_energy_tendsto_zero (fun R r : ℕ => r ≤ R)
    (fun r => eventually_atTop.2 ⟨r, fun _R hR => hR⟩) x

/-- Tail stability on the target, using the actual convergent quadratic series. -/
theorem backwardShift_tendsto_zero (x : ℓ²(ℕ, ℂ)) :
    Tendsto (fun n => carryVerticalL2BackwardShift n x) atTop (nhds 0) := by
  have hs := residualL2_normSq_summable x
  have he (n : ℕ) : ‖carryVerticalL2BackwardShift n x‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ r ∈ Finset.range n, Complex.normSq (x r) := by
    rw [← residualL2_normSq_tsum_eq_norm_sq,
      ← residualL2_normSq_tsum_eq_norm_sq, ← hs.sum_add_tsum_nat_add n]
    simp only [carryVerticalL2BackwardShift_apply]
    ring
  have hsq : Tendsto (fun n => ‖carryVerticalL2BackwardShift n x‖ ^ 2) atTop (nhds 0) := by
    simp_rw [he]
    have h := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub hs.hasSum.tendsto_sum_nat
    rw [residualL2_normSq_tsum_eq_norm_sq, sub_self] at h
    exact h
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem physicalCauchyShift_tendsto_zero (x : PhysicalCauchySpace) :
    Tendsto (fun n => physicalCauchyShift n x) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_zero_iff_norm_tendsto_zero.mp
    (backwardShift_tendsto_zero (cauchyLaguerreIsometry x))
  simpa only [← physicalCauchyShift_intertwines, cauchyLaguerreIsometry.norm_map] using h

end
end CarrySelfAdjointOperator.NativeLaguerre
