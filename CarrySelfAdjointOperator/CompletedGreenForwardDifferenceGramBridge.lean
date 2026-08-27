import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceLimit
import CarrySelfAdjointOperator.CompletedGreenRealKernelClosure
import Mathlib.Tactic

/-!
# Concrete forward-difference Gram bridge

The scalar completed Green kernel already has the required all-order
forward-difference limit.  This file transports that limit back to an honest
Hilbert Gram.  The transport is performed only on the finite real sampling
grids used by each forward difference.

No Hilbert-valued derivative is taken.  The only factor-level inputs are the
two division-free Green representations and continuity of the completion
factor state.  The finite C3 state is concrete and globally continuous.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- Equality of two scalar kernels on the finite sampling rectangle is enough
to identify their normalized mixed forward differences. -/
theorem completedGreenKernelForwardDifference_eq_of_eq_on_grid
    (kernel kernel' : ℂ → ℂ → ℂ) (h : ℂ) (p q : ℕ)
    (hkernel : ∀ i ∈ Finset.range (p + 1),
      ∀ j ∈ Finset.range (q + 1),
        kernel (i • h) (j • h) = kernel' (i • h) (j • h)) :
    completedGreenKernelForwardDifference kernel h p q =
      completedGreenKernelForwardDifference kernel' h p q := by
  unfold completedGreenKernelForwardDifference
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact hkernel i hi j hj

/-- Every canonical complex sampling point is the cast of an explicit real
height. -/
theorem nsmul_canonicalGreenJetStep_eq_ofReal
    (k n : ℕ) :
    n • canonicalGreenJetStep k =
      (((n : ℝ) * ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
  simp [canonicalGreenJetStep, nsmul_eq_mul]

/-- Minimal vector interface used by the forward-difference construction.
It asks only for the normalized Gram kernel on the real sampling axis; no
extension to two arbitrary complex parameters is part of this definition. -/
def HasCompletedNativeRealAxisNormalizedGreenKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) : Prop :=
  ∀ x z : ℝ,
    completedNativeOperatorCharacteristic (x : ℂ) ≠ 0 →
    completedNativeOperatorCharacteristic (z : ℂ) ≠ 0 →
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state (x : ℂ))
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state (z : ℂ)) =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ)

/-- On the real axis, continuity of the completion-factor state closes the
diagonal of the concrete normalized product-ledger kernel at every point
where the completed characteristic is nonzero. -/
theorem completedNativeC3ProductLedger_normalizedKernel_ofReal_eq_dslope_of_continuous
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : Continuous xiState)
    (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) (x : ℂ))
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) (z : ℂ)) =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) := by
  apply completedNativeC3ProductLedger_normalizedKernel_ofReal_eq_dslope
    xiState hxi hnative x hxF
  · have hF := completedNativeOperatorCharacteristic_analyticAt
      (ofReal_mem_completedNativeHeightDomain x)
    exact continuousAt_normalizedCompletedGreenState
      hF.continuousAt hxF
      (completedNativeC3ProductLedgerState_continuousAt_ofReal
        x hxiContinuous.continuousAt)
  · exact ofReal_mem_completedNativeHeightDomain z
  · exact hzF

/-- Every fixed real sampling ray eventually remains in the proved
nonvanishing neighborhood of the centered characteristic. -/
theorem completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero
    (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      completedNativeOperatorCharacteristic
        (n • canonicalGreenJetStep k) ≠ 0 := by
  have hsample : Tendsto
      (fun k : ℕ ↦ n • canonicalGreenJetStep k) atTop (nhds 0) := by
    simpa [nsmul_eq_mul] using
      canonicalGreenJetStep_tendsto_zero.const_mul (n : ℂ)
  exact hsample.eventually
    (completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero)

/-- On every fixed finite real sampling grid, the concrete normalized
product-ledger kernel is eventually exactly the total `dslope` kernel. -/
theorem completedNativeC3ProductLedger_kernelForwardDifference_eventuallyEq_dslope
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : Continuous xiState)
    (p q : ℕ) :
    (fun k ↦ completedGreenKernelForwardDifference
      (fun w z ↦ inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) w)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) z))
      (canonicalGreenJetStep k) p q) =ᶠ[atTop]
    (fun k ↦ completedGreenKernelForwardDifference
      (fun w z ↦ dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) w z)
      (canonicalGreenJetStep k) p q) := by
  have hp : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  have hq : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        completedNativeOperatorCharacteristic
          (j • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero j
  filter_upwards [hp, hq] with k hkP hkQ
  apply completedGreenKernelForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [nsmul_canonicalGreenJetStep_eq_ofReal,
    nsmul_canonicalGreenJetStep_eq_ofReal]
  exact
    completedNativeC3ProductLedger_normalizedKernel_ofReal_eq_dslope_of_continuous
      xiState hxi hnative hxiContinuous
      ((i : ℝ) * ((k : ℝ) + 1)⁻¹)
      ((j : ℝ) * ((k : ℝ) + 1)⁻¹)
      (by simpa [canonicalGreenJetStep] using hkP i hi)
      (by simpa [canonicalGreenJetStep] using hkQ j hj)

/-- Any one-point Hilbert carrier realizing the real-axis normalized kernel
identifies its finite sampled Grams with the scalar `dslope` differences.
This is the carrier-level form of the bridge; it does not mention a factor
decomposition of the state. -/
theorem completedNative_kernelForwardDifference_eventuallyEq_dslope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (p q : ℕ) :
    (fun k ↦ completedGreenKernelForwardDifference
      (fun w z ↦ inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state w)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state z))
      (canonicalGreenJetStep k) p q) =ᶠ[atTop]
    (fun k ↦ completedGreenKernelForwardDifference
      (fun w z ↦ dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) w z)
      (canonicalGreenJetStep k) p q) := by
  have hp : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  have hq : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        completedNativeOperatorCharacteristic
          (j • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero j
  filter_upwards [hp, hq] with k hkP hkQ
  apply completedGreenKernelForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [nsmul_canonicalGreenJetStep_eq_ofReal,
    nsmul_canonicalGreenJetStep_eq_ofReal]
  exact hkernel
    ((i : ℝ) * ((k : ℝ) + 1)⁻¹)
    ((j : ℝ) * ((k : ℝ) + 1)⁻¹)
    (by simpa [canonicalGreenJetStep] using hkP i hi)
    (by simpa [canonicalGreenJetStep] using hkQ j hj)

/-- The existing factor construction supplies the minimal real-axis kernel
interface for its concrete product ledger. -/
theorem hasCompletedNativeRealAxisNormalizedGreenKernel_of_continuousGreenFactors
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : Continuous xiState) :
    HasCompletedNativeRealAxisNormalizedGreenKernel
      (completedNativeC3ProductLedgerState xiState) := by
  intro x z hxF hzF
  exact
    completedNativeC3ProductLedger_normalizedKernel_ofReal_eq_dslope_of_continuous
      xiState hxi hnative hxiContinuous x z hxF hzF

/-- A one-point carrier satisfying the real-axis kernel identity realizes all
four parity blocks of the canonical completed moment kernel in the limit. -/
theorem hasCompletedGreenForwardDifferenceGramLimit_of_realAxisKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    HasCompletedGreenForwardDifferenceGramLimit
      canonicalCompletedNativeLogDerivativeMoment
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state) := by
  intro i j
  let normalizedState := normalizedCompletedGreenState
    completedNativeOperatorCharacteristic state
  let response := completedGreenNormalizedResponse
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion
  have hfinite :=
    completedNative_kernelForwardDifference_eventuallyEq_dslope
      state hkernel
      (completedGreenParityOrder i) (completedGreenParityOrder j)
  have hgram :
      (fun k ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet normalizedState k i)
        (completedGreenForwardDifferenceParityJet normalizedState k j)).re) =ᶠ[atTop]
      (fun k ↦ (completedGreenKernelForwardDifference
        (fun w z ↦ dslope response w z)
        (canonicalGreenJetStep k)
        (completedGreenParityOrder i)
        (completedGreenParityOrder j)).re) := by
    filter_upwards [hfinite] with k hk
    have hi : completedGreenForwardDifferenceParityJet normalizedState k i =
        completedGreenForwardDifferenceJet normalizedState
          (canonicalGreenJetStep k) (completedGreenParityOrder i) := by
      cases i <;> rfl
    have hj : completedGreenForwardDifferenceParityJet normalizedState k j =
        completedGreenForwardDifferenceJet normalizedState
          (canonicalGreenJetStep k) (completedGreenParityOrder j) := by
      cases j <;> rfl
    rw [hi, hj,
      inner_completedGreenForwardDifferenceJet_eq_kernelForwardDifference]
    exact congrArg Complex.re
      (by simpa [normalizedState, response] using hk)
  exact
    (completedNativeGreenKernelForwardDifference_dslope_re_tendsto i j).congr'
      hgram.symm

/-- The real-axis vector identity alone is enough to make every finite
canonical Hankel pair positive semidefinite. -/
theorem canonicalCompletedNativeHankelPair_posSemidef_of_realAxisKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef ∧
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosSemidef :=
  hankelPair_posSemidef_of_completedGreenForwardDifferenceGramLimit
    (hasCompletedGreenForwardDifferenceGramLimit_of_realAxisKernel
      state hkernel) N

/-- The factor Green representations and continuity of their concrete
product carrier transport the scalar all-order limit to finite Hilbert Grams. -/
theorem completedNativeC3ProductLedger_hasForwardDifferenceGramLimit
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : Continuous xiState) :
    HasCompletedGreenForwardDifferenceGramLimit
      canonicalCompletedNativeLogDerivativeMoment
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)) :=
  hasCompletedGreenForwardDifferenceGramLimit_of_realAxisKernel
    (completedNativeC3ProductLedgerState xiState)
    (hasCompletedNativeRealAxisNormalizedGreenKernel_of_continuousGreenFactors
      xiState hxi hnative hxiContinuous)

/-- Consequently every finite Hankel pair of the canonical completed native
moments is positive semidefinite once the concrete completion-factor Green
state is supplied. -/
theorem canonicalCompletedNativeHankelPair_posSemidef_of_continuousGreenFactors
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : Continuous xiState)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef ∧
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosSemidef :=
  canonicalCompletedNativeHankelPair_posSemidef_of_realAxisKernel
    (completedNativeC3ProductLedgerState xiState)
    (hasCompletedNativeRealAxisNormalizedGreenKernel_of_continuousGreenFactors
      xiState hxi hnative hxiContinuous) N

end

end CarrySelfAdjointOperator
