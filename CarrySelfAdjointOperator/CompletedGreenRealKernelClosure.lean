import CarrySelfAdjointOperator.CompletedGreenDiagonalClosure
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic

/-!
# Removable closure of the normalized completed Green kernel

The division-free Green identity determines the normalized point-state Gram
away from collisions.  Continuity determines the diagonal.  This file joins
those two statements into one total divided-difference identity using
Mathlib's `dslope`, whose collision value is the derivative.

The result is still vector honest: the left side is the inner product of the
same normalized Hilbert state at both parameters.  Only after that identity
is established is the kernel replaced by its scalar divided-difference
formula.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter Set

noncomputable section

/-- Off-diagonal Green polarization and the continuous diagonal closure are
one total `dslope` identity.  The second parameter may be complex; only the
fixed first parameter must be invariant under conjugation, together with its
scalar response. -/
theorem normalizedCompletedGreenState_inner_eq_dslope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {domain : Set ℂ} {F Psi : ℂ → ℂ} {state : ℂ → E}
    (hgreen : HasDivisionFreeGreenRepresentationOn domain F Psi state)
    {x z : ℂ}
    (hdomain : domain ∈ nhds x)
    (hF : ∀ᶠ u in nhds x, F u ≠ 0)
    (hxReal : (starRingEnd ℂ) x = x)
    (hresponseReal :
      (starRingEnd ℂ) (completedGreenNormalizedResponse F Psi x) =
        completedGreenNormalizedResponse F Psi x)
    (hstate : ContinuousAt (normalizedCompletedGreenState F state) x)
    (hresponse : DifferentiableAt ℂ
      (completedGreenNormalizedResponse F Psi) x)
    (hzDomain : z ∈ domain) (hzF : F z ≠ 0) :
    inner ℂ
        (normalizedCompletedGreenState F state x)
        (normalizedCompletedGreenState F state z) =
      dslope (completedGreenNormalizedResponse F Psi) x z := by
  have hxDomain : x ∈ domain := mem_of_mem_nhds hdomain
  have hxF : F x ≠ 0 := mem_of_mem_nhds hF
  by_cases hzx : z = x
  · subst z
    rw [dslope_same]
    exact normalizedCompletedGreenState_inner_self_eq_responseDerivative
      hgreen hdomain hF hxReal hresponseReal hstate hresponse.hasDerivAt
  · rw [dslope_of_ne _ hzx, slope_def_module]
    simp only [smul_eq_mul]
    have hpolarized := normalizedCompletedGreenState_polarizedResponse
      hgreen hzDomain hxDomain hzF hxF
    rw [hxReal, hresponseReal] at hpolarized
    calc
      inner ℂ
          (normalizedCompletedGreenState F state x)
          (normalizedCompletedGreenState F state z) =
        (z - x)⁻¹ *
          ((z - x) *
            inner ℂ
              (normalizedCompletedGreenState F state x)
              (normalizedCompletedGreenState F state z)) := by
          field_simp [sub_ne_zero.mpr hzx]
      _ = (z - x)⁻¹ *
          (completedGreenNormalizedResponse F Psi z -
            completedGreenNormalizedResponse F Psi x) := by
        rw [hpolarized]

/-- At the centered origin, the canonical completed response and the
normalized product-ledger Gram are one total divided-difference kernel.  The
factor Green representations construct the off-diagonal identity, while the
already-proved continuity theorem fills the collision. -/
theorem completedNativeC3ProductLedger_normalizedKernel_zero_eq_dslope
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0)
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) 0)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) z) =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) 0 z := by
  apply normalizedCompletedGreenState_inner_eq_dslope
    (completedNativeC3ProductLedger_greenRepresentationOn_of_factors
      xiState hxi hnative)
  · exact isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  · exact
      completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero
  · simp
  · simp [completedNativeGreenNormalizedResponse_zero]
  · exact continuousAt_normalizedCompletedGreenState
      completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt
      completedNativeOperatorCharacteristic_zero_ne_zero
      (completedNativeC3ProductLedgerState_continuousAt_zero hxiContinuous)
  · have hcharacteristic :=
      completedNativeOperatorCharacteristic_analyticAt
        zero_mem_completedNativeHeightDomain
    rw [show completedNativeOperatorBoundaryCompanion =
        fun u => -deriv completedNativeOperatorCharacteristic u by
      funext u
      exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u]
    unfold completedGreenNormalizedResponse
    exact (hcharacteristic.deriv.neg.div
      (analyticAt_const.mul hcharacteristic)
      (mul_ne_zero (by norm_num)
        completedNativeOperatorCharacteristic_zero_ne_zero)).differentiableAt
  · exact hzDomain
  · exact hzF

/-- The canonical normalized response is real on the complete native-height
axis.  Both its value and derivative channels are inherited from the same
real-valued completed characteristic. -/
theorem completedNativeGreenNormalizedResponse_ofReal_conj
    (time : ℝ) :
    (starRingEnd ℂ)
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion (time : ℂ)) =
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (time : ℂ) := by
  have hvalueIm :
      (completedNativeOperatorCharacteristic (time : ℂ)).im = 0 :=
    completedNativeOperatorCharacteristic_ofReal_im_eq_zero time
  have hderivIm :
      (deriv completedNativeOperatorCharacteristic (time : ℂ)).im = 0 := by
    have h := iteratedDeriv_completedNativeOperatorCharacteristic_zero_im
      1 time
    simpa [iteratedDeriv_succ] using h
  have hvalueFixed :
      (starRingEnd ℂ)
          (completedNativeOperatorCharacteristic (time : ℂ)) =
        completedNativeOperatorCharacteristic (time : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hvalueIm]
  have hderivFixed :
      (starRingEnd ℂ)
          (deriv completedNativeOperatorCharacteristic (time : ℂ)) =
        deriv completedNativeOperatorCharacteristic (time : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hderivIm]
  unfold completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  simp only [map_div₀, map_neg, map_mul, map_ofNat]
  rw [hvalueFixed, hderivFixed]

/-- Real-axis specialization at an arbitrary base point.  Once continuity of
the actual normalized carrier is available at that point, no separate
diagonal value remains in the Green kernel. -/
theorem completedNativeC3ProductLedger_normalizedKernel_ofReal_eq_dslope
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (time : ℝ)
    (hcenterF :
      completedNativeOperatorCharacteristic (time : ℂ) ≠ 0)
    (hstate : ContinuousAt
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        (completedNativeC3ProductLedgerState xiState)) (time : ℂ))
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) (time : ℂ))
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic
          (completedNativeC3ProductLedgerState xiState) z) =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (time : ℂ) z := by
  have hcharacteristic := completedNativeOperatorCharacteristic_analyticAt
    (ofReal_mem_completedNativeHeightDomain time)
  apply normalizedCompletedGreenState_inner_eq_dslope
    (completedNativeC3ProductLedger_greenRepresentationOn_of_factors
      xiState hxi hnative)
  · exact isOpen_completedNativeHeightDomain.mem_nhds
      (ofReal_mem_completedNativeHeightDomain time)
  · exact hcharacteristic.continuousAt.eventually_ne hcenterF
  · simp
  · exact completedNativeGreenNormalizedResponse_ofReal_conj time
  · exact hstate
  · rw [show completedNativeOperatorBoundaryCompanion =
        fun u => -deriv completedNativeOperatorCharacteristic u by
      funext u
      exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u]
    unfold completedGreenNormalizedResponse
    exact (hcharacteristic.deriv.neg.div
      (analyticAt_const.mul hcharacteristic)
      (mul_ne_zero (by norm_num) hcenterF)).differentiableAt
  · exact hzDomain
  · exact hzF

end

end CarrySelfAdjointOperator
