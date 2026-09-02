import CarrySelfAdjointOperator.CompletedC3CentralChartFreeSewingAudit
import CarrySelfAdjointOperator.CompletedGreenDiagonalClosure
import CarrySelfAdjointOperator.CompletedNativeGreenWeylHeight
import CarrySelfAdjointOperator.CompletedNativeProductMomentCenter
import Mathlib.Tactic

/-!
# Central product-dressing audit

The concrete real-axis positive carrier orthogonalizes its ordinary, log-jet,
and retained-residual coordinates before taking a Gram product.  The exact
Green product rule supplies a different, upstream construction.  If `A` and
`G` possess Green states `a` and `g`, the state of `A * G` is

`G(z) • a(z) ⊕ A(z) • g(z)`.

After the canonical `sqrt 2 * A * G` normalization this is exactly the direct
sum of the separately normalized factor states.  This file records that
center-only calculation and identifies the first inputs which are not yet
constructed: genuine Green representations of the xi factor and of the
native scalar by the canonical enriched C3 state.

No theta representation, zero data, confinement statement, fixed chiral
return, all-order promotion, or `h₁` gate is used.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## The canonical product transport before scalarization -/

/-- At the center, the already-defined normalized completed product ledger is
literally the direct sum of the two separately normalized factor states.
This is the canonical multiplicative dressing; no fitted weight or mixing
matrix occurs. -/
theorem canonicalCompletedNativeNormalizedGreenState_zero_eq_factorStates
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    canonicalCompletedNativeNormalizedGreenState xiState 0 =
      WithLp.toLp 2
        (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0,
          normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0) := by
  have hA : nativeXiCompletionFactor 0 ≠ 0 :=
    nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  have hG : nativeHeightScalar 0 ≠ 0 :=
    nativeHeightScalar_zero_ne_zero
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [canonicalCompletedNativeNormalizedGreenState,
      normalizedCompletedGreenState, completedNativeOperatorCharacteristic,
      nativeHeightScalar, completedNativeC3ProductLedgerState,
      weightedProductGreenState, WithLp.ofLp_smul, Prod.smul_mk,
      smul_smul]
    change
      (((((Real.sqrt 2 : ℝ) : ℂ) *
            (nativeXiCompletionFactor 0 * nativeHeightScalar 0))⁻¹ *
          nativeHeightScalar 0) • xiState 0) =
        ((((Real.sqrt 2 : ℝ) : ℂ) *
            nativeXiCompletionFactor 0)⁻¹ • xiState 0)
    congr 1
    field_simp [hA, hG]
  · simp only [canonicalCompletedNativeNormalizedGreenState,
      normalizedCompletedGreenState, completedNativeOperatorCharacteristic,
      nativeHeightScalar, completedNativeC3ProductLedgerState,
      weightedProductGreenState, WithLp.ofLp_smul, Prod.smul_mk,
      smul_smul]
    change
      (((((Real.sqrt 2 : ℝ) : ℂ) *
            (nativeXiCompletionFactor 0 * nativeHeightScalar 0))⁻¹ *
          nativeXiCompletionFactor 0) •
          canonicalCompletedOperatorC3HilbertState 0) =
        ((((Real.sqrt 2 : ℝ) : ℂ) * nativeHeightScalar 0)⁻¹ •
          canonicalCompletedOperatorC3HilbertState 0)
    congr 1
    field_simp [hA, hG]

/-- Consequently the center Gram of the product-dressed state is exactly the
sum of the two factor Grams.  In particular, the product rule creates no
ordinary/log/residual cross term: its two lossless coordinates are the xi
factor state and the native-factor state. -/
theorem inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_factorGrams
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    inner ℂ
        (canonicalCompletedNativeNormalizedGreenState xiState 0)
        (canonicalCompletedNativeNormalizedGreenState xiState 0) =
      inner ℂ
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0)
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0) +
        inner ℂ
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0)
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0) := by
  rw [canonicalCompletedNativeNormalizedGreenState_zero_eq_factorStates]
  exact WithLp.prod_inner_apply _ _

/-! ## The scalar order-two transport and the central Gram target -/

/-- The derivative of the completed normalized response at the center is the
zeroth canonical moment.  This is extracted from the existing analytic
Taylor-coefficient theorem, not assumed as a new sewing identity. -/
theorem completedNativeGreenNormalizedResponse_hasDerivAt_h0 :
    HasDerivAt
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion)
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) 0 := by
  have hderiv :=
    completedNativeGreenNormalizedResponse_analyticAt.differentiableAt.hasDerivAt
  have hvalue :
      deriv
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    rw [← completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0]
    simp [completedNativeGreenResponseTaylorCoefficient, iteratedDeriv_one]
  rw [hvalue] at hderiv
  exact hderiv

/-- If the two factor Green representations requested by the old product
ledger are supplied, the existing diagonal-removal theorem closes the
product-dressed center Gram at `h₀`.  The hypotheses are representation
statements for the two factors, not a renamed scalar Gram equality. -/
theorem inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_h0_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0) :
    inner ℂ
        (canonicalCompletedNativeNormalizedGreenState xiState 0)
        (canonicalCompletedNativeNormalizedGreenState xiState 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  exact completedNativeC3ProductLedger_inner_self_zero_eq_responseDerivative
    xiState hxi hnative hxiContinuous
      completedNativeGreenNormalizedResponse_hasDerivAt_h0

/-- The same center Gram with the scalar target opened before the
first-derivative cancellation.  The canonical Leibniz transport contributes
the mixed term with coefficient `2`; it is a scalar product-jet term, not a
cross inner product between prematurely orthogonal ordinary and log jets. -/
theorem
    inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_productJet_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0) :
    inner ℂ
        (canonicalCompletedNativeNormalizedGreenState xiState 0)
        (canonicalCompletedNativeNormalizedGreenState xiState 0) =
      -(iteratedDeriv 2 nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
          2 * deriv nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 * iteratedDeriv 2 nativeHeightScalar 0) /
        (2 * nativeXiCompletionFactor 0 * nativeHeightScalar 0) := by
  rw [inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_h0_of_factors
    xiState hxi hnative hxiContinuous,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet]

/-- After the exact first-jet cancellation, the mixed Leibniz contribution
is equivalently absorbed into the two logarithmic square corrections. -/
theorem
    inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_factorCurvatures_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0) :
    inner ℂ
        (canonicalCompletedNativeNormalizedGreenState xiState 0)
        (canonicalCompletedNativeNormalizedGreenState xiState 0) =
      -(1 / 2 : ℂ) *
        ((iteratedDeriv 2 nativeXiCompletionFactor 0 *
                nativeXiCompletionFactor 0 -
              deriv nativeXiCompletionFactor 0 ^ 2) /
            nativeXiCompletionFactor 0 ^ 2 +
          (iteratedDeriv 2 nativeHeightScalar 0 * nativeHeightScalar 0 -
              deriv nativeHeightScalar 0 ^ 2) /
            nativeHeightScalar 0 ^ 2) := by
  rw [inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_h0_of_factors
    xiState hxi hnative hxiContinuous,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_factorLogCurvatures]

/-- Combining the explicit factor-coordinate calculation with diagonal
closure gives the exact center-only target in its factorwise form. -/
theorem canonicalCompletedNativeFactorGrams_zero_eq_h0_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0) :
    inner ℂ
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0)
          (normalizedCompletedGreenState
            nativeXiCompletionFactor xiState 0) +
        inner ℂ
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0)
          (normalizedCompletedGreenState
            nativeHeightScalar canonicalCompletedOperatorC3HilbertState 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [← inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_factorGrams]
  exact inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_h0_of_factors
    xiState hxi hnative hxiContinuous

end

end CarrySelfAdjointOperator
