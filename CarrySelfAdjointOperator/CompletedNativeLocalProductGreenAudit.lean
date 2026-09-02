import CarrySelfAdjointOperator.CompletedNativeCentralProductDressingAudit
import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection
import CarrySelfAdjointOperator.CanonicalC3GreenIntertwiner
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Local product-Green audit at the completed-native center

The diagonal closure theorem needs a Green identity only on the centered
height domain.  This file first localizes the exact product rule and the
product-dressed center theorem accordingly.

It then tests the proposed native factor state before considering a new xi
carrier.  The test exposes a zeroth-diagonal obstruction: a division-free
Green representation with multiplier `z - conj w` forces the native factor
Wronskian to vanish at the real center.  Native Schwarz reflection then
forces `deriv nativeHeightScalar 0 = 0`.  Thus the first missing statement is
already a concrete scalar identity for the native factor, before tails,
completion-factor construction, or Taylor/Gram extraction.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## Local multiplicative Green transport -/

/-- Domain-local form of the exact product Green-state rule.  The proof is
pointwise and needs no global extension of either factor representation. -/
theorem HasDivisionFreeGreenRepresentationOn.mul
    {H_A H_G : Type*}
    [NormedAddCommGroup H_A] [InnerProductSpace ℂ H_A]
    [NormedAddCommGroup H_G] [InnerProductSpace ℂ H_G]
    {domain : Set ℂ} {A PsiA G PsiG : ℂ → ℂ}
    {stateA : ℂ → H_A} {stateG : ℂ → H_G}
    (hA : HasDivisionFreeGreenRepresentationOn domain A PsiA stateA)
    (hG : HasDivisionFreeGreenRepresentationOn domain G PsiG stateG) :
    HasDivisionFreeGreenRepresentationOn domain
      (fun z ↦ A z * G z)
      (productBoundaryCompanion A PsiA G PsiG)
      (weightedProductGreenState A G stateA stateG) := by
  intro z hz w hw
  rw [completedGreenWronskian_mul, hA z hz w hw, hG z hz w hw,
    inner_weightedProductGreenState]
  ring

/-- Two factor identities only on `completedNativeHeightDomain` already
construct the local completed product ledger.  This is the minimal Green
input consumed by center diagonal closure. -/
theorem completedNativeC3ProductLedger_greenRepresentationOn_of_localFactors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion
      (completedNativeC3ProductLedgerState xiState) := by
  intro z hz w hw
  change operatorHeightParameter z ∈ genuineCriticalStrip at hz
  change operatorHeightParameter w ∈ genuineCriticalStrip at hw
  have hproduct := (hxi.mul hnative) z hz w hw
  change completedGreenWronskian
      (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
      completedNativeOperatorBoundaryCompanion z w = _
  calc
    completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        completedNativeOperatorBoundaryCompanion z w =
      completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        (productBoundaryCompanion
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
          nativeHeightScalar nativeHeightScalarBoundaryCompanion) z w := by
            unfold completedGreenWronskian
            rw [completedNativeOperatorBoundaryCompanion_eq_product hz,
              completedNativeOperatorBoundaryCompanion_eq_product hw]
    _ = _ := by
      simpa [completedNativeC3ProductLedgerState] using hproduct

/-- The product-dressed center theorem requires only the two local factor
identities, plus center continuity of the still-abstract xi state. -/
theorem
    inner_canonicalCompletedNativeNormalizedGreenState_zero_eq_h0_of_localFactors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState)
    (hxiContinuous : ContinuousAt xiState 0) :
    inner ℂ
        (canonicalCompletedNativeNormalizedGreenState xiState 0)
        (canonicalCompletedNativeNormalizedGreenState xiState 0) =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  apply completedNativeGreenState_inner_self_zero_eq_responseDerivative_of_continuous
    (completedNativeC3ProductLedger_greenRepresentationOn_of_localFactors
      xiState hxi hnative)
  · exact completedNativeC3ProductLedgerState_continuousAt_zero hxiContinuous
  · exact completedNativeGreenNormalizedResponse_hasDerivAt_h0

/-! ## Exact native trace and the finite C3 candidate -/

/-- On the centered strip the tail-completed normalized TFVD trace is exactly
the native factor trace `(G,-G')`, at both polarized arguments. -/
theorem completedGreenWronskian_nativeHeightScalar_eq_tailCompleted
    {z w : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hw : w ∈ completedNativeHeightDomain) :
    completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion z w =
      completedGreenWronskian
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
        canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z w := by
  unfold completedGreenWronskian
  rw [canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hw,
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hw]

/-- The Hilbert Gram of the proposed native state is the positive
same-coordinate sum of the two finite C3 port legs.  Existing C3 Green
factorizations instead use the skew Green form and a reflected parameter. -/
theorem inner_canonicalCompletedOperatorC3HilbertState_eq_finiteC3PositiveGram
    (z w : ℂ) :
    inner ℂ
        (canonicalCompletedOperatorC3HilbertState w)
        (canonicalCompletedOperatorC3HilbertState z) =
      inner ℂ
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter w)).1
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter z)).1 +
        inner ℂ
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter w)).2
          (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
            (operatorHeightParameter z)).2 := by
  rw [WithLp.prod_inner_apply]
  simp only [canonicalCompletedOperatorC3HilbertState,
    canonicalCompletedOperatorC3State]
  rw [canonicalEnrichedC3SourcePort_eq_greenBoundaryPair,
    canonicalEnrichedC3SourcePort_eq_greenBoundaryPair]

/-- Therefore the proposed native representation is equivalent to one fully
concrete equality: the tail-completed native scalar Wronskian must equal the
positive finite-C3 Gram with multiplier `z - conj w`.  No existing tail or
Green-form theorem proves this equality. -/
theorem nativeC3GreenRepresentationOn_iff_tailWronskian_eq_positiveFiniteGram :
    HasDivisionFreeGreenRepresentationOn
        completedNativeHeightDomain
        nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState ↔
      ∀ z ∈ completedNativeHeightDomain, ∀ w ∈ completedNativeHeightDomain,
        completedGreenWronskian
            canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
            canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z w =
          (z - (starRingEnd ℂ) w) *
            (inner ℂ
                (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                  3 (operatorHeightParameter w)).1
                (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                  3 (operatorHeightParameter z)).1 +
              inner ℂ
                (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                  3 (operatorHeightParameter w)).2
                (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair
                  3 (operatorHeightParameter z)).2) := by
  constructor
  · intro hgreen z hz w hw
    rw [← completedGreenWronskian_nativeHeightScalar_eq_tailCompleted hz hw,
      ← inner_canonicalCompletedOperatorC3HilbertState_eq_finiteC3PositiveGram]
    exact hgreen z hz w hw
  · intro hidentity z hz w hw
    rw [completedGreenWronskian_nativeHeightScalar_eq_tailCompleted hz hw,
      inner_canonicalCompletedOperatorC3HilbertState_eq_finiteC3PositiveGram]
    exact hidentity z hz w hw

/-! ## The first center obstruction -/

/-- Centered evenness annihilates only the *weighted sum* of the two factor
Wronskians.  The exact product rule does not annihilate either factor
Wronskian separately.  This is the cancellation which a factorwise positive
direct sum would have to refine. -/
theorem nativeXi_native_centerWronskians_weighted_cancel :
    nativeHeightScalar 0 * (starRingEnd ℂ) (nativeHeightScalar 0) *
          completedGreenWronskian
            nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 +
        nativeXiCompletionFactor 0 *
            (starRingEnd ℂ) (nativeXiCompletionFactor 0) *
          completedGreenWronskian
            nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  rw [← completedGreenWronskian_mul]
  have hstrip : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hcompanion := completedNativeOperatorBoundaryCompanion_eq_product hstrip
  have hderiv : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  change completedGreenWronskian
      (fun z ↦ nativeXiCompletionFactor z * nativeHeightScalar z)
      (productBoundaryCompanion
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
        nativeHeightScalar nativeHeightScalarBoundaryCompanion) 0 0 = 0
  unfold completedGreenWronskian
  rw [← hcompanion]
  change
    completedNativeOperatorBoundaryCompanion 0 *
          (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) -
        completedNativeOperatorCharacteristic 0 *
          (starRingEnd ℂ) (completedNativeOperatorBoundaryCompanion 0) = 0
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv, hderiv]
  simp

/-- Any proposed native representation already forces its scalar Wronskian
to vanish at the real center, before continuity or diagonal removal enters. -/
theorem nativeC3GreenRepresentationOn_implies_centerWronskian_zero
    (hnative : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  have h := hnative 0 zero_mem_completedNativeHeightDomain
    0 zero_mem_completedNativeHeightDomain
  simpa using h

/-- The native scalar value at the centered height is fixed by conjugation. -/
theorem nativeHeightScalar_zero_conj :
    (starRingEnd ℂ) (nativeHeightScalar 0) = nativeHeightScalar 0 := by
  unfold nativeHeightScalar
  rw [← nativeScalar_conj_from_nativeSeries]
  congr 1
  apply Complex.ext <;> norm_num [operatorHeightParameter]

/-- The native scalar derivative in centered-height coordinates is
anti-fixed by conjugation: the chain rule contributes the factor `I`. -/
theorem nativeHeightScalar_deriv_zero_conj :
    (starRingEnd ℂ) (deriv nativeHeightScalar 0) =
      -deriv nativeHeightScalar 0 := by
  let center : ℂ := (1 / 2 : ℂ)
  have hfun : nativeScalar =
      (starRingEnd ℂ) ∘ nativeScalar ∘ (starRingEnd ℂ) := by
    funext s
    have h := nativeScalar_conj_from_nativeSeries ((starRingEnd ℂ) s)
    simpa [Function.comp_def] using h
  have hnativeDerivReal :
      (starRingEnd ℂ) (deriv nativeScalar center) =
        deriv nativeScalar center := by
    have hderiv := congrArg deriv hfun
    have hcenter : (starRingEnd ℂ) center = center := by
      apply Complex.ext <;> norm_num [center]
    have hat := congrFun hderiv center
    rw [deriv_conj_conj] at hat
    simpa [Function.comp_def, hcenter] using hat.symm
  have hcenterDomain : center ∈ nativeScalarDomain :=
    ⟨by norm_num [center], by norm_num [center]⟩
  have hcenterEq : operatorHeightParameter 0 = center := by
    apply Complex.ext <;> norm_num [operatorHeightParameter, center]
  have hnativeAtParameter : HasDerivAt nativeScalar
      (deriv nativeScalar (operatorHeightParameter 0))
      (operatorHeightParameter 0) := by
    rw [hcenterEq]
    exact (nativeScalar_differentiableOn.differentiableAt
      (isOpen_nativeScalarDomain.mem_nhds hcenterDomain)).hasDerivAt
  have hchain :=
    (hnativeAtParameter.comp 0
      (hasDerivAt_operatorHeightParameter 0)).deriv
  have hformula :
      deriv nativeHeightScalar 0 = deriv nativeScalar center * Complex.I := by
    change deriv (fun z ↦ nativeScalar (operatorHeightParameter z)) 0 = _
    simpa only [Function.comp_def, hcenterEq] using hchain
  rw [hformula, map_mul, hnativeDerivReal]
  simp

/-- Hence the local positive Green representation for the proposed native C3
state would force the concrete, pre-Gram identity `G'(0)=0`.  This is the
first new equality on the route; it is not hidden in a named hypothesis. -/
theorem nativeC3GreenRepresentationOn_implies_deriv_nativeHeightScalar_zero
    (hnative : HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState) :
    deriv nativeHeightScalar 0 = 0 := by
  have hwronskian :=
    nativeC3GreenRepresentationOn_implies_centerWronskian_zero hnative
  have hvalue : nativeHeightScalar 0 ≠ 0 := nativeHeightScalar_zero_ne_zero
  have hproduct : nativeHeightScalar 0 * deriv nativeHeightScalar 0 = 0 := by
    calc
      nativeHeightScalar 0 * deriv nativeHeightScalar 0 =
          -(1 / 2 : ℂ) *
            completedGreenWronskian
              nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 := by
        unfold completedGreenWronskian nativeHeightScalarBoundaryCompanion
        rw [nativeHeightScalar_zero_conj,
          map_neg, nativeHeightScalar_deriv_zero_conj]
        ring
      _ = 0 := by rw [hwronskian]; ring
  exact (mul_eq_zero.mp hproduct).resolve_left hvalue

/-- An explicit proof of nonvanishing of the native centered derivative would
therefore refute the proposed local native Green representation immediately.
This statement exposes that exact remaining scalar fact instead of packaging
the failed representation in a new existence hypothesis. -/
theorem not_nativeC3GreenRepresentationOn_of_deriv_ne_zero
    (hderiv : deriv nativeHeightScalar 0 ≠ 0) :
    ¬ HasDivisionFreeGreenRepresentationOn
      completedNativeHeightDomain
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3HilbertState := by
  intro hnative
  exact hderiv
    (nativeC3GreenRepresentationOn_implies_deriv_nativeHeightScalar_zero
      hnative)

end

end CarrySelfAdjointOperator
