import CarrySelfAdjointOperator.CompletedC3GlobalGreenOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3CentralLedgerChannelDerivative
import Mathlib.Tactic

/-!
# Symplectic audit of the completed C3 central collision

The crossed chart identity cancels at the central collision before any
division by the Hermitian separation.  This file first records that
cancellation as an equality of the two already constructed symplectic
operator forms: the xi-weighted raw boundary trace and the crossed
archimedean/chart trace.

It then tests the larger `CanonicalCompletedC3GlobalGreenOperatorCarrier`.
On the fixed-center real collision line its radial coefficient is identically
zero.  Consequently that carrier reads only the archimedean/chart form; the
raw contribution is carried by the structural channels which are absent from
the candidate global operator kernel.  After the canonical ledger
normalization, the first variation of the existing global carrier is the
chart-replacement coefficient, while the sum with the missing raw
symplectic branch is exactly `h₀`.

No positivity, Green factorization, theta representation, zero hypothesis,
confinement statement, or all-order promotion is used.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Division-free cancellation at the central collision -/

/-- Centered evenness kills the Wronskian of the completed pair `(F,-F')`
at `(0,0)`.  The state itself is not asserted to vanish. -/
theorem completedFNegFPrimeWronskian_zero_zero :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        0 0 = 0 := by
  have hderiv : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  simp [completedGreenWronskian, hderiv]

/-- Exact central collision cancellation in the crossed-chart identity,
before division by `z - conj w` and before any positivity interpretation. -/
theorem canonicalCompletedC3RawArchimedean_center_collision_cancel :
    mixedHermitianWeight nativeXiCompletionFactor 0 0 *
          canonicalCompletedC3RawHeightMixedWronskian 0 0 +
        canonicalCompletedC3ArchimedeanChartMixedChannel 0 0 = 0 := by
  have hcross := completedFNegFPrimeWronskian_crossedChartIdentity
    (z := (0 : ℂ)) (w := (0 : ℂ))
    zero_mem_completedNativeHeightDomain
    zero_mem_completedNativeHeightDomain
  rw [completedFNegFPrimeWronskian_zero_zero] at hcross
  simpa using hcross.symm

/-- The xi-weighted raw C3 Wronskian is already an exact symplectic operator
form on the existing scalar boundary-trace carrier. -/
theorem canonicalCompletedC3XiWeightedRawWronskian_eq_symplecticInner
    (z w : ℂ) :
    mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalCompletedC3RawHeightMixedWronskian z w =
      inner ℂ
        (nativeXiCompletionFactor w •
          completedScalarBoundaryTraceState
            canonicalCompletedC3RawHeightValue
            canonicalCompletedC3RawHeightCompanion w)
        (completedScalarBoundarySymplecticRotation
          (nativeXiCompletionFactor z •
            completedScalarBoundaryTraceState
              canonicalCompletedC3RawHeightValue
              canonicalCompletedC3RawHeightCompanion z)) := by
  unfold canonicalCompletedC3RawHeightMixedWronskian
  rw [completedGreenWronskian_eq_boundarySymplecticInner]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  unfold mixedHermitianWeight
  ring

/-- Operatorial form of the complete central cancellation.  Both summands
are symplectic forms on carriers already present in the repository; neither
is replaced by a positive Gram. -/
theorem canonicalCompletedC3CentralCollision_symplecticForms_cancel :
    inner ℂ
          (nativeXiCompletionFactor 0 •
            completedScalarBoundaryTraceState
              canonicalCompletedC3RawHeightValue
              canonicalCompletedC3RawHeightCompanion 0)
          (completedScalarBoundarySymplecticRotation
            (nativeXiCompletionFactor 0 •
              completedScalarBoundaryTraceState
                canonicalCompletedC3RawHeightValue
                canonicalCompletedC3RawHeightCompanion 0)) +
        inner ℂ
          (canonicalCompletedC3ArchimedeanChartOperatorState 0)
          (canonicalCompletedC3ArchimedeanChartOperator
            (canonicalCompletedC3ArchimedeanChartOperatorState 0)) = 0 := by
  rw [← canonicalCompletedC3XiWeightedRawWronskian_eq_symplecticInner,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner]
  exact canonicalCompletedC3RawArchimedean_center_collision_cancel

/-! ## What the existing global carrier retains on the collision line -/

/-- The completed radial Green block vanishes on the fixed-center real
collision line because its canonical radial difference is zero there. -/
theorem canonicalCompletedC3MixedRadialGreenKernel_fixedCenter_ofReal_eq_zero
    (t : ℝ) :
    canonicalCompletedC3MixedRadialGreenKernel
        (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)
        (operatorHeightParameter_ofReal_re_pos 0)
        (reflected_operatorHeightParameter_ofReal_re_pos (t : ℂ)) = 0 := by
  unfold canonicalCompletedC3MixedRadialGreenKernel
  rw [canonicalC3MixedRadialCoefficient_operatorHeight_ofReal_zero]
  simp

/-- Hence the candidate global kernel retains only the archimedean/chart
channel along this real collision direction. -/
theorem canonicalCompletedC3FNegFPrimeMixedGreenKernel_fixedCenter_ofReal_eq_archimedean
    (t : ℝ) :
    canonicalCompletedC3FNegFPrimeMixedGreenKernel
        (t : ℂ) 0
        (operatorHeightParameter_ofReal_re_pos 0)
        (reflected_operatorHeightParameter_ofReal_re_pos (t : ℂ)) =
      canonicalCompletedC3ArchimedeanChartMixedChannel (t : ℂ) 0 := by
  unfold canonicalCompletedC3FNegFPrimeMixedGreenKernel
  rw [canonicalCompletedC3MixedRadialGreenKernel_fixedCenter_ofReal_eq_zero]
  ring

/-- The same fact inside the already constructed global Hilbert carrier:
its bounded symplectic operator reads exactly the archimedean/chart form and
not the full raw-plus-archimedean collision ledger. -/
theorem canonicalCompletedC3GlobalGreenOperator_fixedCenter_ofReal_eq_archimedean
    (t : ℝ) :
    inner ℂ
        (canonicalCompletedC3GlobalGreenResponseRealAxisState 0)
        (canonicalCompletedC3GlobalGreenOperator
          (canonicalCompletedC3GlobalGreenReflectedRealAxisState (t : ℂ))) =
      canonicalCompletedC3ArchimedeanChartMixedChannel (t : ℂ) 0 := by
  rw [← canonicalCompletedC3FNegFPrimeMixedGreenKernel_realAxis_eq_operatorInner
    (t : ℂ) 0]
  simpa using
    canonicalCompletedC3FNegFPrimeMixedGreenKernel_fixedCenter_ofReal_eq_archimedean
      t

/-- At the center, the global operator form is the negative of the omitted
xi-weighted raw symplectic form.  Thus it does not itself implement the
complete collision cancellation. -/
theorem canonicalCompletedC3GlobalGreenOperator_center_eq_neg_rawSymplectic :
    inner ℂ
        (canonicalCompletedC3GlobalGreenResponseRealAxisState 0)
        (canonicalCompletedC3GlobalGreenOperator
          (canonicalCompletedC3GlobalGreenReflectedRealAxisState 0)) =
      -(mixedHermitianWeight nativeXiCompletionFactor 0 0 *
          canonicalCompletedC3RawHeightMixedWronskian 0 0) := by
  calc
    _ = canonicalCompletedC3ArchimedeanChartMixedChannel 0 0 := by
      simpa using
        canonicalCompletedC3GlobalGreenOperator_fixedCenter_ofReal_eq_archimedean
          (0 : ℝ)
    _ = -(mixedHermitianWeight nativeXiCompletionFactor 0 0 *
          canonicalCompletedC3RawHeightMixedWronskian 0 0) := by
      linear_combination
        canonicalCompletedC3RawArchimedean_center_collision_cancel

/-- The global response state itself remains nonzero at the collision.  The
vanishing of the complete flux is therefore symplectic cancellation, not
annihilation of the state. -/
theorem canonicalCompletedC3GlobalGreenResponseRealAxisState_zero_ne_zero :
    canonicalCompletedC3GlobalGreenResponseRealAxisState 0 ≠ 0 := by
  have hradial :
      completedC3RadialAllOrderState
          (operatorHeightParameter 0)
          (operatorHeightParameter_ofReal_re_pos 0) ≠ 0 := by
    exact canonicalCompletedC3DirichletGradientState_ne_zero
      zero_mem_completedNativeHeightDomain
  have hradialOperator :
      canonicalCompletedC3RadialOperatorState
          (operatorHeightParameter 0)
          (operatorHeightParameter_ofReal_re_pos 0) ≠ 0 := by
    intro hzero
    have hsnd := congrArg
      (fun state : CanonicalCompletedC3RadialOperatorCarrier => state.snd)
      hzero
    change completedC3RadialAllOrderState
        (operatorHeightParameter 0)
        (operatorHeightParameter_ofReal_re_pos 0) = 0 at hsnd
    exact hradial hsnd
  intro hzero
  have hfst := congrArg
    (fun state : CanonicalCompletedC3GlobalGreenOperatorCarrier => state.fst)
    hzero
  change nativeXiCompletionFactor 0 •
      canonicalCompletedC3RadialOperatorState
        (operatorHeightParameter 0)
        (operatorHeightParameter_ofReal_re_pos 0) = 0 at hfst
  exact (smul_ne_zero
    (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain)
    hradialOperator) hfst

/-! ## First real collision variation -/

/-- The existing global operator form with the exact normalization of the
central completed ledger.  This names a scalar diagnostic only; no new
carrier or positive form is introduced. -/
def canonicalCompletedC3FixedCenterGlobalOperatorRealBranch (t : ℝ) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GlobalGreenResponseRealAxisState 0)
      (canonicalCompletedC3GlobalGreenOperator
        (canonicalCompletedC3GlobalGreenReflectedRealAxisState (t : ℂ))) /
    canonicalCompletedC3FixedCenterLedgerNormalization (t : ℂ)

/-- Pointwise, the normalized global operator branch is exactly the existing
archimedean ledger branch. -/
theorem canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean
    (t : ℝ) :
    canonicalCompletedC3FixedCenterGlobalOperatorRealBranch t =
      canonicalCompletedC3FixedCenterArchimedeanBranch (t : ℂ) := by
  unfold canonicalCompletedC3FixedCenterGlobalOperatorRealBranch
    canonicalCompletedC3FixedCenterArchimedeanBranch
  rw [canonicalCompletedC3GlobalGreenOperator_fixedCenter_ofReal_eq_archimedean]

private theorem
    canonicalCompletedC3FixedCenterArchimedeanBranch_differentiableAt_zero :
    DifferentiableAt ℂ canonicalCompletedC3FixedCenterArchimedeanBranch 0 := by
  apply
    canonicalCompletedC3FixedCenterArchimedeanBranch_eventuallyEq_replacement.differentiableAt_iff.mpr
  exact
    (nativeXiCompletionNormalizedResponse_analyticAt_zero.differentiableAt.sub
      canonicalC3ChartFactorNormalizedResponse_analyticAt_zero.differentiableAt).sub
        (differentiableAt_const
          (c := conj (canonicalCompletedC3ChartReplacementNormalizedResponse 0)))

/-- The natural first variation of the existing global symplectic carrier is
the chart-replacement coefficient.  No sign or Gram interpretation is
attached to this complex scalar. -/
theorem deriv_canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_zero :
    deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 =
      canonicalCompletedC3ChartReplacementResponseTaylorCoefficient 1 := by
  rw [show canonicalCompletedC3FixedCenterGlobalOperatorRealBranch =
      fun t : ℝ => canonicalCompletedC3FixedCenterArchimedeanBranch (t : ℂ) by
    funext t
    exact
      canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean t]
  rw [deriv_comp_ofReal_eq
    canonicalCompletedC3FixedCenterArchimedeanBranch_differentiableAt_zero]
  exact deriv_canonicalCompletedC3FixedCenterArchimedeanBranch_zero

/-- Adding back the raw symplectic branch gives the complete first variation
`h₀`.  This is the precise collision derivative supplied by the existing
ledger, before any attempted positive tangent metric. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_plus_globalVariation :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) =
      deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 +
        deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
  rw [deriv_canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_zero]
  simpa [deriv_canonicalCompletedC3FixedCenterArchimedeanBranch_zero] using
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_centralLedgerBlockDerivatives

/-- The complete normalized real-collision form: the raw boundary
symplectic branch plus the form read by the existing global operator
carrier. -/
def canonicalCompletedC3FixedCenterTotalSymplecticRealBranch (t : ℝ) : ℂ :=
  canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) +
    canonicalCompletedC3FixedCenterGlobalOperatorRealBranch t

/-- The complete normalized symplectic form still vanishes at collision,
although neither retained summand is required to vanish separately. -/
@[simp] theorem canonicalCompletedC3FixedCenterTotalSymplecticRealBranch_zero :
    canonicalCompletedC3FixedCenterTotalSymplecticRealBranch 0 = 0 := by
  unfold canonicalCompletedC3FixedCenterTotalSymplecticRealBranch
  rw [canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean]
  have hsplit :=
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_eq_raw_add_archimedean
      0 zero_mem_completedNativeHeightDomain
  have hzero :=
    canonicalCompletedC3FixedCenterChannelSeparatedLedgerNumerator_zero 0
  simpa only [Complex.ofReal_zero] using hsplit.symm.trans hzero

/-- The first real variation of the total normalized symplectic form is
exactly `h₀`.  This is a derivative of an operatorial form, not a declaration
that the form is a positive Gram. -/
theorem deriv_canonicalCompletedC3FixedCenterTotalSymplecticRealBranch_zero :
    deriv canonicalCompletedC3FixedCenterTotalSymplecticRealBranch 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [show canonicalCompletedC3FixedCenterTotalSymplecticRealBranch =
      fun t : ℝ =>
        canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) +
          canonicalCompletedC3FixedCenterArchimedeanBranch (t : ℂ) by
    funext t
    unfold canonicalCompletedC3FixedCenterTotalSymplecticRealBranch
    rw [canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean]]
  change deriv
      ((fun t : ℝ =>
          canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ)) +
        (fun t : ℝ =>
          canonicalCompletedC3FixedCenterArchimedeanBranch (t : ℂ))) 0 = _
  rw [deriv_add
    canonicalCompletedC3FixedCenterRawWronskianBranch_differentiableAt_zero.hasDerivAt.comp_ofReal.differentiableAt
    canonicalCompletedC3FixedCenterArchimedeanBranch_differentiableAt_zero.hasDerivAt.comp_ofReal.differentiableAt,
    deriv_comp_ofReal_eq
      canonicalCompletedC3FixedCenterRawWronskianBranch_differentiableAt_zero,
    deriv_comp_ofReal_eq
      canonicalCompletedC3FixedCenterArchimedeanBranch_differentiableAt_zero]
  exact
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_centralLedgerBlockDerivatives.symm

/-- The global carrier variation alone equals `h₀` precisely if the omitted
raw first variation vanishes.  This isolates the first equality that would
be needed to promote the current global carrier to the complete collision
carrier. -/
theorem deriv_globalOperatorRealBranch_eq_h0_iff_rawVariation_zero :
    deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ↔
      deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 = 0 := by
  have hsplit :=
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_raw_plus_globalVariation
  constructor <;> intro h
  · calc
      deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 =
          (deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 +
              deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0) -
            deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
              ring
      _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) -
            deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
              rw [← hsplit]
      _ = 0 := by rw [h]; ring
  · calc
      deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 =
          deriv canonicalCompletedC3FixedCenterRawWronskianBranch 0 +
            deriv canonicalCompletedC3FixedCenterGlobalOperatorRealBranch 0 := by
              rw [h]
              ring
      _ = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := hsplit.symm

end

end CarrySelfAdjointOperator
