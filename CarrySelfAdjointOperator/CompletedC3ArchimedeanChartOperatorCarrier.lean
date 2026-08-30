import CarrySelfAdjointOperator.CompletedC3FNegFPrimeMixedKernel
import Mathlib.Tactic

/-!
# Operator carrier for the archimedean/chart channel

The completion/chart correction is not itself a positive Gram kernel.  This
module nevertheless places it in an honest Hilbert carrier without changing
its sign: a boundary trace pair is read through the canonical symplectic
rotation `J (Psi, F) = (-F, Psi)`.  The full crossed channel is the direct sum
of one `J` block and one `-J` block with exactly the weights already present in
the completed ledger.

Thus the remaining positivity problem becomes positivity of an explicit
operator-valued form on the geometric jet range, rather than an unsupported
factorwise Green representation.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

noncomputable section

/-- Hilbert carrier of one scalar boundary trace pair `(Psi, F)`. -/
abbrev CompletedScalarBoundaryTraceCarrier := WithLp 2 (ℂ × ℂ)

/-- Scalar boundary trace packaged in its canonical Hilbert carrier. -/
def completedScalarBoundaryTraceState
    (F Psi : ℂ → ℂ) (z : ℂ) : CompletedScalarBoundaryTraceCarrier :=
  WithLp.toLp 2 (Psi z, F z)

/-- Canonical symplectic rotation on scalar boundary traces. -/
def completedScalarBoundarySymplecticRotation :
    CompletedScalarBoundaryTraceCarrier →L[ℂ]
      CompletedScalarBoundaryTraceCarrier :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).symm.toLinearMap.comp
      ((-(WithLp.sndₗ 2 ℂ ℂ ℂ)).prod
        (WithLp.fstₗ 2 ℂ ℂ ℂ)))

@[simp] theorem completedScalarBoundarySymplecticRotation_apply
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundarySymplecticRotation state =
      WithLp.toLp 2 (-state.snd, state.fst) :=
  rfl

/-- Applying the boundary rotation twice gives minus the original trace. -/
@[simp] theorem completedScalarBoundarySymplecticRotation_sq
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundarySymplecticRotation
        (completedScalarBoundarySymplecticRotation state) = -state := by
  apply (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).injective
  ext <;> rfl

/-- The division-free Wronskian is exactly the operator readout of the two
boundary trace states. -/
theorem completedGreenWronskian_eq_boundarySymplecticInner
    (F Psi : ℂ → ℂ) (z w : ℂ) :
    completedGreenWronskian F Psi z w =
      inner ℂ
        (completedScalarBoundaryTraceState F Psi w)
        (completedScalarBoundarySymplecticRotation
          (completedScalarBoundaryTraceState F Psi z)) := by
  simp [completedGreenWronskian, completedScalarBoundaryTraceState,
    completedScalarBoundarySymplecticRotation, WithLp.prod_inner_apply]
  ring

/-- A boundary trace paired with its own symplectic rotation has zero real
part. Thus this exact Wronskian carrier is operator-valued, not a positive
Gram realization obtained by forgetting the rotation. -/
theorem completedScalarBoundarySymplecticRotation_inner_self_re_eq_zero
    (state : CompletedScalarBoundaryTraceCarrier) :
    (inner ℂ state
      (completedScalarBoundarySymplecticRotation state)).re = 0 := by
  rw [completedScalarBoundarySymplecticRotation_apply,
    WithLp.prod_inner_apply]
  change (inner ℂ state.fst (-state.snd) +
    inner ℂ state.snd state.fst).re = 0
  rw [inner_neg_right, Complex.add_re, Complex.neg_re]
  have hsymm :
      (inner ℂ state.fst state.snd).re =
        (inner ℂ state.snd state.fst).re := by
    exact inner_re_symm (𝕜 := ℂ) state.fst state.snd
  linarith

/-- Two-block Hilbert carrier of the crossed completion/chart correction. -/
abbrev CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  WithLp 2
    (CompletedScalarBoundaryTraceCarrier ×
      CompletedScalarBoundaryTraceCarrier)

/-- The exact two weighted trace states entering the crossed
archimedean/chart channel. -/
def canonicalCompletedC3ArchimedeanChartOperatorState
    (z : ℂ) : CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  let nativeTrace := completedScalarBoundaryTraceState
    nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z
  let chartTrace := completedScalarBoundaryTraceState
    canonicalC3ChartFactorHeight canonicalC3ChartFactorHeightCompanion z
  let value := canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z
  WithLp.toLp 2
    ((value * canonicalC3ChartFactorHeight z) • nativeTrace,
      (value * nativeXiCompletionFactor z) • chartTrace)

/-- Block symplectic operator of the crossed carrier: `J` on the completion block
and `-J` on the chart block. -/
def canonicalCompletedC3ArchimedeanChartOperator :
    CanonicalCompletedC3ArchimedeanChartOperatorCarrier →L[ℂ]
      CanonicalCompletedC3ArchimedeanChartOperatorCarrier :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ
        (CompletedScalarBoundaryTraceCarrier ×
          CompletedScalarBoundaryTraceCarrier)).symm.toLinearMap.comp
      ((completedScalarBoundarySymplecticRotation.toLinearMap.comp
          (WithLp.fstₗ 2 ℂ
            CompletedScalarBoundaryTraceCarrier
            CompletedScalarBoundaryTraceCarrier)).prod
        ((-completedScalarBoundarySymplecticRotation.toLinearMap).comp
          (WithLp.sndₗ 2 ℂ
            CompletedScalarBoundaryTraceCarrier
            CompletedScalarBoundaryTraceCarrier))))

@[simp] theorem canonicalCompletedC3ArchimedeanChartOperator_apply
    (state : CanonicalCompletedC3ArchimedeanChartOperatorCarrier) :
    canonicalCompletedC3ArchimedeanChartOperator state = WithLp.toLp 2
      (completedScalarBoundarySymplecticRotation state.fst,
        -completedScalarBoundarySymplecticRotation state.snd) :=
  rfl

/-- The crossed block operator is a complex structure on its Hilbert carrier. -/
@[simp] theorem canonicalCompletedC3ArchimedeanChartOperator_sq
    (state : CanonicalCompletedC3ArchimedeanChartOperatorCarrier) :
    canonicalCompletedC3ArchimedeanChartOperator
        (canonicalCompletedC3ArchimedeanChartOperator state) = -state := by
  rw [canonicalCompletedC3ArchimedeanChartOperator_apply,
    canonicalCompletedC3ArchimedeanChartOperator_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact completedScalarBoundarySymplecticRotation_sq state.fst
  · simp
    apply WithLp.ofLp_injective 2
    ext <;> rfl

@[simp] theorem canonicalCompletedC3ArchimedeanChartOperatorState_fst
    (z : ℂ) :
    (canonicalCompletedC3ArchimedeanChartOperatorState z).fst =
      (canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z *
          canonicalC3ChartFactorHeight z) •
        completedScalarBoundaryTraceState
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z :=
  rfl

@[simp] theorem canonicalCompletedC3ArchimedeanChartOperatorState_snd
    (z : ℂ) :
    (canonicalCompletedC3ArchimedeanChartOperatorState z).snd =
      (canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z *
          nativeXiCompletionFactor z) •
        completedScalarBoundaryTraceState
          canonicalC3ChartFactorHeight
          canonicalC3ChartFactorHeightCompanion z :=
  rfl

/-- Expands only the outer direct-sum readout.  The two boundary-pair inner
products remain intact so that each can be recognized as a Wronskian. -/
theorem canonicalCompletedC3ArchimedeanChartOperator_inner
    (x y : CanonicalCompletedC3ArchimedeanChartOperatorCarrier) :
    inner ℂ x (canonicalCompletedC3ArchimedeanChartOperator y) =
      inner ℂ x.fst
          (completedScalarBoundarySymplecticRotation y.fst) -
        inner ℂ x.snd
          (completedScalarBoundarySymplecticRotation y.snd) := by
  rw [canonicalCompletedC3ArchimedeanChartOperator_apply,
    WithLp.prod_inner_apply]
  change
    inner ℂ x.fst (completedScalarBoundarySymplecticRotation y.fst) +
        inner ℂ x.snd (-completedScalarBoundarySymplecticRotation y.snd) = _
  rw [inner_neg_right]
  rfl

/-- The crossed archimedean/chart operator remains symplectic on the
diagonal: its quadratic readout has zero real part. -/
theorem canonicalCompletedC3ArchimedeanChartOperator_inner_self_re_eq_zero
    (state : CanonicalCompletedC3ArchimedeanChartOperatorCarrier) :
    (inner ℂ state
      (canonicalCompletedC3ArchimedeanChartOperator state)).re = 0 := by
  rw [canonicalCompletedC3ArchimedeanChartOperator_inner,
    Complex.sub_re,
    completedScalarBoundarySymplecticRotation_inner_self_re_eq_zero,
    completedScalarBoundarySymplecticRotation_inner_self_re_eq_zero]
  ring

/-- Exact Hilbert-operator realization of the archimedean/chart mixed
channel.  No positivity, zero condition, or spectral premise is used. -/
theorem canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner
    (z w : ℂ) :
    canonicalCompletedC3ArchimedeanChartMixedChannel z w =
      inner ℂ
        (canonicalCompletedC3ArchimedeanChartOperatorState w)
        (canonicalCompletedC3ArchimedeanChartOperator
          (canonicalCompletedC3ArchimedeanChartOperatorState z)) := by
  unfold canonicalCompletedC3ArchimedeanChartMixedChannel
  rw [canonicalCompletedC3ArchimedeanChartOperator_inner]
  simp only [canonicalCompletedC3ArchimedeanChartOperatorState_fst,
    canonicalCompletedC3ArchimedeanChartOperatorState_snd,
    map_smul, inner_smul_left, inner_smul_right, map_mul]
  rw [← completedGreenWronskian_eq_boundarySymplecticInner,
    ← completedGreenWronskian_eq_boundarySymplecticInner]
  unfold mixedHermitianWeight
  ring

end

end CarrySelfAdjointOperator
