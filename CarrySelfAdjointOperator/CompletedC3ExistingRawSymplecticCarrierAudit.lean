import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import CarrySelfAdjointOperator.CompletedC3GreenFrameStructuralReadoutBridge
import CarrySelfAdjointOperator.CompletedC3SymplecticCollisionVariationAudit
import Mathlib.Tactic

/-!
# Audit of the existing raw C3 symplectic carrier

The raw operator carrier requested by the central-collision audit was already
present inside `CompletedC3FullWronskianOperatorCarrier`.  Its state is the
first block of the full state: the xi-weighted image of the permanent
one-point all-cutoff state under the bounded completed-trace projection.  Its
operator is the fixed boundary symplectic rotation.

This file exposes that raw block, connects it to the pair-dependent no-leak
ledger and to the bounded Green-frame structural synthesis, and then records
the fixed-center first derivatives of the raw block and of the existing full
raw-plus-archimedean direct sum.

No new channel, fitted weight, positivity statement, theta representation,
zero hypothesis, confinement statement, or higher moment is introduced.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The raw block already contained in the full operator state -/

/-- The existing xi-weighted raw boundary state at cutoff `M`.  This is
literally the first block of the previously constructed full Wronskian
operator state. -/
def canonicalCompletedC3RawWronskianOperatorState
    (M : ℕ) (z : ℂ) : CompletedScalarBoundaryTraceCarrier :=
  (canonicalCompletedC3FullWronskianOperatorState M z).fst

/-- The fixed bounded raw operator is the already existing scalar boundary
symplectic rotation.  It is independent of `M`, `z`, and `w`. -/
abbrev canonicalCompletedC3RawWronskianOperator :=
  completedScalarBoundarySymplecticRotation

@[simp] theorem canonicalCompletedC3RawWronskianOperatorState_eq
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3RawWronskianOperatorState M z =
      nativeXiCompletionFactor z •
        canonicalCompletedC3OnePointCompletedTraceProjection
          (canonicalCompletedC3AllCutoffOnePointState M z) :=
  rfl

/-- The value coordinate retains the seeded finite head and the independently
stored value tail.  In particular the constant seed is not reconstructed by
an affine readout from a seedless Hilbert prefix. -/
theorem canonicalCompletedC3RawWronskianOperatorState_value_eq_seed_head_tail
    (M : ℕ) (z : ℂ) :
    (canonicalCompletedC3RawWronskianOperatorState M z).snd =
      nativeXiCompletionFactor z *
        (1 + finiteCanonicalBracketTrace M (operatorHeightParameter z) +
          realCpBracketCutoffTail 3 M (operatorHeightParameter z)) := by
  unfold canonicalCompletedC3RawWronskianOperatorState
    canonicalCompletedC3FullWronskianOperatorState
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply]
  change nativeXiCompletionFactor z *
      (finiteBracketedDirichletChart 3 M (operatorHeightParameter z) +
        realCpBracketCutoffTail 3 M (operatorHeightParameter z)) = _
  rw [finiteBracketedDirichletChart_three_eq_one_add_trace]

/-- Exact raw operator factorization at fixed cutoff.  The response depends
only on `w`, the source only on `z`, and the bounded operator is fixed. -/
theorem canonicalCompletedC3RawWronskianOperator_inner_eq
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3RawWronskianOperatorState M w)
        (canonicalCompletedC3RawWronskianOperator
          (canonicalCompletedC3RawWronskianOperatorState M z)) =
      mixedHermitianWeight nativeXiCompletionFactor z w *
        canonicalCompletedC3RawHeightMixedWronskian z w := by
  rw [canonicalCompletedC3RawWronskianOperatorState_eq,
    canonicalCompletedC3RawWronskianOperatorState_eq,
    canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hz,
    canonicalCompletedC3OnePointCompletedTraceProjection_state_eq M hw]
  exact
    (canonicalCompletedC3XiWeightedRawWronskian_eq_symplecticInner z w).symm

/-! ## Compatibility with every retained no-leak channel -/

/-- The raw operator form is exactly the xi-weighted no-leak raw ledger,
with the structural coordinate supplied by bounded Green-frame synthesis.
Thus the operator factorization does not assume away radial, provenance,
off-diagonal, readout-residual, or head--tail channels. -/
theorem canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameLedger
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3RawWronskianOperatorState M w)
        (canonicalCompletedC3RawWronskianOperator
          (canonicalCompletedC3RawWronskianOperatorState M z)) =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).xiWeight *
        ((canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout +
          canonicalC3MixedStructuralScalarReadout
            (canonicalCompletedC3AllCutoffOrientedStructuralState M z w) +
          (canonicalCompletedC3AllCutoffKernelLedgerState M z w).tail) := by
  rw [canonicalCompletedC3AllCutoffOrientedStructuralState_eq_ledger]
  change _ =
    (canonicalCompletedC3AllCutoffKernelLedgerState M z w).xiWeight *
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).rawReadout
  rw [canonicalCompletedC3RawWronskianOperator_inner_eq M hz hw,
    canonicalCompletedC3AllCutoffKernelLedgerState_xiWeight,
    canonicalCompletedC3AllCutoffKernelLedgerState_rawReadout_eq_wronskian
      M hz hw]

/-- Coordinatewise spelling of the same theorem.  The three Green-frame
structural coordinates remain visible until the last scalar addition. -/
theorem canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameChannels
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3RawWronskianOperatorState M w)
        (canonicalCompletedC3RawWronskianOperator
          (canonicalCompletedC3RawWronskianOperatorState M z)) =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).xiWeight *
        ((canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout +
          (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).fst +
          (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).snd.fst +
          (canonicalCompletedC3AllCutoffOrientedStructuralState M z w).snd.snd +
          (canonicalCompletedC3AllCutoffKernelLedgerState M z w).tail) := by
  rw [canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameLedger
      M hz hw]
  unfold canonicalC3MixedStructuralScalarReadout
  ring

/-! ## Fixed-center raw variation -/

/-- Fixed-center real collision branch of the raw operator form with the
exact central-ledger normalization. -/
def canonicalCompletedC3FixedCenterRawOperatorRealBranch
    (M : ℕ) (t : ℝ) : ℂ :=
  inner ℂ
      (canonicalCompletedC3RawWronskianOperatorState M 0)
      (canonicalCompletedC3RawWronskianOperator
        (canonicalCompletedC3RawWronskianOperatorState M (t : ℂ))) /
    canonicalCompletedC3FixedCenterLedgerNormalization (t : ℂ)

/-- The raw operator branch is pointwise the previously isolated scalar raw
branch. -/
theorem canonicalCompletedC3FixedCenterRawOperatorRealBranch_eq_raw
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FixedCenterRawOperatorRealBranch M t =
      canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) := by
  unfold canonicalCompletedC3FixedCenterRawOperatorRealBranch
    canonicalCompletedC3FixedCenterRawWronskianBranch
  have ht : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  rw [canonicalCompletedC3RawWronskianOperator_inner_eq M ht
    zero_mem_completedNativeHeightDomain]

/-- Its first normalized real collision variation is exactly the first raw
C3 response coefficient. -/
theorem deriv_canonicalCompletedC3FixedCenterRawOperatorRealBranch_zero
    (M : ℕ) :
    deriv (canonicalCompletedC3FixedCenterRawOperatorRealBranch M) 0 =
      canonicalCompletedC3RawHeightResponseTaylorCoefficient 1 := by
  rw [show canonicalCompletedC3FixedCenterRawOperatorRealBranch M =
      fun t : ℝ => canonicalCompletedC3FixedCenterRawWronskianBranch (t : ℂ) by
    funext t
    exact canonicalCompletedC3FixedCenterRawOperatorRealBranch_eq_raw M t]
  rw [deriv_comp_ofReal_eq
    canonicalCompletedC3FixedCenterRawWronskianBranch_differentiableAt_zero]
  exact deriv_canonicalCompletedC3FixedCenterRawWronskianBranch_zero

/-! ## The existing raw-plus-archimedean direct sum -/

/-- The old full operator readout is literally the sum of the raw block above
and the independently retained archimedean/chart operator block. -/
theorem canonicalCompletedC3FullWronskianOperator_inner_eq_raw_add_archimedean
    (M : ℕ) (z w : ℂ) :
    inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState M z)) =
      inner ℂ
          (canonicalCompletedC3RawWronskianOperatorState M w)
          (canonicalCompletedC3RawWronskianOperator
            (canonicalCompletedC3RawWronskianOperatorState M z)) +
        inner ℂ
          (canonicalCompletedC3ArchimedeanChartOperatorState w)
          (canonicalCompletedC3ArchimedeanChartOperator
            (canonicalCompletedC3ArchimedeanChartOperatorState z)) := by
  rw [canonicalCompletedC3FullWronskianOperator_apply,
    WithLp.prod_inner_apply]
  rfl

/-- Fully channel-visible operatorial sewing.  The old full direct-sum
operator reads the Green-frame recovered raw ledger plus the existing
archimedean/chart block. -/
theorem canonicalCompletedC3FullWronskianOperator_inner_eq_greenFrameFinalLedger
    (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M w)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState M z)) =
      (canonicalCompletedC3AllCutoffKernelLedgerState M z w).xiWeight *
          ((canonicalCompletedC3AllCutoffKernelLedgerState M z w).radialComplexReadout +
            canonicalC3MixedStructuralScalarReadout
              (canonicalCompletedC3AllCutoffOrientedStructuralState M z w) +
            (canonicalCompletedC3AllCutoffKernelLedgerState M z w).tail) +
        (canonicalCompletedC3AllCutoffKernelLedgerState M z w).archimedeanChart := by
  rw [canonicalCompletedC3FullWronskianOperator_inner_eq_raw_add_archimedean,
    canonicalCompletedC3RawWronskianOperator_inner_eq_greenFrameLedger M hz hw,
    ← canonicalCompletedC3ArchimedeanChartMixedChannel_eq_operatorInner,
    canonicalCompletedC3AllCutoffKernelLedgerState_archimedeanChart]

/-- The complete operator form cancels at the central collision before any
normalization or division. -/
theorem canonicalCompletedC3FullWronskianOperator_center_collision
    (M : ℕ) :
    inner ℂ
        (canonicalCompletedC3FullWronskianOperatorState M 0)
        (canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperatorState M 0)) = 0 := by
  rw [← completedFNegFPrimeWronskian_eq_fullOperatorInner M
    zero_mem_completedNativeHeightDomain
    zero_mem_completedNativeHeightDomain,
    completedFNegFPrimeWronskian_zero_zero]
  ring

/-- Real restriction of the already existing full operator normalized
response.  This is the operatorial `B_total` branch. -/
def canonicalCompletedC3FullOperatorFixedCenterRealBranch
    (M : ℕ) (t : ℝ) : ℂ :=
  canonicalCompletedC3FullOperatorNormalizedResponse M (t : ℂ)

/-- The existing full operator response is pointwise the same normalized
total symplectic branch isolated in the preceding collision audit. -/
theorem canonicalCompletedC3FullOperatorFixedCenterRealBranch_eq_total
    (M : ℕ) (t : ℝ) :
    canonicalCompletedC3FullOperatorFixedCenterRealBranch M t =
      canonicalCompletedC3FixedCenterTotalSymplecticRealBranch t := by
  have ht : operatorHeightParameter (t : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hcross := completedFNegFPrimeWronskian_crossedChartIdentity
    (z := (t : ℂ)) (w := (0 : ℂ)) ht
      zero_mem_completedNativeHeightDomain
  have hchart :
      mixedHermitianWeight canonicalC3ChartFactorHeight (t : ℂ) 0 ≠ 0 :=
    canonicalC3ChartMixedHermitianWeight_ne_zero ht
      zero_mem_completedNativeHeightDomain
  unfold canonicalCompletedC3FullOperatorFixedCenterRealBranch
    canonicalCompletedC3FullOperatorNormalizedResponse
  rw [canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed
    M zero_mem_completedNativeHeightDomain ht]
  unfold canonicalCompletedC3FixedCenterTotalSymplecticRealBranch
  rw [canonicalCompletedC3FixedCenterGlobalOperatorRealBranch_eq_archimedean]
  unfold canonicalCompletedC3FixedCenterRawWronskianBranch
    canonicalCompletedC3FixedCenterArchimedeanBranch
    canonicalCompletedC3FixedCenterLedgerNormalization
  rw [← add_div, ← hcross]
  have hcancel := mul_div_mul_left
    (completedGreenWronskian
      completedNativeOperatorCharacteristic
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
      (t : ℂ) 0)
    ((2 : ℂ) * (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) *
      completedNativeOperatorCharacteristic (t : ℂ)) hchart
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel.symm

@[simp] theorem canonicalCompletedC3FullOperatorFixedCenterRealBranch_zero
    (M : ℕ) :
    canonicalCompletedC3FullOperatorFixedCenterRealBranch M 0 = 0 := by
  change canonicalCompletedC3FullOperatorNormalizedResponse M (0 : ℂ) = 0
  rw [(canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed
    M).self_of_nhds]
  exact completedNativeGreenNormalizedResponse_zero

private theorem canonicalCompletedC3FullOperatorNormalizedResponse_differentiableAt_zero
    (M : ℕ) :
    DifferentiableAt ℂ (canonicalCompletedC3FullOperatorNormalizedResponse M) 0 := by
  apply
    (canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed
      M).differentiableAt_iff.mpr
  exact completedNativeGreenNormalizedResponse_analyticAt.differentiableAt

/-- The first real variation of the old full raw-plus-archimedean operator
readout is exactly `h₀`. -/
theorem deriv_canonicalCompletedC3FullOperatorFixedCenterRealBranch_zero
    (M : ℕ) :
    deriv (canonicalCompletedC3FullOperatorFixedCenterRealBranch M) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  change deriv
      (fun t : ℝ =>
        canonicalCompletedC3FullOperatorNormalizedResponse M (t : ℂ)) 0 = _
  rw [deriv_comp_ofReal_eq
    (canonicalCompletedC3FullOperatorNormalizedResponse_differentiableAt_zero M)]
  change deriv (canonicalCompletedC3FullOperatorNormalizedResponse M) (0 : ℂ) = _
  rw [(canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed
    M).deriv_eq]
  have hmoment :=
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa [completedNativeGreenResponseTaylorCoefficient,
    iteratedDeriv_one] using hmoment

end

end CarrySelfAdjointOperator
