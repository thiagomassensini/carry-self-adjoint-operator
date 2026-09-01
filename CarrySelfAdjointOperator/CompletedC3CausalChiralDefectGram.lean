import CarrySelfAdjointOperator.CompletedC3CausalChiralSourceCoherence
import Mathlib.Tactic

/-!
# Causal chiral defect Gram gate

The positive Wronskian readout and the coisometric camera/chiral readout are
already defined on the same enriched completed C3 source.  This module states
the route-B contraction only on the real-linear span of the actual causal
source family and separates its two logically distinct parts:

1. kernel compatibility, which makes a response-from-positive-readout map
   well defined on the causal range;
2. the norm inequality, which says that this map is contractive.

The second condition is exactly nonpositivity of the existing indefinite
boundary form.  Its specialization to a canonical source contradicts the
strictly positive boundary defect already proved at an upper-half-plane
native closure.

No contraction, positivity, zero, spectral, or confinement statement is
assumed or proved here.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The two source-level gates -/

/-- Necessary well-definedness condition for a causal transformation from
the positive Wronskian readout to the coisometric camera/chiral readout. -/
def CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt
    (z : ℂ) : Prop :=
  ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
    state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
      canonicalCompletedC3EnrichedPositiveChiralReadout z state = 0 →
        canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state = 0

/-- Route-B defect-Gram condition on the actual causal source span.  The
orientation says that the coisometric camera/chiral response is contractive
relative to the positive Wronskian response. -/
def CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt
    (z : ℂ) : Prop :=
  ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
    state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ ^ 2 ≤
        ‖canonicalCompletedC3EnrichedPositiveChiralReadout z state‖ ^ 2

/-- Any causal contraction first satisfies the necessary kernel
compatibility.  This implication uses no finite-dimensionality or selected
inverse. -/
theorem canonicalCompletedC3CausalChiralReadoutKernelCompatibleAt_of_defectGram
    {z : ℂ}
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    CanonicalCompletedC3CausalChiralReadoutKernelCompatibleAt z := by
  intro state hstate hpositive
  have hnorm := hdefect state hstate
  simp only [hpositive, norm_zero, pow_two, zero_mul] at hnorm
  have hzero :
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ = 0 := by
    nlinarith [norm_nonneg
      (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state)]
  exact norm_eq_zero.mp hzero

/-! ## Exact boundary-form spelling -/

/-- On a readout of one enriched source, the indefinite boundary form is the
coisometric norm square minus the positive Wronskian norm square. -/
theorem canonicalCompletedC3CausalChiralBoundaryForm_readout_self
    (z : ℂ) (state : CanonicalCompletedC3EnrichedChiralSourceCarrier) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state)
        (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state) =
      ‖canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state‖ ^ 2 -
        ‖canonicalCompletedC3EnrichedPositiveChiralReadout z state‖ ^ 2 := by
  unfold canonicalCompletedC3CausalChiralBoundaryForm
    canonicalCompletedC3EnrichedCausalChiralBoundaryReadout
  change
    inner ℝ
          (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state)
          (canonicalCompletedC3EnrichedCoisometricCameraChiralReadout z state) -
        inner ℝ
          (canonicalCompletedC3EnrichedPositiveChiralReadout z state)
          (canonicalCompletedC3EnrichedPositiveChiralReadout z state) = _
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The source-level contraction is exactly nonpositivity of the existing
indefinite boundary form on the image of every causal source. -/
theorem canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_iff_boundaryForm
    (z : ℂ) :
    CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z ↔
      ∀ state : CanonicalCompletedC3EnrichedChiralSourceCarrier,
        state ∈ canonicalCompletedC3CausalChiralSourceSubmodule →
          canonicalCompletedC3CausalChiralBoundaryForm
              (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state)
              (canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z state) ≤ 0 := by
  constructor
  · intro hdefect state hstate
    rw [canonicalCompletedC3CausalChiralBoundaryForm_readout_self]
    exact sub_nonpos.mpr (hdefect state hstate)
  · intro hform state hstate
    exact sub_nonpos.mp (by
      rw [← canonicalCompletedC3CausalChiralBoundaryForm_readout_self]
      exact hform state hstate)

/-! ## Canonical specialization and upper-half-plane exclusion -/

/-- A causal defect-Gram contraction makes the concrete canonical boundary
datum nonpositive. -/
theorem canonicalCompletedC3CausalChiralBoundaryForm_self_nonpos_of_defectGram
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    canonicalCompletedC3CausalChiralBoundaryForm
        (canonicalCompletedC3CausalChiralBoundaryState M z hzStrip.1)
        (canonicalCompletedC3CausalChiralBoundaryState M z hzStrip.1) ≤ 0 := by
  rw [← canonicalCompletedC3EnrichedCausalChiralBoundaryReadout_sourceState
    M z hzStrip]
  exact
    (canonicalCompletedC3CausalChiralDefectGramNonnegativeAt_iff_boundaryForm
      z).mp hdefect
      (canonicalCompletedC3EnrichedChiralSourceState z hzStrip)
      (canonicalCompletedC3EnrichedChiralSourceState_mem_causalSubmodule
        z hzStrip)

/-- The causal defect-Gram contraction excludes a native bracket closure at
every strictly upper-half-plane point. -/
theorem not_nativeCarryLogWaveBoundaryCloses_of_causalChiralDefectGram
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    ¬ NativeCarryLogWaveBoundaryCloses z := by
  intro hclose
  have hpos :=
    canonicalCompletedC3CausalChiralBoundaryForm_self_pos_of_nativeCarryLogWaveBoundaryCloses
      M z hzIm hzStrip hclose
  have hnonpos :=
    canonicalCompletedC3CausalChiralBoundaryForm_self_nonpos_of_defectGram
      M z hzStrip hdefect
  linarith

/-- In the closed upper half-plane, a native bracket closure and the causal
defect-Gram contraction force the centered height to be real. -/
theorem nativeCarryLogWaveBoundaryCloses_im_eq_zero_of_causalChiralDefectGram
    (M : ℕ) (z : ℂ) (hzIm : 0 ≤ z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hclose : NativeCarryLogWaveBoundaryCloses z)
    (hdefect : CanonicalCompletedC3CausalChiralDefectGramNonnegativeAt z) :
    z.im = 0 := by
  by_contra hne
  have hpos : 0 < z.im := lt_of_le_of_ne hzIm (Ne.symm hne)
  exact
    (not_nativeCarryLogWaveBoundaryCloses_of_causalChiralDefectGram
      M z hpos hzStrip hdefect) hclose

end

end CarrySelfAdjointOperator
