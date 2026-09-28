import CarrySelfAdjointOperator.MinimalNativeCarryConfinementCapstone
import CPFormal.Analytic.CpNativeGenuineGreenCompletedCrosswalk

/-!
# Minimal Native/Genuine confinement audit

This file adds no new mathematical input.  It only audits the logical
strength of the existing Native/Genuine confinement interfaces and records
the already-proved confinement of the completed Green operator.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

/-- Native C3 confinement stated directly on the primitive real-operator zero
predicate, with no additional structural hypothesis. -/
def FinalNativeZeroConfinement : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    IsNativeCarryRealOperatorZero 3 s.re s.im →
      s.re = (1 : ℝ) / 2

/-- Inside the open Genuine strip, Native C3 and Genuine have exactly the
same zero locus, hence their confinement statements are equivalent. -/
theorem finalNativeZeroConfinement_iff_finalGenuineZeroConfinement :
    FinalNativeZeroConfinement ↔
      NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  constructor
  · intro hnative s hs hgenuine
    apply hnative hs
    exact
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs).2
        hgenuine
  · intro hgenuine s hs hnative
    apply hgenuine hs
    exact
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs).1
        hnative

/-- Semantic audit of the current boundary no-leak hypothesis.  The forward
direction is the existing confinement theorem.  Conversely, once confinement
is assumed there are no off-critical Genuine zeros, so the no-leak obligation
is discharged vacuously. -/
theorem globalBoundaryNoLeak_iff_finalGenuineZeroConfinement :
    CanonicalCompletedC3GlobalBoundaryNoLeakOnGenuineKernel ↔
      NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  constructor
  · exact finalGenuineZeroConfinement_of_globalBoundaryNoLeakOnGenuineKernel
  · intro hconf s hs hzero hoff
    exact False.elim (hoff (hconf hs hzero))

/-- A zero of the already-completed two-channel Green operator is
unconditionally confined to the half-abscissa by the existing exact zero
characterization. -/
theorem genuineGreenCompleted_zero_re_eq_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineGreenCompletedLimitOperator p q s = 0) :
    s.re = (1 : ℝ) / 2 := by
  exact
    ((genuineGreenCompletedLimitOperator_eq_zero_iff_nativeZero_and_re_eq_half
      p q hp hq hs).1 hzero).2

#print axioms finalNativeZeroConfinement_iff_finalGenuineZeroConfinement
#print axioms globalBoundaryNoLeak_iff_finalGenuineZeroConfinement
#print axioms genuineGreenCompleted_zero_re_eq_half

end CarrySelfAdjointOperator
