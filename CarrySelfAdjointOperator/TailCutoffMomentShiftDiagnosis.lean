import CarrySelfAdjointOperator.FinitePhysicalSixCameraWhiteningBridge
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.CompletedNativeCorrectedChiralClockTower
import Mathlib.Tactic

/-!
# Cutoff-tail shift versus moment-order shift

This file records the part of the comparison that is literal in the present
development.  Advancing a camera cutoff is a translation of the aligned-center
tail.  Advancing a moment order is instead the interior transport of the
polarized Green coefficient tower.  The two are deliberately kept as different
indices here: no tail-to-moment linear map is introduced.

The first theorem is the exact scalar tail recurrence.  It is useful both as a
diagnostic and as a guardrail: it says what the cutoff shift actually does
before the normalized Wronskian response and its Taylor jets are formed.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Raising the geometric cutoff removes exactly its leading aligned-center
block from the completion tail.  This is a cutoff/center translation, not a
moment-order shift. -/
theorem finiteCameraPhysicalCompletionTail_succ
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ) :
    finiteCameraPhysicalCompletionTail camera (cutoff + 1) time =
      finiteCameraPhysicalCompletionTail camera cutoff time -
        centerBracketTerm camera (nativeLine time) cutoff := by
  let f : ℕ → ℂ := centerBracketTerm camera (nativeLine time)
  have hsum : Summable f :=
    centerBracketTerm_summable hcamera (by
      rw [nativeLine_re]
      norm_num)
  have hinj : Function.Injective (fun index : ℕ => index + cutoff) := by
    intro left right h
    exact Nat.add_right_cancel h
  have htail : Summable (fun index : ℕ => f (index + cutoff)) :=
    hsum.comp_injective hinj
  have hsplit := htail.sum_add_tsum_nat_add 1
  change (∑' index : ℕ, f (index + (cutoff + 1))) =
    (∑' index : ℕ, f (index + cutoff)) - f cutoff
  rw [Finset.sum_range_one] at hsplit
  simp only [zero_add] at hsplit
  have htailSucc :
      (∑' index : ℕ, f (index + (cutoff + 1))) =
        ∑' index : ℕ, f (index + 1 + cutoff) := by
    apply tsum_congr
    intro index
    congr 1
    omega
  rw [htailSucc]
  apply eq_sub_iff_add_eq.mpr
  calc
    (∑' index : ℕ, f (index + 1 + cutoff)) + f cutoff =
        f cutoff + ∑' index : ℕ, f (index + 1 + cutoff) := by ring
    _ = ∑' index : ℕ, f (index + cutoff) := hsplit

/-- The completed Wronskian response reads the moments only after a
normalization by the completed characteristic.  This theorem records the
exact already-proved response-to-moment stage; it intentionally has no claim
that the raw aligned-center tail is linearly mapped to these moments. -/
theorem canonicalC3BracketTfvdResponseJet_odd_eq_moment
    (carrierCutoff order : ℕ) :
    canonicalC3BracketTfvdResponseTaylorCoefficient carrierCutoff (2 * order + 1) =
      (canonicalCompletedNativeLogDerivativeMoment order : ℂ) :=
  by
    rw [canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed,
      completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- The existing corrected clock tower transports **moment order** diagonally.
This is the Hankel/Green shift, whose coordinates are the Taylor-jet orders
`p,q`, not the aligned-center cutoff coordinate of the preceding theorem. -/
theorem canonicalCompletedNativeMomentTower_shift
    (p q : ℕ) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient p (q + 1) =
      canonicalCompletedNativeCorrectedClockTowerCoefficient (p + 1) q :=
  canonicalCompletedNativeCorrectedClockTower_shift p q

end

end CarrySelfAdjointOperator
