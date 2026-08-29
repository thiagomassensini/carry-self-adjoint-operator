import CarrySelfAdjointOperator.CompletedC3RecoveredEnrichedWronskianCarrier
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Tactic

/-!
# First positivity gate for the recovered completed C3 kernel

The recovered enriched carrier realizes the completed Wronskian and its
canonically normalized readout converges to the completed-native `dslope`.
This file records where positivity first enters that construction.  At the
central diagonal the removable closure is exactly the zeroth canonical
moment; it is not the norm of the recovered pair carrier by definition.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- The central diagonal of every recovered cutoff kernel is exactly the
zeroth completed-native logarithmic moment.  In particular, the value is
cutoff-independent. -/
theorem canonicalCompletedC3RecoveredAllCutoffRealKernelReadout_zero_zero
    (M : ℕ) :
    canonicalCompletedC3RecoveredAllCutoffRealKernelReadout M 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [canonicalCompletedC3RecoveredAllCutoffRealKernelReadout]
  simp only [ite_true]
  have h :=
    completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized 0 0
  simpa [completedNativeGreenResponseTaylorCoefficient,
    polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using h

/-- All-order Stieltjes positivity forces strict positivity already at the
central diagonal.  This is the first scalar consequence that any geometric
positive realization of the recovered kernel must reproduce. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_stieltjes
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hdiag := (hpos 1).1.diag_pos (i := (0 : Fin 1))
  simpa [hankelGram] using hdiag

/-- The shifted one-by-one Hankel section similarly forces positivity of the
first shifted moment. -/
theorem canonicalCompletedNativeLogDerivativeMoment_one_pos_of_stieltjes
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  have hdiag := (hpos 1).2.diag_pos (i := (0 : Fin 1))
  simpa [shiftedHankel] using hdiag

/-- At size one there is no hidden matrix condition: the two Stieltjes
sections are positive definite exactly when the central and first shifted
moments are strictly positive. -/
theorem canonicalCompletedNativeHankelPair_one_posDef_iff :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 1).PosDef ∧
        (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment 1).PosDef ↔
      0 < canonicalCompletedNativeLogDerivativeMoment 0 ∧
        0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  constructor
  · rintro ⟨heven, hodd⟩
    exact ⟨by simpa [hankelGram] using
        (heven.diag_pos (i := (0 : Fin 1))),
      by simpa [shiftedHankel] using
        (hodd.diag_pos (i := (0 : Fin 1)))⟩
  · rintro ⟨hm0, hm1⟩
    constructor
    · rw [show hankelGram canonicalCompletedNativeLogDerivativeMoment 1 =
          Matrix.diagonal (fun _ : Fin 1 =>
            canonicalCompletedNativeLogDerivativeMoment 0) by
        ext i j
        fin_cases i
        fin_cases j
        simp [hankelGram]]
      exact Matrix.posDef_diagonal_iff.mpr (fun _ => hm0)
    · rw [show shiftedHankel canonicalCompletedNativeLogDerivativeMoment 1 =
          Matrix.diagonal (fun _ : Fin 1 =>
            canonicalCompletedNativeLogDerivativeMoment 1) by
        ext i j
        fin_cases i
        fin_cases j
        simp [shiftedHankel]]
      exact Matrix.posDef_diagonal_iff.mpr (fun _ => hm1)

end

end CarrySelfAdjointOperator
