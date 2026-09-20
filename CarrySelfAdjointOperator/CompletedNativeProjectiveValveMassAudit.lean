import CarrySelfAdjointOperator.DiscreteProjectiveReconstruction
import CarrySelfAdjointOperator.NativeMomentProjectiveValveBridge
import Mathlib.Tactic

/-!
# Projective-valve mass: reconstruction guardrail

The projective valve is an exact and useful scalar reconstruction mechanism:
the normalized mass is the exponential of the transported discrete
curvature, and the two affine boundary coordinates restore the entire
sequence.  It must nevertheless not be confused with the Hilbert-valued
defect channel sought for the chiral multiplier.

This file makes the distinction concrete over the real scalars.  Two
different sequences with the same zero curvature have the same projective
mass.  Hence the mass alone loses the affine boundary data.  This is not a
no-go for the *three-coordinate* discrete-projective reconstruction, which
is exact, and it is not a claim against a future chiral loss channel coupled
to the actual multiplier `Q`.  It rules out only the unsupported shortcut of
treating the scalar mass itself as a lossless Hilbert defect state.

No moment positivity, Hankel matrix, Cholesky factorization, or spectral
statement is used below.
-/

namespace CarrySelfAdjointOperator

open DiscreteProjective

noncomputable section

/-- The zero-curvature sequence with zero affine boundary data. -/
def projectiveValveMassZeroAffineState : ℕ → ℝ :=
  fun _ ↦ 0

/-- The zero-curvature sequence with a distinct constant affine boundary. -/
def projectiveValveMassOneAffineState : ℕ → ℝ :=
  fun _ ↦ 1

/-- The two test states have exactly the same discrete curvature. -/
theorem projectiveValveMass_testStates_bracket_eq :
    DiscreteValve.bracket projectiveValveMassZeroAffineState =
      DiscreteValve.bracket projectiveValveMassOneAffineState := by
  funext n
  simp [DiscreteValve.bracket,
    projectiveValveMassZeroAffineState, projectiveValveMassOneAffineState]
  ring

/-- Consequently their normalized projective masses agree.  This uses the
existing mass--curvature equivalence, rather than calculating a formal
exponential by hand. -/
theorem projectiveValveMass_testStates_eq :
    DiscreteProjective.stateMass projectiveValveMassZeroAffineState =
      DiscreteProjective.stateMass projectiveValveMassOneAffineState :=
  (DiscreteProjective.stateMass_eq_iff_bracket_eq
    projectiveValveMassZeroAffineState projectiveValveMassOneAffineState).2
    projectiveValveMass_testStates_bracket_eq

/-- The equality of masses does not identify the original states: their
initial values, one of the boundary coordinates retained by
`reconstructionEquiv`, differ. -/
theorem projectiveValveMass_testStates_ne :
    projectiveValveMassZeroAffineState ≠ projectiveValveMassOneAffineState := by
  intro h
  have hzero := congrFun h 0
  norm_num [projectiveValveMassZeroAffineState,
    projectiveValveMassOneAffineState] at hzero

/-- The scalar projective mass is not injective on discrete states.  The
loss of affine boundary information is therefore an exact obstruction to
using this mass *by itself* as a lossless dilation output. -/
theorem not_injective_discreteProjective_stateMass :
    ¬ Function.Injective
      (DiscreteProjective.stateMass : (ℕ → ℝ) → PowerSeries ℝ) := by
  intro hinjective
  exact projectiveValveMass_testStates_ne
    (hinjective projectiveValveMass_testStates_eq)

/-- The scalar native moment series is recovered exactly as the curvature of
the reciprocal native projective mass.  This records what the valve does
provide: scalar curvature provenance, not a polarized Hilbert Gram. -/
theorem projectiveValveMass_nativeMoments_curvature_readback :
    ProjectiveValve.projectiveValveCurvature
        normalizedCompletedNativeEvenFormalSeries⁻¹ =
      PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment :=
  projectiveValveCurvature_nativeReciprocal_eq_moments

end

end CarrySelfAdjointOperator
