import CarrySelfAdjointOperator.C3TraceDynamics
import CarrySelfAdjointOperator.C3ReturnCompletedTraceChannels

/-!
# The native ordinary/log-jet prefix lies on an affine graph

The earlier ambient pulse tests keep the log channel independent. Here the
log channel is transported from the same nodal state. The original no-go
theorems and their canonical witnesses are not changed or discharged.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section
set_option autoImplicit false

/-- The actual three native gradients, not camera-resultant coordinates. -/
def nativeC3GradientTriple (s : ℂ) : Fin 3 → ℂ :=
  ![positiveDirichletGradient s 0, positiveDirichletGradient s 1,
    positiveDirichletGradient s 2]

def nativeC3LogGradientTriple (s : ℂ) : Fin 3 → ℂ :=
  ![positiveLogDirichletGradient s 0, positiveLogDirichletGradient s 1,
    positiveLogDirichletGradient s 2]

/-- Retaining the seed gives the exact native log channel in gradient
coordinates. This graph constraint is stronger than membership in the
ambient direct sum of two unrelated gradient spaces. -/
theorem nativeC3LogGradientTriple_eq_affine_clock (s : ℂ) :
    nativeC3LogGradientTriple s =
      gradientClock (Real.log 2 : ℂ) (Real.log 3 : ℂ) (Real.log 4 : ℂ)
        (nativeC3GradientTriple s) +
      positiveDirichletValue s 0 •
        ![(Real.log 2 : ℂ), (Real.log 3 : ℂ) - (Real.log 2 : ℂ),
          (Real.log 4 : ℂ) - (Real.log 3 : ℂ)] := by
  funext i
  fin_cases i <;>
    simp [nativeC3LogGradientTriple, nativeC3GradientTriple, gradientClock,
      positiveLogDirichletGradient, positiveLogDirichletValue,
      positiveDirichletGradient] <;> ring

/-- In the actual readout orientation the log trace is the last gradient
minus the middle one. The clock forces its variation under the initial pulse. -/
theorem nativeC3_consistent_initialPulse_logTrace (u : ℂ) :
    trace (gradientClock (Real.log 2 : ℂ) (Real.log 3 : ℂ) (Real.log 4 : ℂ)
      ![u, 0, 0]) =
      ((Real.log 2 : ℂ) - 2 * (Real.log 3 : ℂ) + (Real.log 4 : ℂ)) * u :=
  initialPulse_logTrace _ _ _ _

theorem nativeC3_consistent_initialPulse_logTrace_ne_zero (u : ℂ) (hu : u ≠ 0) :
    trace (gradientClock (Real.log 2 : ℂ) (Real.log 3 : ℂ) (Real.log 4 : ℂ)
      ![u, 0, 0]) ≠ 0 := by
  rw [nativeC3_consistent_initialPulse_logTrace]
  apply mul_ne_zero _ hu
  exact_mod_cast (ne_of_lt native_log_trace_gap_neg)

end
end CarrySelfAdjointOperator
