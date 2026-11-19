import ResidualReturn
import HigherOrderCayleyDefect
import Mathlib.Tactic

/-!
# Exact equality with the ORIGINAL physical native return (GoN)
This identifies the computed cubic defect with the physical coefficients,
not just a separate Cayley test on a similar radial grid.
-/

namespace CarryCauchyResidual
open CarrySelfAdjointOperator
open CarrySelfAdjointOperator.HigherOrderCayleyDefect
open ChiralReturn CarryPositiveSquare
open Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

private theorem actual_radial_point_eq (k n : ℕ) :
    canonicalCompletedC3RadialTiltPoint k n =
      Complex.I * ((((n+1:ℕ):ℝ)*radialStepReal k:ℝ):ℂ) := by
  unfold canonicalCompletedC3RadialTiltPoint
    canonicalCompletedC3RadialTiltStep canonicalGreenJetStep radialStepReal
  have hk : (k:ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
  push_cast
  field_simp [hk]

theorem original_source_return_eq_actual (k n : ℕ) :
    sourceReturn k n =
      nativeRadialQuotient (((n+1:ℕ):ℝ)*radialStepReal k) := by
  unfold sourceReturn nativeRadialQuotient
  rw [actual_radial_point_eq]

theorem original_one_return_eq_actual (k : ℕ) :
    oneReturn k = nativeRadialQuotient (radialStepReal k) := by
  unfold oneReturn nativeRadialQuotient
  rw [actual_radial_point_eq]
  norm_num

theorem original_incident_eq_actual_radial (k i : ℕ) :
    incidentCoefficient k i =
      actualRadialIncidentCoefficient i (radialStepReal k) := by
  unfold incidentCoefficient feedbackDenominator actualRadialIncidentCoefficient
  rw [original_one_return_eq_actual, original_source_return_eq_actual]

theorem original_returned_eq_actual_radial (k i : ℕ) :
    returnedCoefficient k i =
      actualRadialReturnedCoefficient i (radialStepReal k) := by
  unfold returnedCoefficient actualRadialReturnedCoefficient
  rw [original_one_return_eq_actual, original_source_return_eq_actual]

theorem original_native_physical_cubic_defect_tendsto (i : ℕ) :
    Tendsto
      (fun k : ℕ => (incidentCoefficient k i - returnedCoefficient k i) /
        (radialStep k)^3)
      atTop
      (nhds (8*(i:ℂ)*((i:ℂ)+1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ))) := by
  simpa only [original_incident_eq_actual_radial,
    original_returned_eq_actual_radial] using
    native_actual_incident_return_cubic_tendsto i

#print axioms original_native_physical_cubic_defect_tendsto
#print axioms original_incident_eq_actual_radial
end
end CarryCauchyResidual
