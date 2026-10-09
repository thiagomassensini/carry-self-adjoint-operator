import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms completedNativeOperatorLogDerivative_eq_twice_greenResponse
#print axioms completedNativeOperatorLogDerivative_eq_twice_greenResponse
#assert_prime_depth_source_axioms nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment
#print axioms nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment
#assert_prime_depth_source_axioms nativeSourceOddBoundaryCoefficient_weighted_eq_primeDepth
#print axioms nativeSourceOddBoundaryCoefficient_weighted_eq_primeDepth
#assert_prime_depth_source_axioms nativeSourceEvenBoundaryCoefficient_eq_polarizedPrimeDepth
#print axioms nativeSourceEvenBoundaryCoefficient_eq_polarizedPrimeDepth
#assert_prime_depth_source_axioms nativeSourceOddBoundaryCoefficient_eq_polarizedPrimeDepth
#print axioms nativeSourceOddBoundaryCoefficient_eq_polarizedPrimeDepth
#assert_prime_depth_source_axioms nativeSourceOddGreenTower_eq_primeDepth
#print axioms nativeSourceOddGreenTower_eq_primeDepth

#assert_oriented_green_source
  completedNativeOperatorLogDerivative_eq_twice_greenResponse
  nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment
  nativeSourceOddBoundaryCoefficient_weighted_eq_primeDepth
  nativeSourceEvenBoundaryCoefficient_eq_polarizedPrimeDepth
  nativeSourceOddBoundaryCoefficient_eq_polarizedPrimeDepth
  nativeSourceOddGreenTower_eq_primeDepth
end CarrySelfAdjointOperator

/- The first source-facing sign obligation is type-checked ONLY.
This command is not a proof, assumed constant, assumption interface or new declaration. -/
open scoped BigOperators ComplexConjugate
#check (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin N → ℂ,
  let b : ℕ → ℂ := fun a => if ha : a < N then x ⟨a,ha⟩ else 0
  ε * ‖x‖^2 ≤ 2 * (∑ j ∈ Finset.range N,
    (-1 : ℝ)^j * CarrySelfAdjointOperator.nativeSourceOddBoundaryCoefficient j *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a * (conj (b a)*b (2*j-a)).re)))
