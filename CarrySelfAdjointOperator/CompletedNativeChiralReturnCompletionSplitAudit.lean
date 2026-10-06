import CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplit
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

/-! Source-first trust-footprint and transitive dependency firewall for the completion
vector split. No positive certificate or moment target may be a proof input. -/
set_option maxHeartbeats 0
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.canonicalC3BracketTfvdNormalizedTracePair_eq_native
#print axioms CarrySelfAdjointOperator.canonicalC3BracketTfvdNormalizedTracePair_eq_native
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.nativeArchimedeanCompanionChannels_zero_cancel
#print axioms CarrySelfAdjointOperator.nativeArchimedeanCompanionChannels_zero_cancel
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.canonicalArchimedeanBoundaryGreenCorrection_zero_cancel
#print axioms CarrySelfAdjointOperator.canonicalArchimedeanBoundaryGreenCorrection_zero_cancel
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.nativeDressedCompanion
#print axioms CarrySelfAdjointOperator.ChiralReturn.nativeDressedCompanion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.completionCompanion
#print axioms CarrySelfAdjointOperator.ChiralReturn.completionCompanion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.sourceValue_eq_native_product
#print axioms CarrySelfAdjointOperator.ChiralReturn.sourceValue_eq_native_product
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eq_native_add_completion
#print axioms CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eq_native_add_completion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.companion_channels_eq_bracketTfvd
#print axioms CarrySelfAdjointOperator.ChiralReturn.companion_channels_eq_bracketTfvd
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.completion_pairing_skew_eq_archimedean_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.completion_pairing_skew_eq_archimedean_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.native_pairing_skew_eq_weighted_green_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.native_pairing_skew_eq_weighted_green_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.source_pairing_skew_eq_product_green_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.source_pairing_skew_eq_product_green_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.completion_orientation_eq_archimedean_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.completion_orientation_eq_archimedean_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.source_cross_eq_native_add_completion
#print axioms CarrySelfAdjointOperator.ChiralReturn.source_cross_eq_native_add_completion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eventually_eq_native_add_completion
#print axioms CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eventually_eq_native_add_completion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.storage_eventually_eq_native_add_completion
#print axioms CarrySelfAdjointOperator.ChiralReturn.storage_eventually_eq_native_add_completion
#assert_oriented_green_source
  CarrySelfAdjointOperator.canonicalC3BracketTfvdNormalizedTracePair_eq_native
  CarrySelfAdjointOperator.nativeArchimedeanCompanionChannels_zero_cancel
  CarrySelfAdjointOperator.canonicalArchimedeanBoundaryGreenCorrection_zero_cancel
  CarrySelfAdjointOperator.ChiralReturn.nativeDressedCompanion
  CarrySelfAdjointOperator.ChiralReturn.completionCompanion
  CarrySelfAdjointOperator.ChiralReturn.sourceValue_eq_native_product
  CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eq_native_add_completion
  CarrySelfAdjointOperator.ChiralReturn.companion_channels_eq_bracketTfvd
  CarrySelfAdjointOperator.ChiralReturn.completion_pairing_skew_eq_archimedean_sum
  CarrySelfAdjointOperator.ChiralReturn.native_pairing_skew_eq_weighted_green_sum
  CarrySelfAdjointOperator.ChiralReturn.source_pairing_skew_eq_product_green_sum
  CarrySelfAdjointOperator.ChiralReturn.completion_orientation_eq_archimedean_sum
  CarrySelfAdjointOperator.ChiralReturn.source_cross_eq_native_add_completion
  CarrySelfAdjointOperator.ChiralReturn.sourceCompanion_eventually_eq_native_add_completion
  CarrySelfAdjointOperator.ChiralReturn.storage_eventually_eq_native_add_completion

/-! Concrete one- and two-sample algebra canaries. The two-sample expansion
retains both off-diagonal terms; neither test assumes a sign. -/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators
noncomputable section
example (k : ℕ) (c : Fin 1 → ℂ) (r : ℝ) :
    let z := canonicalCompletedC3RadialTiltPoint k 0
    let d := c 0 * (r : ℂ) / completedNativePositiveHermiteBiehlerCoordinate z
    inner ℂ (sourceValue k c r) (completionCompanion k c r) -
        inner ℂ (completionCompanion k c r) (sourceValue k c r) =
      star d * d * inner ℂ (completedNativeRadialChiralCauchyState k 0)
        (completedNativeRadialChiralCauchyState k 0) *
        canonicalArchimedeanBoundaryGreenCorrection z z := by
  simpa using completion_pairing_skew_eq_archimedean_sum k c r

example (k : ℕ) (c : Fin 2 → ℂ) (r : ℝ) :
    let z := fun i : Fin 2 => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin 2 => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let t := fun i j : Fin 2 => star (d i) * d j *
      inner ℂ (completedNativeRadialChiralCauchyState k i)
        (completedNativeRadialChiralCauchyState k j) *
        canonicalArchimedeanBoundaryGreenCorrection (z i) (z j)
    inner ℂ (sourceValue k c r) (completionCompanion k c r) -
        inner ℂ (completionCompanion k c r) (sourceValue k c r) =
      t 0 0 + t 0 1 + (t 1 0 + t 1 1) := by
  dsimp only
  simpa only [Fin.sum_univ_two] using completion_pairing_skew_eq_archimedean_sum k c r
end
end CarrySelfAdjointOperator.ChiralReturn
