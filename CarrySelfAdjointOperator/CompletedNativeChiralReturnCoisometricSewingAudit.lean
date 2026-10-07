import CarrySelfAdjointOperator.CompletedNativeChiralReturnCoisometricSewing
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

/-! Source-first footprint and full dependency closure of the camera comparison. -/
set_option maxHeartbeats 0
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.radialCauchy_inner_mul_separation
#print axioms CarrySelfAdjointOperator.ChiralReturn.radialCauchy_inner_mul_separation
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.coisometricSourceSynthesis
#print axioms CarrySelfAdjointOperator.ChiralReturn.coisometricSourceSynthesis
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.coisometricFourChannelBalance
#print axioms CarrySelfAdjointOperator.ChiralReturn.coisometricFourChannelBalance
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.radialBracketWronskian_eq_coisometricGram_sub_defect
#print axioms CarrySelfAdjointOperator.ChiralReturn.radialBracketWronskian_eq_coisometricGram_sub_defect
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_iff_fourChannelBalance_zero
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_iff_fourChannelBalance_zero
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.coisometricEscapeBoundarySynthesis_eq_zero
#print axioms CarrySelfAdjointOperator.ChiralReturn.coisometricEscapeBoundarySynthesis_eq_zero
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.storage_re_eq_coisometricEnergy_sub_fourChannelBalance
#print axioms CarrySelfAdjointOperator.ChiralReturn.storage_re_eq_coisometricEnergy_sub_fourChannelBalance
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.coisometricSource_comparison_eventually
#print axioms CarrySelfAdjointOperator.ChiralReturn.coisometricSource_comparison_eventually
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.coisometricResponse_escape_eq_zero
#print axioms CarrySelfAdjointOperator.ChiralReturn.coisometricResponse_escape_eq_zero
#assert_oriented_green_source
  CarrySelfAdjointOperator.ChiralReturn.radialCauchy_inner_mul_separation
  CarrySelfAdjointOperator.ChiralReturn.coisometricSourceSynthesis
  CarrySelfAdjointOperator.ChiralReturn.coisometricFourChannelBalance
  CarrySelfAdjointOperator.ChiralReturn.radialBracketWronskian_eq_coisometricGram_sub_defect
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_coisometricGram_iff_fourChannelBalance_zero
  CarrySelfAdjointOperator.ChiralReturn.coisometricEscapeBoundarySynthesis_eq_zero
  CarrySelfAdjointOperator.ChiralReturn.storage_re_eq_coisometricEnergy_sub_fourChannelBalance
  CarrySelfAdjointOperator.ChiralReturn.coisometricSource_comparison_eventually
  CarrySelfAdjointOperator.ChiralReturn.coisometricResponse_escape_eq_zero

/-! Low-order canaries retain the actual correction rather than assuming it
vanishes. The two-sample case keeps both independent off-diagonal terms. -/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators
open CPFormal.Analytic.Cp
noncomputable section
example (M k : ℕ) (c : Fin 1 → ℂ)
    (hstrip : ∀ i : Fin 1, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip)
    (hpositive : ∀ i : Fin 1, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c 1).re =
      2 * ‖coisometricSourceSynthesis k c 1 (fun i => (hstrip i).1)‖ ^ 2 -
      2 * (coisometricFourChannelBalance k c c 1 1 (fun i => (hstrip i).1)).im := by
  exact storage_re_eq_coisometricEnergy_sub_fourChannelBalance M k c 1 hstrip hpositive

example (M k : ℕ) (c d : Fin 2 → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin 2, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := fun i : Fin 2 => canonicalCompletedC3RadialTiltPoint k i
    let a := fun i : Fin 2 => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun i : Fin 2 => d i * (s : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let t := fun i j : Fin 2 => star (a i) * b j *
      inner ℂ (completedNativeRadialChiralCauchyState k i)
        (completedNativeRadialChiralCauchyState k j) *
      canonicalCompletedC3CoisometricWronskianFourChannelDefect (z i) (z j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) (hstrip i).1 (hstrip j).1
    polarizedSourceBalance k c d r s =
      2 * inner ℂ (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))
        (coisometricSourceSynthesis k d s (fun i => (hstrip i).1)) +
      2 * Complex.I * (t 0 0 + t 0 1 + (t 1 0 + t 1 1)) := by
  dsimp only
  simpa only [coisometricFourChannelBalance, Fin.sum_univ_two] using
    polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance M k c d r s hstrip
end
end CarrySelfAdjointOperator.ChiralReturn
