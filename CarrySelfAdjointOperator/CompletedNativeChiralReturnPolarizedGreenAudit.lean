import CarrySelfAdjointOperator.CompletedNativeChiralReturnPolarizedGreen
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

/-! Trust-footprint and source-only closure of the full polarized balance. -/
set_option maxHeartbeats 0
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance
#print axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_total
#print axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_total
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_greenForm
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_greenForm
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_self_eq_storage
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_self_eq_storage
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_conj_symm
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_conj_symm
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance_isometry
#print axioms CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance_isometry
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarized_mixed_synthesis_eq_wronskian_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarized_mixed_synthesis_eq_wronskian_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_bracketTfvd_sum
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_bracketTfvd_sum
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_corrected_green_ledger
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_corrected_green_ledger
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_native_add_completion
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_native_add_completion
#assert_prime_depth_source_axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eventually_complete
#print axioms CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eventually_complete
#assert_oriented_green_source
  CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance
  CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_total
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_greenForm
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_self_eq_storage
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_conj_symm
  CarrySelfAdjointOperator.ChiralReturn.chiral_pairing_balance_isometry
  CarrySelfAdjointOperator.ChiralReturn.polarized_mixed_synthesis_eq_wronskian_sum
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_bracketTfvd_sum
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_corrected_green_ledger
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eq_native_add_completion
  CarrySelfAdjointOperator.ChiralReturn.polarizedSourceBalance_eventually_complete

/-! Two independent coefficient families, with all four ordered terms.
These are identity canaries; no positive sign is an input or conclusion. -/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators
open CPFormal.Analytic.Cp
noncomputable section
example (M k : ℕ) (c d : Fin 1 → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin 1, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := canonicalCompletedC3RadialTiltPoint k 0
    let a := c 0 * (r : ℂ) / completedNativePositiveHermiteBiehlerCoordinate z
    let b := d 0 * (s : ℂ) / completedNativePositiveHermiteBiehlerCoordinate z
    polarizedSourceBalance k c d r s = -2 * Complex.I *
      (star a * b * inner ℂ (completedNativeRadialChiralCauchyState k 0)
        (completedNativeRadialChiralCauchyState k 0) *
        canonicalC3BracketTfvdCompletedWronskianReadout M z z) := by
  simpa using polarizedSourceBalance_eq_bracketTfvd_sum M k c d r s hstrip

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
      canonicalC3BracketTfvdCompletedWronskianReadout M (z j) (z i)
    polarizedSourceBalance k c d r s = -2 * Complex.I *
      (t 0 0 + t 0 1 + (t 1 0 + t 1 1)) := by
  dsimp only
  simpa only [Fin.sum_univ_two] using
    polarizedSourceBalance_eq_bracketTfvd_sum M k c d r s hstrip
end
end CarrySelfAdjointOperator.ChiralReturn
