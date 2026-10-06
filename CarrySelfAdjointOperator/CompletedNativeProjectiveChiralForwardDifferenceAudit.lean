import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifference
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrenceAudit

open Lean Elab Command

/-- Check proof/type dependencies, not merely module imports. Canonical
coefficient identification is permitted only in the limit layer; BR2 and
moment-matrix/operator inputs are excluded throughout this new route. -/
elab "#assert_chiral_pairing_provenance " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let mut todo : List Name := []
  for id in ids do
    todo := (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id) :: todo
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      let text := name.toString
      if text.startsWith "CarrySelfAdjointOperator.br2" ||
          text.startsWith "CarrySelfAdjointOperator.BR2" ||
          text == "CarrySelfAdjointOperator.hankelGram" ||
          text == "CarrySelfAdjointOperator.shiftedHankel" ||
          text == "CarrySelfAdjointOperator.finiteJacobiTransport" ||
          text == "CarrySelfAdjointOperator.finiteHeightOperator" then
        throwError "Pairing provenance violation: reachable declaration {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Signed pairing provenance closure checked: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms projectiveChiralForm_smul
#print axioms projectiveChiralForm_smul
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet
#print axioms projectiveChiralDifferenceJet
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_eq_weightedSum
#print axioms projectiveChiralDifferenceJet_pairing_eq_weightedSum
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_eq_dslope
#print axioms projectiveChiralDifferenceJet_pairing_eq_dslope
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
#print axioms projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_canaries
#print axioms projectiveChiralDifferenceJet_pairing_canaries
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_tendsto_coefficient
#print axioms projectiveChiralDifferenceJet_pairing_tendsto_coefficient
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_canary_limits
#print axioms projectiveChiralDifferenceJet_pairing_canary_limits
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
#print axioms projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_even_even_tendsto
#print axioms projectiveChiralDifferenceJet_even_even_tendsto
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_odd_odd_tendsto
#print axioms projectiveChiralDifferenceJet_odd_odd_tendsto
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_even_odd_tendsto
#print axioms projectiveChiralDifferenceJet_even_odd_tendsto
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_odd_even_tendsto
#print axioms projectiveChiralDifferenceJet_odd_even_tendsto
#assert_prime_depth_source_axioms projectiveChiralDifferenceJet_two_two_tendsto
#print axioms projectiveChiralDifferenceJet_two_two_tendsto
#assert_prime_depth_source_first
  projectiveChiralForm_smul
  projectiveChiralDifferenceJet
  projectiveChiralDifferenceJet_pairing_eq_weightedSum
  projectiveChiralDifferenceJet_pairing_eq_dslope
  projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
  projectiveChiralDifferenceJet_pairing_canaries
#assert_chiral_pairing_provenance
  projectiveChiralForm_smul
  projectiveChiralDifferenceJet
  projectiveChiralDifferenceJet_pairing_eq_weightedSum
  projectiveChiralDifferenceJet_pairing_eq_dslope
  projectiveChiralDifferenceJet_pairing_eventuallyEq_dslope
  projectiveChiralDifferenceJet_pairing_canaries
  projectiveChiralDifferenceJet_pairing_tendsto_coefficient
  projectiveChiralDifferenceJet_pairing_canary_limits
  projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
  projectiveChiralDifferenceJet_even_even_tendsto
  projectiveChiralDifferenceJet_odd_odd_tendsto
  projectiveChiralDifferenceJet_even_odd_tendsto
  projectiveChiralDifferenceJet_odd_even_tendsto
  projectiveChiralDifferenceJet_two_two_tendsto
end CarrySelfAdjointOperator
