import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrenceAudit

open Lean Elab Command

/-- The completed source identities may not use a positive downstream
certificate, moment sign/Gram, Jacobi/height or BR2 inputs. -/
elab "#assert_chiral_storage_source " ids:ident+ : command => do
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
      let lower := text.toLower
      if text.startsWith "CarrySelfAdjointOperator.CompletedNativeRealHPCarrierCertificate" ||
          text.startsWith "CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjes" ||
          text.startsWith "CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment" ||
          (lower.contains "hankel") || (lower.contains "jacobi") ||
          (lower.contains "heightoperator") || (lower.contains "br2") then
        throwError "Storage source violation: reachable declaration {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Storage source dependency closure checked: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator.ChiralReturn
#assert_prime_depth_source_axioms sourceValue
#print axioms sourceValue
#assert_prime_depth_source_axioms sourceCompanion
#print axioms sourceCompanion
#assert_prime_depth_source_axioms source_pair_eq_bracketTfvd
#print axioms source_pair_eq_bracketTfvd
#assert_prime_depth_source_axioms incident_synthesis_eq_source
#print axioms incident_synthesis_eq_source
#assert_prime_depth_source_axioms returned_synthesis_eq_source
#print axioms returned_synthesis_eq_source
#assert_prime_depth_source_axioms norm_chiral_balance_eq_source_cross
#print axioms norm_chiral_balance_eq_source_cross
#assert_prime_depth_source_axioms source_total_energy
#print axioms source_total_energy
#assert_prime_depth_source_axioms storage_re_eq_source_cross
#print axioms storage_re_eq_source_cross
#assert_prime_depth_source_axioms integral_flux_re_eq_source_cross
#print axioms integral_flux_re_eq_source_cross
#assert_prime_depth_source_axioms storage_eventually_eq_source_cross
#print axioms storage_eventually_eq_source_cross
#assert_prime_depth_source_axioms storage_one_eventually_eq_source_cross
#print axioms storage_one_eventually_eq_source_cross
#assert_chiral_storage_source
  sourceValue
  sourceCompanion
  source_pair_eq_bracketTfvd
  incident_synthesis_eq_source
  returned_synthesis_eq_source
  norm_chiral_balance_eq_source_cross
  source_total_energy
  storage_re_eq_source_cross
  integral_flux_re_eq_source_cross
  storage_eventually_eq_source_cross
  storage_one_eventually_eq_source_cross
end CarrySelfAdjointOperator.ChiralReturn
