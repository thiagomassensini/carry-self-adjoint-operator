import CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenFormCrosswalk
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrenceAudit

open Lean Elab Command

/-- The completed source identities may not use a positive downstream
certificate, moment sign/Gram, Jacobi/height or BR2 inputs. -/
elab "#assert_chiral_green_source " ids:ident+ : command => do
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
          (lower.contains "heightoperator") || (lower.contains "finiteheight") ||
          (lower.contains "signedheight") || (lower.contains "stieltjes") ||
          (lower.contains "momentgrampositivity") ||
          (lower.contains "herglotz") ||
          (lower.contains "br2") then
        throwError "Chiral Green source violation: reachable declaration {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Chiral Green source dependency closure checked: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator.ChiralReturn
#assert_prime_depth_source_axioms source_cross_eq_cauchy_greenForm
#print axioms source_cross_eq_cauchy_greenForm
#assert_prime_depth_source_axioms mixed_synthesis_eq_wronskian_sum
#print axioms mixed_synthesis_eq_wronskian_sum
#assert_prime_depth_source_axioms source_cross_eq_bracketTfvd_wronskian_sum
#print axioms source_cross_eq_bracketTfvd_wronskian_sum
#assert_prime_depth_source_axioms bracketTfvd_wronskian_eq_corrected_green_ledger
#print axioms bracketTfvd_wronskian_eq_corrected_green_ledger
#assert_prime_depth_source_axioms source_cross_eq_corrected_green_ledger
#print axioms source_cross_eq_corrected_green_ledger
#assert_prime_depth_source_axioms source_cross_eventually_eq_corrected_green_ledger
#print axioms source_cross_eventually_eq_corrected_green_ledger
#assert_chiral_green_source
  source_cross_eventually_eq_corrected_green_ledger
  source_cross_eq_cauchy_greenForm
  mixed_synthesis_eq_wronskian_sum
  source_cross_eq_bracketTfvd_wronskian_sum
  bracketTfvd_wronskian_eq_corrected_green_ledger
  source_cross_eq_corrected_green_ledger
end CarrySelfAdjointOperator.ChiralReturn
