import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
import Lean

open Lean Elab Command

elab "#assert_prime_depth_source_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let deps ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in deps do
    unless allowed.contains name do
      throwError "Unexpected foundational dependency: {decl} depends on {name}"

/-- Walk declaration types and proof bodies, rather than the import graph.
The identification theorem is deliberately excluded from this source check. -/
elab "#assert_prime_depth_source_first " ids:ident+ : command => do
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
      if text.startsWith "CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment" ||
          text == "CarrySelfAdjointOperator.hankelGram" ||
          text == "CarrySelfAdjointOperator.shiftedHankel" ||
          text == "CarrySelfAdjointOperator.finiteJacobiTransport" ||
          text == "CarrySelfAdjointOperator.finiteHeightOperator" ||
          text.startsWith "CarrySelfAdjointOperator.br2CameraBracketProjectiveHilbert" then
        throwError "Source-first violation: reachable declaration {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Source-first dependency closure checked: {seen.size} declarations"

set_option maxHeartbeats 0

namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms primeDepthGeometricMoment
#print axioms primeDepthGeometricMoment
#assert_prime_depth_source_axioms primeDepthResponse_oddCoefficient_recurrence
#print axioms primeDepthResponse_oddCoefficient_recurrence
#assert_prime_depth_source_axioms primeDepthGeometricMoment_zero
#print axioms primeDepthGeometricMoment_zero
#assert_prime_depth_source_axioms primeDepthGeometricMoment_one
#print axioms primeDepthGeometricMoment_one
#assert_prime_depth_source_axioms primeDepthGeometricMoment_two
#print axioms primeDepthGeometricMoment_two
#assert_prime_depth_source_axioms primeDepthGeometricMoment_isLogDerivativeMomentSequence
#print axioms primeDepthGeometricMoment_isLogDerivativeMomentSequence
#assert_prime_depth_source_axioms primeDepthResponse_oddCoefficient_im_zero
#print axioms primeDepthResponse_oddCoefficient_im_zero
#assert_prime_depth_source_axioms primeDepthGeometricMoment_coe
#print axioms primeDepthGeometricMoment_coe
#assert_prime_depth_source_axioms primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor
#print axioms primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor
#assert_prime_depth_source_axioms primeDepthGeometricMoment_eq_canonical
#print axioms primeDepthGeometricMoment_eq_canonical
#assert_prime_depth_source_first
  primeDepthGeometricMoment
  primeDepthResponse_oddCoefficient_recurrence
  primeDepthGeometricMoment_zero
  primeDepthGeometricMoment_one
  primeDepthGeometricMoment_two
  primeDepthGeometricMoment_isLogDerivativeMomentSequence
  primeDepthResponse_oddCoefficient_im_zero
  primeDepthGeometricMoment_coe
  primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor
end CarrySelfAdjointOperator
