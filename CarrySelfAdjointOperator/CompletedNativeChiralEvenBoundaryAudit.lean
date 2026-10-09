import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

/-! Source-only closure for the raw algebra. The final equivalence necessarily
mentions the canonical target; its closure excludes downstream sign certificates
and spectral consumers, rather than pretending its target is source-only. -/
open Lean Elab Command
elab "#assert_even_boundary_no_downstream " ids:ident+ : command => do
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
      let text := (Lean.privateToUserName name).toString
      let lower := text.toLower
      let classicalTheta := text == "jacobiTheta₂" ||
        text == "jacobiTheta₂_term" || text == "jacobiTheta₂_term._proof_1"
      if lower.contains "hpcarriercertificate" ||
          (lower.contains "jacobi" && !classicalTheta) ||
          lower.contains "heightoperator" || lower.contains "finiteheight" ||
          lower.contains "signedheight" || lower.contains "momentgrampositivity" ||
          lower.contains "br2" || lower.contains "herglotz" then
        throwError "Even-boundary downstream violation: {name}"
      -- Allow the target predicate itself, never its positive-carrier consumers.
      if lower.contains "stieltjes" &&
          text != "CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesPositivity" &&
          text != "CarrySelfAdjointOperator.nativeSourceEvenBoundary_positive_iff_stieltjes" then
        throwError "Even-boundary positive-consumer violation: {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Even-boundary closure checked without downstream consumers: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms nativeSourceFiniteBoundaryEnergy
#print axioms nativeSourceFiniteBoundaryEnergy
#assert_prime_depth_source_axioms nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum
#print axioms nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum
#assert_prime_depth_source_axioms nativeSourceFiniteBoundaryEnergy_even_split
#print axioms nativeSourceFiniteBoundaryEnergy_even_split
#assert_prime_depth_source_axioms nativeSourceEvenBoundaryPhase_fromParity
#print axioms nativeSourceEvenBoundaryPhase_fromParity
#assert_prime_depth_source_axioms nativeSourceOddBoundaryPhase_fromParity
#print axioms nativeSourceOddBoundaryPhase_fromParity
#assert_prime_depth_source_axioms nativeSourceBoundaryFromParity_phases
#print axioms nativeSourceBoundaryFromParity_phases
#assert_prime_depth_source_axioms nativeSourceBoundaryPhase_nonzero
#print axioms nativeSourceBoundaryPhase_nonzero
#assert_oriented_green_source
  nativeSourceFiniteBoundaryEnergy
  nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum
  nativeSourceFiniteBoundaryEnergy_even_split
  nativeSourceEvenBoundaryPhase_fromParity
  nativeSourceOddBoundaryPhase_fromParity
  nativeSourceBoundaryFromParity_phases
  nativeSourceBoundaryPhase_nonzero
#assert_prime_depth_source_axioms nativeSourceEvenBoundary_positive_iff_stieltjes
#print axioms nativeSourceEvenBoundary_positive_iff_stieltjes
#assert_even_boundary_no_downstream nativeSourceEvenBoundary_positive_iff_stieltjes
end CarrySelfAdjointOperator
