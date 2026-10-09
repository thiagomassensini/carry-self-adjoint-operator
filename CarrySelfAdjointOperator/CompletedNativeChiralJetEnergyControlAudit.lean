import CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControl
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryAudit

/-! Uniform control and the reused source-certified six-jet margin use no
positive downstream consumer. The old signed coefficient limit permits its
already-closed final scalar uniqueness identification; no moment sign is used. -/
open Lean Elab Command

/-- Stricter check than the old boundary-equivalence audit: no Hankel or
Stieltjes declaration, even its target predicate, supplies the energy bound. -/
elab "#assert_chiral_control_no_hankel " ids:ident+ : command => do
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
      let lower := (Lean.privateToUserName name).toString.toLower
      if lower.contains "hankel" || lower.contains "stieltjes" then
        throwError "Chiral-control positive-consumer violation: {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Chiral-control closure without Hankel/Stieltjes: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
#print axioms nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
#assert_prime_depth_source_axioms nativeSourceFiniteBoundaryEnergy_smul
#print axioms nativeSourceFiniteBoundaryEnergy_smul
#assert_prime_depth_source_axioms nativeSourceFiniteBoundaryEnergy_six
#print axioms nativeSourceFiniteBoundaryEnergy_six
#assert_prime_depth_source_axioms nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
#print axioms nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
#assert_prime_depth_source_axioms nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant
#print axioms nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant
#assert_oriented_green_source
  nativeSourceFiniteBoundaryEnergy_smul
  nativeSourceFiniteBoundaryEnergy_six
#assert_even_boundary_no_downstream
  nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
  nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
  nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant
#assert_chiral_control_no_hankel
  nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control
  nativeSourceFiniteBoundaryEnergy_smul
  nativeSourceFiniteBoundaryEnergy_six
  nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_relative_control
  nativeSourceProjectiveBoundaryJetSynthesis_six_eventually_dominant
end CarrySelfAdjointOperator
