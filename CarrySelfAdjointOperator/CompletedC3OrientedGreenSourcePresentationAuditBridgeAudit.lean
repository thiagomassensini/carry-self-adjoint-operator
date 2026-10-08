import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridge
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrenceAudit

open Lean Elab Command

/-- The completed source identities may not use a positive downstream
certificate, moment sign/Gram, Jacobi/height or BR2 inputs. -/
elab "#assert_oriented_green_source " ids:ident+ : command => do
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
      -- Audit declaration names, not the historical module address embedded
      -- in private names. Generic reindexing helpers share a BR2-named file
      -- but use no BR2 incidence; their types and values are still traversed.
      let text := (Lean.privateToUserName name).toString
      let lower := text.toLower
      -- Classical Mathlib theta FUNCTIONS, reached by raw analytic integral
      -- facts, are unrelated to spectral Jacobi operators. Only these exact
      -- declarations are exempted; every other Jacobi name stays forbidden.
      let classicalTheta := text == "jacobiTheta₂" ||
        text == "jacobiTheta₂_term" || text == "jacobiTheta₂_term._proof_1"
      if text.startsWith "CarrySelfAdjointOperator.CompletedNativeRealHPCarrierCertificate" ||
          text.startsWith "CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjes" ||
          text.startsWith "CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment" ||
          (lower.contains "hankel") || (lower.contains "jacobi" && !classicalTheta) ||
          (lower.contains "heightoperator") || (lower.contains "finiteheight") ||
          (lower.contains "signedheight") || (lower.contains "stieltjes") ||
          (lower.contains "momentgrampositivity") ||
          (lower.contains "herglotz") ||
          (lower.contains "br2") then
        throwError "Oriented Green source violation: reachable declaration {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Oriented Green source dependency closure checked: {seen.size} declarations"

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
#assert_prime_depth_source_axioms canonicalCompletedGreenFrameSynthesis_preserves_weightedTrace
#print axioms canonicalCompletedGreenFrameSynthesis_preserves_weightedTrace
#assert_prime_depth_source_axioms canonicalCompletedGreenFrameSynthesis_weightedTfvd_reconstruction
#print axioms canonicalCompletedGreenFrameSynthesis_weightedTfvd_reconstruction
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation
#print axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing
#print axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation_dressed_eq_existing
#print axioms canonicalCompletedC3OrientedRecoveredHilbertPresentation_dressed_eq_existing
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq
#print axioms canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedGreenFramePrefixState_zero
#print axioms canonicalCompletedC3OrientedGreenFramePrefixState_zero
#assert_prime_depth_source_axioms canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero
#print axioms canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedRealAxisWrapper_radial_eq_center
#print axioms canonicalCompletedC3OrientedRealAxisWrapper_radial_eq_center
#assert_prime_depth_source_axioms no_linear_orientedPrefix_completedValue_readout
#print axioms no_linear_orientedPrefix_completedValue_readout
#assert_prime_depth_source_axioms canonicalCompletedC3OrientedGreenFrameCarrier_not_parallelogram
#print axioms canonicalCompletedC3OrientedGreenFrameCarrier_not_parallelogram
#assert_oriented_green_source
  canonicalCompletedC3OrientedGreenFrameCarrier_not_parallelogram
  canonicalCompletedGreenFrameSynthesis_preserves_weightedTrace
  canonicalCompletedGreenFrameSynthesis_weightedTfvd_reconstruction
  canonicalCompletedC3OrientedRecoveredHilbertPresentation
  canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing
  canonicalCompletedC3OrientedRecoveredHilbertPresentation_dressed_eq_existing
  canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq
  canonicalCompletedC3OrientedGreenFramePrefixState_zero
  canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero
  canonicalCompletedC3OrientedRealAxisWrapper_radial_eq_center
  no_linear_orientedPrefix_completedValue_readout
end CarrySelfAdjointOperator
