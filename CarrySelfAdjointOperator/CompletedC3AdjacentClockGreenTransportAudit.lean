import CarrySelfAdjointOperator.CompletedC3AdjacentClockGreenTransport
import CarrySelfAdjointOperator.CompletedC3OrientedGreenSourcePresentationAuditBridgeAudit

set_option maxHeartbeats 0
namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
set_option autoImplicit false
#assert_prime_depth_source_axioms canonicalC3LogGradient_right_productRule
#print axioms canonicalC3LogGradient_right_productRule
#assert_prime_depth_source_axioms canonicalC3LogGradient_left_productRule
#print axioms canonicalC3LogGradient_left_productRule
#assert_prime_depth_source_axioms canonicalC3AdjacentClockChannels
#print axioms canonicalC3AdjacentClockChannels
#assert_prime_depth_source_axioms canonicalC3AdjacentClockChannels_eq_mixedWedge
#print axioms canonicalC3AdjacentClockChannels_eq_mixedWedge
#assert_prime_depth_source_axioms canonicalC3AdjacentMaterialLegIndex
#print axioms canonicalC3AdjacentMaterialLegIndex
#assert_prime_depth_source_axioms canonicalC3MixedLegWedge_at_materialIndex
#print axioms canonicalC3MixedLegWedge_at_materialIndex
#assert_prime_depth_source_axioms canonicalC3AdjacentClockChannelFamily
#print axioms canonicalC3AdjacentClockChannelFamily
#assert_prime_depth_source_axioms canonicalC3MixedPrefixLeg_clockTransport
#print axioms canonicalC3MixedPrefixLeg_clockTransport
#assert_prime_depth_source_axioms canonicalC3MixedPrefixGreenProvenance_clockTransport
#print axioms canonicalC3MixedPrefixGreenProvenance_clockTransport
#assert_prime_depth_source_axioms canonicalC3MixedPrefixHead_clockTransport
#print axioms canonicalC3MixedPrefixHead_clockTransport
#assert_prime_depth_source_axioms canonicalC3AdjacentClockChannels_sameParameter_first
#print axioms canonicalC3AdjacentClockChannels_sameParameter_first
#assert_prime_depth_source_axioms canonicalC3MixedPrefixGreenProvenance_sameParameter
#print axioms canonicalC3MixedPrefixGreenProvenance_sameParameter
#assert_prime_depth_source_axioms canonicalC3Sample_eq_seed_add_gradientPrefix
#print axioms canonicalC3Sample_eq_seed_add_gradientPrefix
#assert_prime_depth_source_axioms canonicalC3Sample_eq_seed_add_completedGradientPrefix
#print axioms canonicalC3Sample_eq_seed_add_completedGradientPrefix
#assert_prime_depth_source_axioms canonicalC3AdjacentClockReturn_eq_seededPrefix
#print axioms canonicalC3AdjacentClockReturn_eq_seededPrefix
#assert_oriented_green_source
  canonicalC3LogGradient_right_productRule
  canonicalC3LogGradient_left_productRule
  canonicalC3AdjacentClockChannels
  canonicalC3AdjacentClockChannels_eq_mixedWedge
  canonicalC3AdjacentMaterialLegIndex
  canonicalC3MixedLegWedge_at_materialIndex
  canonicalC3AdjacentClockChannelFamily
  canonicalC3MixedPrefixLeg_clockTransport
  canonicalC3MixedPrefixGreenProvenance_clockTransport
  canonicalC3MixedPrefixHead_clockTransport
  canonicalC3AdjacentClockChannels_sameParameter_first
  canonicalC3MixedPrefixGreenProvenance_sameParameter
  canonicalC3Sample_eq_seed_add_gradientPrefix
  canonicalC3Sample_eq_seed_add_completedGradientPrefix
  canonicalC3AdjacentClockReturn_eq_seededPrefix

noncomputable section

/-! First-cell canaries use the actual mixed prefix legs, before synthesis. -/
example (z w : ℂ) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState 1 z w
    let mr : Fin 1 × Fin 2 := (0, 0)
    sameSEdgeBoundaryWedge
      ((x.mixedLegs 1).left mr) ((x.mixedLegs 1).right mr)
      ((x.mixedLegs 1).jetLeft mr) ((x.mixedLegs 1).jetRight mr) =
      (canonicalC3AdjacentClockChannels z w 0).1 +
        (canonicalC3AdjacentClockChannels z w 0).2 := by
  simpa [canonicalC3AdjacentClockChannelFamily, canonicalC3AdjacentMaterialLegIndex] using
    canonicalC3MixedPrefixLeg_clockTransport 1 z w (0, 0)

example (z w : ℂ) :
    let x := canonicalC3AllCutoffMixedSourcePrefixState 1 z w
    let mr : Fin 1 × Fin 2 := (0, 1)
    sameSEdgeBoundaryWedge
      ((x.mixedLegs 1).left mr) ((x.mixedLegs 1).right mr)
      ((x.mixedLegs 1).jetLeft mr) ((x.mixedLegs 1).jetRight mr) =
      (canonicalC3AdjacentClockChannels z w 1).1 +
        (canonicalC3AdjacentClockChannels z w 1).2 := by
  simpa [canonicalC3AdjacentClockChannelFamily, canonicalC3AdjacentMaterialLegIndex] using
    canonicalC3MixedPrefixLeg_clockTransport 1 z w (0, 1)

example (M : ℕ) (z : ℂ) (mr : Fin M × Fin 2) :
    (canonicalC3AdjacentClockChannelFamily M z z mr).1 = 0 := by
  exact canonicalC3AdjacentClockChannels_sameParameter_first z _

end
end CarrySelfAdjointOperator
