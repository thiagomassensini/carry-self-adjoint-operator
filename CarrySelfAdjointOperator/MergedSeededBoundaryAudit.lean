import CarrySelfAdjointOperator.CompletedNativeSeededAffineBoundaryLedger
import Lean
open Lean Elab Command
elab "#assert_merged_seeded_boundary_dependencies " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let deps ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in deps do
    unless allowed.contains name do
      throwError "Unexpected foundational dependency: {decl} depends on {name}"

#assert_merged_seeded_boundary_dependencies CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual
#print axioms CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual

#assert_merged_seeded_boundary_dependencies CarrySelfAdjointOperator.canonicalSeededScalarBoundary_eq_internal_add_cross_add_readoutResidual
#print axioms CarrySelfAdjointOperator.canonicalSeededScalarBoundary_eq_internal_add_cross_add_readoutResidual

#assert_merged_seeded_boundary_dependencies CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual_eq_firstLogGradient
#print axioms CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual_eq_firstLogGradient

#assert_merged_seeded_boundary_dependencies CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual_zero_ne_zero
#print axioms CarrySelfAdjointOperator.canonicalSeededAffineInitialPlacementResidual_zero_ne_zero
