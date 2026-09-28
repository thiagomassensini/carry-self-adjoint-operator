import CarrySelfAdjointOperator.CanonicalEnrichedBoundaryResidualIdentity
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import Mathlib.Tactic

/-!
# Seeded affine boundary placement audit

The canonical seeded value port has an exterior value atom, whereas the
retained enriched same-parameter boundary consists only of the two gradient
edges in each C3 block.  This file does **not** define an enlarged boundary
form.  It records the exact outcome of the only comparison already typed by
the existing API: the scalar boundary of the two seeded readouts, with the
existing internal boundary, ordered cross provenance, and readout correction
all retained.

The proposed initial nodal cell from the affine nodal audit has value
`-positiveLogDirichletGradient s 0`.  Adding that value to the existing
scalar ledger without changing any of its other channels leaves the explicit
residual `positiveLogDirichletGradient s 0`.  Thus this is a diagnostic of
placement, not a definition of a new readout or a claim that the nodal cell
belongs to the established two-edge boundary.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

/-- The scalar residual obtained by adjoining the *candidate* initial nodal
value `-ΔJ₀` to the already-established seeded scalar boundary ledger.  The
comparison is deliberately made only after the existing readout has retained
its internal boundary, cross provenance, and readout-residual channel. -/
def canonicalSeededAffineInitialPlacementResidual
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  scalarBoundaryWedge
      (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
      (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdLogJetPort kappa omega s)) -
    (-positiveLogDirichletGradient s 0 +
      finiteC3EnrichedTfvdPairBoundaryForm M
        (canonicalBoundaryResidualData M kappa omega s) +
      canonicalBoundaryCrossProvenance M kappa omega s +
      canonicalBoundaryReadoutResidualCorrection M kappa omega s)

/-- Before adjoining any nodal cell, the scalar boundary of the canonical
seeded readouts is exactly the existing internal enriched boundary plus the
already retained ordered-cross and readout-residual channels. -/
theorem canonicalSeededScalarBoundary_eq_internal_add_cross_add_readoutResidual
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    scalarBoundaryWedge
        (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
          (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
        (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
          (canonicalSeededEnrichedTfvdLogJetPort kappa omega s)) =
      finiteC3EnrichedTfvdPairBoundaryForm M
          (canonicalBoundaryResidualData M kappa omega s) +
        canonicalBoundaryCrossProvenance M kappa omega s +
        canonicalBoundaryReadoutResidualCorrection M kappa omega s := by
  have hscalar := canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
    M hkappa omega homega s
  have hgreen := finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
    M hkappa omega homega s
  change scalarBoundaryWedge
      (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
      (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdLogJetPort kappa omega s)) = _ at hscalar
  change finiteC3EnrichedTfvdPairBoundaryForm M
      (canonicalBoundaryResidualData M kappa omega s) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s = _ at hgreen
  linear_combination hscalar - hgreen

/-- The exact mismatch of the proposed initial nodal contribution with the
unchanged seeded scalar ledger is the first logarithmic discrete gradient.
Equivalently, adjoining the previous audit's initial cell `-ΔJ₀` would add a
genuinely new term; it is not already the exterior seed of this ledger. -/
theorem canonicalSeededAffineInitialPlacementResidual_eq_firstLogGradient
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    canonicalSeededAffineInitialPlacementResidual M kappa omega s =
      positiveLogDirichletGradient s 0 := by
  unfold canonicalSeededAffineInitialPlacementResidual
  rw [canonicalSeededScalarBoundary_eq_internal_add_cross_add_readoutResidual
    M hkappa omega homega s]
  ring

/-- The placement residual is already nonzero at the zero parameter.  This
rules out the unmodified identity obtained by simply prepending the nodal
cell to the present two-edge seeded scalar ledger. -/
theorem canonicalSeededAffineInitialPlacementResidual_zero_ne_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    canonicalSeededAffineInitialPlacementResidual M kappa omega (0 : ℂ) ≠ 0 := by
  rw [canonicalSeededAffineInitialPlacementResidual_eq_firstLogGradient
    M hkappa omega homega]
  rw [positiveLogDirichletGradient, positiveLogDirichletValue_zero, sub_zero]
  unfold positiveLogDirichletValue
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · have hnorm := norm_positiveDirichletValue (0 : ℂ) 1
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    positivity

#print axioms canonicalSeededScalarBoundary_eq_internal_add_cross_add_readoutResidual
#print axioms canonicalSeededAffineInitialPlacementResidual_eq_firstLogGradient
#print axioms canonicalSeededAffineInitialPlacementResidual_zero_ne_zero

end

end CarrySelfAdjointOperator
