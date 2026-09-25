import CarrySelfAdjointOperator.C3SeededClockShiftIdentity
import CarrySelfAdjointOperator.CompletedNativeCameraResolvedSixSourcePromotionObstruction

/-!
# The ordinary C3 source is affine before any camera resolution

The existing external camera synthesis resolves the logarithmic slope channel.
It cannot be reused for the ordinary value at the incoming vertex: that
failure is recorded by the unit residual in
`CompletedNativeCameraResolvedSixSourcePromotionObstruction`.

This file records the positive structural statement supplied by the native C3
clock instead.  An ordinary incoming value is a *boundary seed* plus a finite
prefix of ordinary gradients.  The seed is global boundary data, not a chosen
camera coordinate.  Thus this is deliberately an affine ledger identity; it
does not claim the as-yet missing camera-wise decomposition of
`positiveDirichletGradient`.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false

/-- The incoming ordinary boundary datum.  This coordinate is deliberately
global: it is not assigned to an external camera label. -/
def canonicalOrdinaryBoundarySeed (s : ℂ) : ℂ :=
  positiveDirichletValue s 0

/-- The canonical ordinary boundary seed is the unit Dirichlet atom. -/
theorem canonicalOrdinaryBoundarySeed_eq_one (s : ℂ) :
    canonicalOrdinaryBoundarySeed s = 1 := by
  simp [canonicalOrdinaryBoundarySeed, positiveDirichletValue]

/-- The ordinary gradient contribution accumulated strictly before the
incoming vertex of C3 block `m`.  This definition remains deliberately
unresolved by camera until a genuine ordinary-gradient camera transport is
provided. -/
def canonicalOrdinaryGradientPrefix (m : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (3 * m), positiveDirichletGradient s n

/-- The affine reconstruction of the ordinary incoming value.  This is the
native prefix identity with the boundary coordinate exposed explicitly. -/
theorem canonicalOrdinaryBoundarySeed_add_gradientPrefix_eq_blockValue
    (m : ℕ) (s : ℂ) :
    canonicalOrdinaryBoundarySeed s + canonicalOrdinaryGradientPrefix m s =
      positiveDirichletValue s (3 * m) := by
  rw [canonicalOrdinaryBoundarySeed, canonicalOrdinaryGradientPrefix]
  exact (nativeC3Block_seed_eq_prefix m s).symm

/-- The full native seeded C3 datum, written in the correct affine form:
the global incoming boundary seed plus the unconsumed ordinary-gradient
prefix, together with the native three-gradient block. -/
def canonicalOrdinaryAffineSeededData (m : ℕ) (s : ℂ) :
    C3TraceDynamics.SeededC3Data :=
  (canonicalOrdinaryBoundarySeed s + canonicalOrdinaryGradientPrefix m s,
    nativeC3BlockGradient m s)

/-- The affine boundary-plus-prefix presentation is literally the existing
native C3 seed/gradient state.  No seed has been assigned to a camera. -/
theorem canonicalOrdinaryAffineSeededData_eq_nativeBlockSeededData
    (m : ℕ) (s : ℂ) :
    canonicalOrdinaryAffineSeededData m s =
      C3TraceDynamics.nativeBlockSeededData m s := by
  apply Prod.ext
  · exact canonicalOrdinaryBoundarySeed_add_gradientPrefix_eq_blockValue m s
  · rfl

/-- Consequently the native four-node reconstruction is already recovered
from the affine ordinary ledger. -/
theorem seededRecover_canonicalOrdinaryAffineSeededData
    (m : ℕ) (s : ℂ) :
    C3TraceDynamics.seededRecover (canonicalOrdinaryAffineSeededData m s) =
      WithLp.toLp 2 ![positiveDirichletValue s (3*m),
        positiveDirichletValue s (3*m+1), positiveDirichletValue s (3*m+2),
        positiveDirichletValue s (3*m+3)] := by
  rw [canonicalOrdinaryAffineSeededData_eq_nativeBlockSeededData]
  exact C3TraceDynamics.seededRecover_nativeBlockSeededData m s

/-- The same global seed remains unit-valued at each of the three six-source
parameter presentations.  Reflection changes the parameter, not ownership of
the boundary atom. -/
theorem canonicalOrdinaryBoundarySeed_parameter_eq_one
    (z w : ℂ) (parameter : CanonicalC3SixSourceParameterRole) :
    canonicalOrdinaryBoundarySeed
      (canonicalC3SixSourceParameterValue z w parameter) = 1 :=
  canonicalOrdinaryBoundarySeed_eq_one _

end

end CarrySelfAdjointOperator
