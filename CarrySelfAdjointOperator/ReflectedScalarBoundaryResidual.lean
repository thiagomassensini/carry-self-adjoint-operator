import CarrySelfAdjointOperator.ReflectedScalarBoundaryTrace
import Mathlib.Tactic

/-!
# Reflected scalar boundary with explicit readout residuals

The reflected four-leg synthesis equalities need not be assumed.  For any
finite local ledger, define four linear residuals measuring the difference
between the desired scalar legs

* `conj(logJet)`;
* `conj(value)`;
* `logJet`;
* `value`;

and the corresponding local sums.  Expanding the scalar Wronskian gives an
exact polynomial correction in those residuals.

Consequently

`scalar boundary = local boundary + cross provenance + residual correction`

without a synthesis hypothesis.  This turns a failed synthesis probe into a
typed identity rather than an external premise.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp

/-- Residual in the reflected left leg. -/
def reflectedBoundaryLeftResidual
    {ι : Type*} [Fintype ι]
    (_value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  (starRingEnd ℂ) logJet - ∑ i : ι, legs.left i

/-- Residual in the reflected right leg. -/
def reflectedBoundaryRightResidual
    {ι : Type*} [Fintype ι]
    (value _logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  (starRingEnd ℂ) value - ∑ i : ι, legs.right i

/-- Residual in the left log-jet leg. -/
def reflectedBoundaryJetLeftResidual
    {ι : Type*} [Fintype ι]
    (_value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  logJet - ∑ i : ι, legs.jetLeft i

/-- Residual in the right value leg. -/
def reflectedBoundaryJetRightResidual
    {ι : Type*} [Fintype ι]
    (value _logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  value - ∑ i : ι, legs.jetRight i

/-- Exact bilinear correction produced by the four linear synthesis
residuals. -/
def reflectedBoundaryResidualCorrection
    {ι : Type*} [Fintype ι]
    (value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) : ℂ :=
  let leftResidual := reflectedBoundaryLeftResidual value logJet legs
  let rightResidual := reflectedBoundaryRightResidual value logJet legs
  let jetLeftResidual := reflectedBoundaryJetLeftResidual value logJet legs
  let jetRightResidual := reflectedBoundaryJetRightResidual value logJet legs
  (∑ i : ι, legs.right i) * jetLeftResidual +
    rightResidual * (∑ i : ι, legs.jetLeft i) +
    rightResidual * jetLeftResidual -
    (∑ i : ι, legs.left i) * jetRightResidual -
    leftResidual * (∑ i : ι, legs.jetRight i) -
    leftResidual * jetRightResidual

/-- The scalar Wronskian is the four-leg boundary of the local sums plus the
explicit residual correction. -/
theorem scalarBoundaryWedge_eq_summedTwoLeg_add_residualCorrection
    {ι : Type*} [Fintype ι]
    (value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    scalarBoundaryWedge value logJet =
      sameSEdgeBoundaryWedge
          (∑ i : ι, legs.left i)
          (∑ i : ι, legs.right i)
          (∑ i : ι, legs.jetLeft i)
          (∑ i : ι, legs.jetRight i) +
        reflectedBoundaryResidualCorrection value logJet legs := by
  unfold scalarBoundaryWedge sameSEdgeBoundaryWedge
    reflectedBoundaryResidualCorrection
    reflectedBoundaryLeftResidual reflectedBoundaryRightResidual
    reflectedBoundaryJetLeftResidual reflectedBoundaryJetRightResidual
  dsimp only
  ring

/-- Fully expanded local form: scalar boundary equals diagonal local wedges,
ordered cross provenance, and the residual correction. -/
theorem scalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    {ι : Type*} [Fintype ι]
    (value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    scalarBoundaryWedge value logJet =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight +
        reflectedBoundaryResidualCorrection value logJet legs := by
  rw [scalarBoundaryWedge_eq_summedTwoLeg_add_residualCorrection (ι := ι),
    sameSEdgeBoundaryWedge_sum_eq_local_add_crossProvenance (ι := ι)]

/-- The previous synthesis theorem is recovered when all four residuals
vanish, but vanishing is no longer built into the general identity. -/
theorem scalarBoundaryWedge_eq_localTwoLeg_add_crossProvenance_of_residuals_zero
    {ι : Type*} [Fintype ι]
    (value logJet : ℂ) (legs : ReflectedBoundarySynthesisData ι)
    (hleft : reflectedBoundaryLeftResidual value logJet legs = 0)
    (hright : reflectedBoundaryRightResidual value logJet legs = 0)
    (hjetLeft : reflectedBoundaryJetLeftResidual value logJet legs = 0)
    (hjetRight : reflectedBoundaryJetRightResidual value logJet legs = 0) :
    scalarBoundaryWedge value logJet =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight := by
  rw [scalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection (ι := ι)]
  unfold reflectedBoundaryResidualCorrection
  rw [hleft, hright, hjetLeft, hjetRight]
  simp

end

end CarrySelfAdjointOperator
