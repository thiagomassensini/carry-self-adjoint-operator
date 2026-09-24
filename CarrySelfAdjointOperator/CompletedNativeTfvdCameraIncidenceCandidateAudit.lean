import CarrySelfAdjointOperator.CompletedNativeTfvdCameraParsevalIncidenceTransport
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import Mathlib.Tactic

/-!
# Audit of the existing BR2 -> TFVD -> recovered-Hilbert candidate

The established BR2/TFVD maps provide a faithful all-order transport, but its
finite TFVD analysis followed by the existing reconstruction returns the
literal completed vertical bracket.  It is therefore a source-side total
transport, not yet a camera compression into `FiniteHilbertFamily`.

This file computes the resulting coefficient defect before attempting to
force a camera interpretation.  The defect is exactly the negative of the
already-defined BR2 energy excess.  Its first four entries show that this raw
recovered candidate has the known `0,2` versus `1,1` Hankel failure.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk

noncomputable section

/-- The actual finite TFVD port followed by its exact existing reconstruction,
applied to the BR2 parity jet.  This is the maximal source-side transport
already supplied by the TFVD genealogy; it deliberately precedes a finite
camera family/readout. -/
def br2FiniteTfvdRecoveredParityJet
    (base radius : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier :=
  fun i => br2FiniteTfvdHilbertRecovery q hq0 hq1 S
    (br2CameraBracketTfvdParityJet base radius q S i)

/-- Reconstruction of the existing finite TFVD port returns exactly the
literal projective BR2 Hilbert jet, at every parity/order component. -/
theorem br2FiniteTfvdRecoveredParityJet_eq_projective
    (base radius : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (i : ℕ ⊕ ℕ) :
    br2FiniteTfvdRecoveredParityJet base radius q hqpos.le hq1 S i =
      br2CameraBracketProjectiveHilbertParityJet base radius i := by
  exact br2FiniteTfvdHilbertRecovery_parityJet
    base radius q hqpos hq1 S i

/-- Coefficient defect of the existing recovered TFVD source candidate.  It
has the desired orientation `coefficient - candidate pairing`, so a future
camera-visible realization would be characterized by its vanishing. -/
def br2FiniteTfvdRecoveredCoefficientDefect
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ)
    (i j : ℕ ⊕ ℕ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
      M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) -
    inner ℂ
      (br2FiniteTfvdRecoveredParityJet base radius q hq0 hq1 S i)
      (br2FiniteTfvdRecoveredParityJet base radius q hq0 hq1 S j)

/-- The recovered-TFVD defect is definitionally the older center-leg defect
after the exact TFVD reconstruction theorem is used.  Thus the present audit
does not create a second unresolved residual. -/
theorem br2FiniteTfvdRecoveredCoefficientDefect_eq_centerLegDefect
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ)
    (i j : ℕ ⊕ ℕ) :
    br2FiniteTfvdRecoveredCoefficientDefect
        M q hqpos.le hq1 S base radius i j =
      nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hqpos.le hq1 S base radius i j := by
  unfold br2FiniteTfvdRecoveredCoefficientDefect
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
  rw [br2FiniteTfvdRecoveredParityJet_eq_projective
    base radius q hqpos hq1 S i,
    br2FiniteTfvdRecoveredParityJet_eq_projective
      base radius q hqpos hq1 S j]

/-- The raw recovered-TFVD defect is not mysterious: it is the negative of
the pre-existing energy excess.  This identifies exactly what a genuine
camera compression would have to transfer into a blind channel. -/
theorem br2FiniteTfvdRecoveredCoefficientDefect_eq_neg_energyExcess
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ)
    (i j : ℕ ⊕ ℕ) :
    br2FiniteTfvdRecoveredCoefficientDefect
        M q hqpos.le hq1 S base radius i j =
      - nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S base radius i j := by
  unfold br2FiniteTfvdRecoveredCoefficientDefect
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
  rw [br2FiniteTfvdRecoveredParityJet_eq_projective
    base radius q hqpos hq1 S i,
    br2FiniteTfvdRecoveredParityJet_eq_projective
      base radius q hqpos hq1 S j]
  ring

/-- The recovered all-order TFVD source has the literal BR2 values in the
four diagnostic positions `(0,0)`, `(0,1)`, `(0,2)`, `(1,1)`. -/
theorem br2FiniteTfvdRecoveredParityJet_lowDegree_rawGram
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0)) = 6 ∧
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0)) = 0 ∧
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 1)) = 0 ∧
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0)) = 6 := by
  repeat' constructor
  · rw [br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inl 0)]
    change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 0) = 6
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  · rw [br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inl 0),
      br2FiniteTfvdRecoveredParityJet_eq_projective
        3 1 q hqpos hq1 S (Sum.inr 0)]
    change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 1) = 0
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  · rw [br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inl 0),
      br2FiniteTfvdRecoveredParityJet_eq_projective
        3 1 q hqpos hq1 S (Sum.inl 1)]
    change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2) = 0
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  · rw [br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inr 0)]
    change inner ℂ (br2CameraBracketVerticalState 3 1 1)
      (br2CameraBracketVerticalState 3 1 1) = 6
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num

/-- The six-source coefficient itself has the required first Hankel equality.
This uses no positivity: both sides are the same native moment `h₁`. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_lowDegree_hankel
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient M q hqpos.le hq1 S 0 2 =
      nativeC3SeededClockTfvdSixSourceCenterLegCoefficient M q hqpos.le hq1 S 1 1 := by
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
      M q hqpos hq1 S 0 2,
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
      M q hqpos hq1 S 1 1]
  norm_num [polarizedGreenMomentCoefficient,
    evenMomentDiagonalCoefficient]

/-- In contrast, the existing recovered TFVD source has the raw first Hankel
defect `-6`.  Thus the established TFVD reconstruction cannot itself be used
as the visible camera channel. -/
theorem br2FiniteTfvdRecoveredParityJet_firstHankelDefect_eq_neg_six
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 1)) -
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0)) = -6 := by
  rw [br2FiniteTfvdRecoveredParityJet_eq_projective
    3 1 q hqpos hq1 S (Sum.inl 0),
    br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inl 1),
    br2FiniteTfvdRecoveredParityJet_eq_projective
      3 1 q hqpos hq1 S (Sum.inr 0)]
  change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2) -
    inner ℂ (br2CameraBracketVerticalState 3 1 1)
      (br2CameraBracketVerticalState 3 1 1) = -6
  rw [br2C3CameraBracketVerticalState_inner,
    br2C3CameraBracketVerticalState_inner]
  norm_num

/-- The coefficient defect of the recovered TFVD source measures exactly the
missing six units in the first Hankel comparison.  It is a low-degree
certificate that the present TFVD/recovery chain remains *before* the desired
visible compression. -/
theorem br2FiniteTfvdRecoveredCoefficientDefect_firstHankelDefect_eq_six
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    br2FiniteTfvdRecoveredCoefficientDefect
        M q hqpos.le hq1 S 3 1 (Sum.inl 0) (Sum.inl 1) -
      br2FiniteTfvdRecoveredCoefficientDefect
        M q hqpos.le hq1 S 3 1 (Sum.inr 0) (Sum.inr 0) = 6 := by
  unfold br2FiniteTfvdRecoveredCoefficientDefect
  have hcoeff :=
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_lowDegree_hankel
      M q hqpos hq1 S
  change
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S 0 2 -
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inl 1)) -
      (nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S 1 1 -
      inner ℂ
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0))
        (br2FiniteTfvdRecoveredParityJet 3 1 q hqpos.le hq1 S (Sum.inr 0))) = 6
  rw [hcoeff]
  have hraw :=
    br2FiniteTfvdRecoveredParityJet_firstHankelDefect_eq_neg_six q hqpos hq1 S
  linear_combination -hraw

end

end CarrySelfAdjointOperator
