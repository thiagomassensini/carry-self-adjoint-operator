import CarrySelfAdjointOperator.CompletedNativeTfvdCameraParsevalLossChannel

/-!
# Source-channel correlation required by the camera Parseval proposal

The camera supplies a fixed quadratic form on the outer state coordinates.
This file expands the visible pairing in those coordinates, without defining
any source transport from the target coefficients.  In C3, the nonzero
zeroth/first even coefficient requires a nonzero cross-channel pairing of
transported BR2 vectors.  Pairwise orthogonality of all source channels is a
strict obstruction, even without a rank-one assumption.

Parseval then forces the blind pairing of that pair to be the negative of
the visible coefficient.  These are necessary tests of an upstream geometric
transport, not a construction of one.
-/

open scoped InnerProductSpace Matrix lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk

noncomputable section

namespace CanonicalCompletedNativeTfvdCameraParsevalTransport

variable {camera state : Type*}
variable [Fintype camera] [DecidableEq camera]
variable [Fintype state] [DecidableEq state]
variable {C : Matrix camera state ℝ}

/-- The visible Gram is the camera's fixed outer Gram applied to the
cross-channel pairings of the source transport. -/
theorem visible_inner_eq_sourceChannelGram
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (x y : CanonicalCompletedTfvdGreenHilbertCarrier) :
    inner ℂ (candidate.visibleMap x) (candidate.visibleMap y) =
      ∑ a : state, ∑ b : state,
        ((((finiteCanonicalCameraReadout C)ᵀ *
            finiteCanonicalCameraReadout C) a b : ℝ) : ℂ) *
          inner ℂ ((candidate.sourceTransport x).ofLp a)
            ((candidate.sourceTransport y).ofLp b) := by
  exact finiteHilbertMatrixSynthesis_inner_gram
    (finiteCanonicalCameraReadout C)
    (candidate.sourceTransport x) (candidate.sourceTransport y)

/-- Exact all-order form of the visible seam in upstream source coordinates.
No map or coefficient is chosen to satisfy this equality. -/
theorem realizesSixSourceVisibleCoefficient_iff_sourceChannelGram
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    candidate.RealizesSixSourceVisibleCoefficient M q hq0 hq1 S base radius ↔
      ∀ i j : ℕ ⊕ ℕ,
        nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
            M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) =
          ∑ a : state, ∑ b : state,
            ((((finiteCanonicalCameraReadout C)ᵀ *
                finiteCanonicalCameraReadout C) a b : ℝ) : ℂ) *
              inner ℂ
                ((candidate.sourceTransport
                  (br2CameraBracketProjectiveHilbertParityJet base radius i)).ofLp a)
                ((candidate.sourceTransport
                  (br2CameraBracketProjectiveHilbertParityJet base radius j)).ofLp b) := by
  unfold RealizesSixSourceVisibleCoefficient visibleParityJet
  simp_rw [candidate.visible_inner_eq_sourceChannelGram]

/-- If every source cross-channel pairing vanishes, the camera cannot create
an off-diagonal visible pairing.  This criterion does not require rank one. -/
theorem visible_inner_eq_zero_of_sourceChannelOrthogonal
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (x y : CanonicalCompletedTfvdGreenHilbertCarrier)
    (hchannels : ∀ a b : state,
      inner ℂ ((candidate.sourceTransport x).ofLp a)
        ((candidate.sourceTransport y).ofLp b) = 0) :
    inner ℂ (candidate.visibleMap x) (candidate.visibleMap y) = 0 := by
  rw [candidate.visible_inner_eq_sourceChannelGram]
  simp only [hchannels, mul_zero, Finset.sum_const_zero]

/-- C3 excludes any transport whose even-zero and even-one source channels
are mutually orthogonal.  It excludes this class, not every geometric
nonseparable transport. -/
theorem not_realizesSixSourceVisibleCoefficient_of_even01_sourceChannelOrthogonal
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (hchannels : ∀ a b : state,
      inner ℂ
        ((candidate.sourceTransport
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))).ofLp a)
        ((candidate.sourceTransport
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))).ofLp b) = 0)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ¬ candidate.RealizesSixSourceVisibleCoefficient M q hqpos.le hq1 S 3 1 := by
  intro hvisible
  have hzero := candidate.visible_inner_eq_zero_of_sourceChannelOrthogonal
    (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))
    (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1)) hchannels
  have hcoeff := hvisible (Sum.inl 0) (Sum.inl 1)
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    M q hqpos hq1 S] at hcoeff
  simp only [parityJetNumber, polarizedGreenMomentCoefficient_even_even] at hcoeff
  change (canonicalCompletedNativeLogDerivativeMoment (0 + 1) : ℂ) =
    inner ℂ (candidate.visibleMap
      (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0)))
      (candidate.visibleMap
        (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))) at hcoeff
  rw [hzero] at hcoeff
  exact canonicalCompletedNativeLogDerivativeMoment_one_ne_zero
    (Complex.ofReal_eq_zero.mp hcoeff)

/-- A realizing C3 transport must create at least one nonzero source
cross-channel pairing for even zero and even one. -/
theorem exists_even01_sourceChannel_pairing_ne_zero_of_realizes
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hvisible : candidate.RealizesSixSourceVisibleCoefficient
      M q hqpos.le hq1 S 3 1) :
    ∃ a b : state,
      inner ℂ
        ((candidate.sourceTransport
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))).ofLp a)
        ((candidate.sourceTransport
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))).ofLp b) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact candidate.not_realizesSixSourceVisibleCoefficient_of_even01_sourceChannelOrthogonal
    h M q hqpos hq1 S hvisible

/-- The required visible C3 even-zero/even-one correlation is compensated
by the opposite blind correlation.  This uses the existing Parseval split,
not a separately chosen loss map. -/
theorem blind_even01_eq_neg_nativeMoment_one_of_realizes
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hvisible : candidate.RealizesSixSourceVisibleCoefficient
      M q hqpos.le hq1 S 3 1) :
    inner ℂ (candidate.blindParityJet 3 1 (Sum.inl 0))
      (candidate.blindParityJet 3 1 (Sum.inl 1)) =
        -(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  have hsplit := candidate.gramSplit
    (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))
    (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))
  have hraw : inner ℂ
      (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))
      (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1)) = 0 := by
    change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2) = 0
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  have hcoeff := hvisible (Sum.inl 0) (Sum.inl 1)
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    M q hqpos hq1 S] at hcoeff
  simp only [parityJetNumber, polarizedGreenMomentCoefficient_even_even] at hcoeff
  change (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) =
    inner ℂ (candidate.visibleMap
      (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0)))
      (candidate.visibleMap
        (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))) at hcoeff
  rw [hraw, ← hcoeff] at hsplit
  change inner ℂ (candidate.blindMap
      (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0)))
      (candidate.blindMap
        (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1))) = _
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hsplit)

end CanonicalCompletedNativeTfvdCameraParsevalTransport

end

end CarrySelfAdjointOperator
