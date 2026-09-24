import CarrySelfAdjointOperator.CompletedNativeTfvdGreenCorrectedMetric
import CarrySelfAdjointOperator.EnrichedMovingCameraCompletedNaimarkCrosswalk
import CarrySelfAdjointOperator.CompletedNativeTaylorResidualNoGo
import Mathlib.Tactic

/-!
# Finite-camera Parseval realization of the corrected/loss interface

The historical finite camera already has the algebra required by the
corrected TFVD/Green metric:

`<R X, R Y> + <B X, B Y> = <X,Y>`.

This file isolates the exact additional transport needed before that identity
can be applied to the literal BR2 bracket family.  A candidate consists of an
isometric transport `U` from the common completed vertical carrier into one
finite camera state family.  The visible and blind maps are then not new
objects: they are literally `R ∘ U` and `B ∘ U`.

For such a candidate, the blind Gram differs from the already defined
six-source BR2 energy excess by exactly one term: the visible-coefficient
defect.  Thus

`blindGram = energyExcess + (sixSourceCoefficient - visibleGram)`.

Consequently the desired visible identification and the desired blind/loss
identification are equivalent.  This is the promised identity-first
reduction: Parseval supplies the upper-frame inequality automatically once
the one remaining visible seam is proved.

The visible readout need not be injective on the whole finite state carrier.
For the HP certificate it is enough to retain a BR2 incidence transport on
the visible parity jet.  This is strictly weaker, and is the correct interface
for an orthogonal camera compression.
-/

open scoped InnerProductSpace Matrix lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarryC3Crosswalk

noncomputable section

/-- A carrier-honest transport of the completed vertical state into a finite
camera state family.  The camera matrix itself supplies the visible/blind
split; the only metric input here is that `U` preserves the source pairing. -/
structure CanonicalCompletedNativeTfvdCameraParsevalTransport
    {camera state : Type*}
    [Fintype camera] [DecidableEq camera]
    [Fintype state] [DecidableEq state]
    (C : Matrix camera state ℝ) where
  sourceTransport :
    CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℂ]
      FiniteHilbertFamily state CanonicalCompletedTfvdGreenHilbertCarrier
  rowGramPosDef : (finiteCameraRowGram C).PosDef
  sourceTransport_inner : ∀ x y : CanonicalCompletedTfvdGreenHilbertCarrier,
    inner ℂ (sourceTransport x) (sourceTransport y) = inner ℂ x y

namespace CanonicalCompletedNativeTfvdCameraParsevalTransport

variable {camera state : Type*}
variable [Fintype camera] [DecidableEq camera]
variable [Fintype state] [DecidableEq state]
variable {C : Matrix camera state ℝ}

/-- The candidate corrected channel is exactly the canonical whitened camera
readout after the supplied source transport. -/
def visibleMap
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C) :
    CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℂ]
      FiniteHilbertFamily camera CanonicalCompletedTfvdGreenHilbertCarrier :=
  (finiteCanonicalCameraHilbertReadout C).comp candidate.sourceTransport

/-- The candidate loss channel is exactly the historical blind projection
after the same source transport. -/
def blindMap
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C) :
    CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℂ]
      FiniteHilbertFamily state CanonicalCompletedTfvdGreenHilbertCarrier :=
  (finiteHilbertMatrixSynthesis
    (finiteCanonicalCameraBlindProjection C)).comp candidate.sourceTransport

/-- The visible image of the literal BR2 parity jet. -/
def visibleParityJet
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (base radius : ℕ) :
    (ℕ ⊕ ℕ) →
      FiniteHilbertFamily camera CanonicalCompletedTfvdGreenHilbertCarrier :=
  fun i => candidate.visibleMap
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- The blind image of the same literal BR2 parity jet. -/
def blindParityJet
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (base radius : ℕ) :
    (ℕ ⊕ ℕ) →
      FiniteHilbertFamily state CanonicalCompletedTfvdGreenHilbertCarrier :=
  fun i => candidate.blindMap
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- The historical finite camera gives the required polarized lossless split
after any pairing-preserving source transport. -/
theorem gramSplit
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (x y : CanonicalCompletedTfvdGreenHilbertCarrier) :
    inner ℂ (candidate.visibleMap x) (candidate.visibleMap y) +
        inner ℂ (candidate.blindMap x) (candidate.blindMap y) =
      inner ℂ x y := by
  have h := finiteCanonicalEnrichedCameraHilbert_parseval
    C candidate.rowGramPosDef
      (candidate.sourceTransport x) (candidate.sourceTransport y)
  rw [candidate.sourceTransport_inner x y] at h
  exact h

/-- The only remaining scalar seam for the camera proposal: the synthesized
six-source coefficient minus the Gram seen by the visible channel. -/
def visibleCoefficientDefect
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) : ℂ :=
  nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
      M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) -
    inner ℂ (candidate.visibleParityJet base radius i)
      (candidate.visibleParityJet base radius j)

/-- Exact defect formula.  No positivity estimate occurs: it is just the
finite-camera Parseval identity with the already fixed orientation
`energyExcess = rawGram - sixSourceCoefficient`. -/
theorem blind_inner_eq_energyExcess_add_visibleCoefficientDefect
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) :
    inner ℂ (candidate.blindParityJet base radius i)
        (candidate.blindParityJet base radius j) =
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
          M q hq0 hq1 S base radius i j +
        candidate.visibleCoefficientDefect
          M q hq0 hq1 S base radius i j := by
  have hsplit := candidate.gramSplit
    (br2CameraBracketProjectiveHilbertParityJet base radius i)
    (br2CameraBracketProjectiveHilbertParityJet base radius j)
  simp only [blindParityJet] at hsplit ⊢
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    visibleCoefficientDefect
  simp only [visibleParityJet]
  linear_combination hsplit

/-- The intended visible identification with the completed six-source
coefficient, stated without any positivity or injectivity premise. -/
def RealizesSixSourceVisibleCoefficient
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) =
      inner ℂ (candidate.visibleParityJet base radius i)
        (candidate.visibleParityJet base radius j)

/-- The equivalent blind-channel formulation of the same seam. -/
def RealizesSixSourceEnergyExcess
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    inner ℂ (candidate.blindParityJet base radius i)
        (candidate.blindParityJet base radius j) =
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hq0 hq1 S base radius i j

/-- For a transported historical camera, proving the visible moment Gram and
proving that the blind channel is the loss Gram are literally the same
obligation. -/
theorem realizesSixSourceVisibleCoefficient_iff_energyExcess
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) :
    candidate.RealizesSixSourceVisibleCoefficient
        M q hq0 hq1 S base radius ↔
      candidate.RealizesSixSourceEnergyExcess
        M q hq0 hq1 S base radius := by
  constructor
  · intro hvisible i j
    rw [candidate.blind_inner_eq_energyExcess_add_visibleCoefficientDefect
      M q hq0 hq1 S base radius i j]
    unfold visibleCoefficientDefect
    rw [hvisible i j]
    ring
  · intro hblind i j
    have hdefect := candidate.blind_inner_eq_energyExcess_add_visibleCoefficientDefect
      M q hq0 hq1 S base radius i j
    rw [hblind i j] at hdefect
    have hzero : candidate.visibleCoefficientDefect
        M q hq0 hq1 S base radius i j = 0 := by
      exact add_eq_left.mp hdefect.symm
    exact sub_eq_zero.mp hzero

/-! ## A necessary nonseparability test for the source transport -/

/-- A fixed outer camera profile tensored with one vertical Hilbert state.
This is the most direct way of inserting the source into a finite family, but
it cannot create new pairings between orthogonal BR2 brackets. -/
def finiteHilbertRankOneSourceState
    (amplitude : state → ℂ)
    (x : CanonicalCompletedTfvdGreenHilbertCarrier) :
    FiniteHilbertFamily state CanonicalCompletedTfvdGreenHilbertCarrier :=
  WithLp.toLp 2 (fun k => amplitude k • x)

omit [Fintype state] [DecidableEq state] in
@[simp] theorem finiteHilbertRankOneSourceState_apply
    (amplitude : state → ℂ)
    (x : CanonicalCompletedTfvdGreenHilbertCarrier) (k : state) :
    (finiteHilbertRankOneSourceState amplitude x).ofLp k =
      amplitude k • x :=
  rfl

omit [DecidableEq state] in
/-- A finite real camera acting on a fixed outer profile cannot turn two
orthogonal vertical states into nonorthogonal visible states. -/
theorem finiteCanonicalCameraHilbertReadout_rankOne_inner_eq_zero
    (amplitude : state → ℂ)
    (x y : CanonicalCompletedTfvdGreenHilbertCarrier)
    (hxy : inner ℂ x y = 0) :
    inner ℂ
        (finiteCanonicalCameraHilbertReadout C
          (finiteHilbertRankOneSourceState amplitude x))
        (finiteCanonicalCameraHilbertReadout C
          (finiteHilbertRankOneSourceState amplitude y)) = 0 := by
  change inner ℂ
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C)
        (finiteHilbertRankOneSourceState amplitude x))
      (finiteHilbertMatrixSynthesis (finiteCanonicalCameraReadout C)
        (finiteHilbertRankOneSourceState amplitude y)) = 0
  rw [finiteHilbertMatrixSynthesis_inner_gram]
  simp only [finiteHilbertRankOneSourceState_apply,
    inner_smul_left, inner_smul_right, hxy]
  simp

/-- If `U` merely tensors every vertical state with one fixed camera profile,
the visible BR2 `(0,2)` pairing remains zero.  The desired six-source entry is
`h₁`, which is unconditionally nonzero, so no such separable transport can
realize the corrected moment channel. -/
theorem not_realizesSixSourceVisibleCoefficient_of_rankOneSourceTransport
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (amplitude : state → ℂ)
    (hsource : ∀ x : CanonicalCompletedTfvdGreenHilbertCarrier,
      candidate.sourceTransport x =
        finiteHilbertRankOneSourceState amplitude x)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ¬ candidate.RealizesSixSourceVisibleCoefficient
        M q hqpos.le hq1 S 3 1 := by
  intro hvisible
  have hraw :
      inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 1)) = 0 := by
    change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 2) = 0
    rw [br2C3CameraBracketVerticalState_inner]
    norm_num
  have hvisibleZero :
      inner ℂ (candidate.visibleParityJet 3 1 (Sum.inl 0))
        (candidate.visibleParityJet 3 1 (Sum.inl 1)) = 0 := by
    unfold visibleParityJet visibleMap
    simp only [LinearMap.comp_apply, hsource]
    exact finiteCanonicalCameraHilbertReadout_rankOne_inner_eq_zero
      amplitude _ _ hraw
  have hcoeff := hvisible (Sum.inl 0) (Sum.inl 1)
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    M q hqpos hq1 S] at hcoeff
  simp only [parityJetNumber,
    polarizedGreenMomentCoefficient_even_even] at hcoeff
  rw [hvisibleZero] at hcoeff
  exact canonicalCompletedNativeLogDerivativeMoment_one_ne_zero
    (Complex.ofReal_eq_zero.mp hcoeff)

/-- The faithfulness condition actually needed downstream.  It asks only for
the BR2 incidence ledger to remain injective in the visible parity jet; the
readout may have a blind kernel elsewhere. -/
def HasVisibleIncidenceTransport
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (base radius : ℕ) : Prop :=
  Nonempty (BR2BracketIncidenceJetTransport base radius
    (candidate.visibleParityJet base radius))

/-- A visible camera realization plus incidence faithfulness yields the real
HP carrier certificate.  No global injectivity of the readout is required. -/
theorem toRealHPCarrierCertificate
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hvisible : candidate.RealizesSixSourceVisibleCoefficient
      M q hqpos.le hq1 S base radius)
    (htransport : candidate.HasVisibleIncidenceTransport base radius) :
    letI : InnerProductSpace ℝ
        (FiniteHilbertFamily camera CanonicalCompletedTfvdGreenHilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    CompletedNativeRealHPCarrierCertificate
      (candidate.visibleParityJet base radius) := by
  letI : InnerProductSpace ℝ
      (FiniteHilbertFamily camera CanonicalCompletedTfvdGreenHilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  let incidence := canonicalParityCenterLegIncidence
    base radius hbase hradius CameraLegSide.left
  let certificate : BR2CenterLegCoefficientCertificate incidence
      canonicalCompletedNativeLogDerivativeMoment
      (candidate.visibleParityJet base radius) :=
    { coeff := nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S
      coefficientEquation :=
        nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
          M q hqpos hq1 S
      greenOffDiagonalReadout := fun i j _ => hvisible i j }
  have hcomplex := certificate.toComplexMomentKernel
  rcases htransport with ⟨transport⟩
  refine
    { momentKernel := ?_
      evenIndependent := transport.even_linearIndependent hbase hradius
      oddIndependent := transport.odd_linearIndependent hbase hradius }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (candidate.visibleParityJet base radius i)
      (candidate.visibleParityJet base radius j)).re
  have h := congrArg Complex.re (hcomplex i j)
  simpa using h

/-- The same two concrete camera seams close the extensional Stieltjes gate. -/
theorem toStieltjesPositivity
    (candidate : CanonicalCompletedNativeTfvdCameraParsevalTransport C)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hvisible : candidate.RealizesSixSourceVisibleCoefficient
      M q hqpos.le hq1 S base radius)
    (htransport : candidate.HasVisibleIncidenceTransport base radius) :
    CanonicalCompletedNativeStieltjesPositivity := by
  letI : InnerProductSpace ℝ
      (FiniteHilbertFamily camera CanonicalCompletedTfvdGreenHilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact canonicalCompletedNativeStieltjesPositivity_of_certificate
    (candidate.toRealHPCarrierCertificate M q hqpos hq1 S
      hbase hradius hvisible htransport)

end CanonicalCompletedNativeTfvdCameraParsevalTransport

end

end CarrySelfAdjointOperator
