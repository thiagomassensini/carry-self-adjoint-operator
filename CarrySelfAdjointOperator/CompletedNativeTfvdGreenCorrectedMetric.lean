import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceBr2EnergyExcess
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Tactic

/-!
# Corrected TFVD/Green metric through an explicit loss channel

The literal C3 bracket carrier is faithful but has the wrong metric.  This
file makes the required correction directional rather than merely naming a
new Gram hypothesis.

First, the complete literal C3 bracket family is computed: every bracket has
energy `6`, and distinct brackets are orthogonal.  Consequently the
six-source excess is, in every finite order, exactly `6 I` minus the native
Hankel block (and similarly for the shifted block).

Second, a corrected metric is represented by a polarized lossless splitting
of the *existing* TFVD Hilbert carrier

`raw = corrected + loss`

at the Gram level.  The corrected map is required to be injective, so the
native incidence pivots and their all-order independence are preserved.  If
the loss channel realizes the already defined six-source energy excess, the
corrected channel realizes the native moment kernel and therefore produces
the concrete HP certificate and Stieltjes positivity.

This is not an unconditional positivity proof: constructing the geometric
loss map remains the material step.  It is, however, stronger than a renamed
center--leg premise.  It fixes the sign, the source carrier, the explicit
six-source residual, the required Pythagorean law, and the exact order-zero
calibration `6 - h₀`.  In particular, an isometric or positive-augmentation
correction cannot satisfy this interface.
-/

open scoped InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## The complete raw C3 metric -/

/-- The literal radius-one C3 brackets form a globally orthogonal family of
equal energy `6`.  This extends the former two- and three-vector calculations
to arbitrary indices. -/
theorem br2C3CameraBracketVerticalState_inner
    (i j : ℕ) :
    inner ℂ (br2CameraBracketVerticalState 3 1 i)
      (br2CameraBracketVerticalState 3 1 j) =
      if i = j then 6 else 0 := by
  simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
    lp.inner_single_left]
  simp only [alignedCenter_eq_cameraSlope_mul,
    cameraSlope_of_ne_two (by omega : (3 : ℕ) ≠ 2)]
  by_cases hij : i = j
  · subst j
    have hm0 : 3 * (i + 1) - 1 ≠ 3 * (i + 1) := by omega
    have hmP : 3 * (i + 1) - 1 ≠ 3 * (i + 1) + 1 := by omega
    have h0m : 3 * (i + 1) ≠ 3 * (i + 1) - 1 := hm0.symm
    have hPm : 3 * (i + 1) + 1 ≠ 3 * (i + 1) - 1 := hmP.symm
    simp [lp.single_apply, hm0, hmP, h0m, hPm]
    norm_num
  · have hmm : 3 * (i + 1) - 1 ≠ 3 * (j + 1) - 1 := by omega
    have hm0 : 3 * (i + 1) - 1 ≠ 3 * (j + 1) := by omega
    have hmP : 3 * (i + 1) - 1 ≠ 3 * (j + 1) + 1 := by omega
    have h0m : 3 * (i + 1) ≠ 3 * (j + 1) - 1 := by omega
    have h00 : 3 * (i + 1) ≠ 3 * (j + 1) := by omega
    have h0P : 3 * (i + 1) ≠ 3 * (j + 1) + 1 := by omega
    have hPm : 3 * (i + 1) + 1 ≠ 3 * (j + 1) - 1 := by omega
    have hP0 : 3 * (i + 1) + 1 ≠ 3 * (j + 1) := by omega
    simp [lp.single_apply, hij, hmm, hm0, hmP, h0m, h00,
      h0P, hPm, hP0]

/-- At every order, the even six-source excess is exactly `6 I` minus the
native unshifted Hankel array. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
        M q hqpos.le hq1 S N =
      fun (i j : Fin N) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ)) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ))) - _ = _
  rw [br2C3CameraBracketVerticalState_inner]
  simp only [parityJetNumber, polarizedGreenMomentCoefficient_even_even]
  by_cases hij : i = j
  · simp [hij]
  · have hnat : (i : ℕ) ≠ (j : ℕ) := by
      exact fun h => hij (Fin.ext h)
    simp [hij, hnat]

/-- At every order, the odd six-source excess is exactly `6 I` minus the
native shifted Hankel array. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_oddBlock_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
        M q hqpos.le hq1 S N =
      fun (i j : Fin N) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ) + 1) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ) + 1))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) - _ = _
  rw [br2C3CameraBracketVerticalState_inner]
  simp only [parityJetNumber, polarizedGreenMomentCoefficient_odd_odd]
  by_cases hij : i = j
  · simp [hij]
  · have hnat : (i : ℕ) ≠ (j : ℕ) := by
      exact fun h => hij (Fin.ext h)
    simp [hij, hnat]

/-- The opposite-parity excess block vanishes at every order, not merely in
the first displayed finite tests. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_crossBlock_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
        M q hqpos.le hq1 S N = 0 := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) - _ = 0
  rw [br2C3CameraBracketVerticalState_inner]
  have hne : 2 * (i : ℕ) ≠ 2 * (j : ℕ) + 1 := by omega
  simp [parityJetNumber, hne]

/-! ## A provenance-preserving corrected metric interface -/

/-- A lossless metric correction of the existing TFVD/Green carrier.

The corrected and loss outputs may live in different Hilbert carriers.  The
polarized Pythagorean identity is imposed on the original TFVD carrier, and
injectivity of the corrected output prevents collapse of any native incidence
relation. -/
structure CanonicalCompletedNativeTfvdGreenLosslessCorrection
    (E Loss : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup Loss] [InnerProductSpace ℂ Loss] where
  correctedMap : CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℝ] E
  lossMap : CanonicalCompletedTfvdGreenHilbertCarrier →ₗ[ℝ] Loss
  correctedInjective : Function.Injective correctedMap
  gramSplit : ∀ x y : CanonicalCompletedTfvdGreenHilbertCarrier,
    inner ℂ x y =
      inner ℂ (correctedMap x) (correctedMap y) +
        inner ℂ (lossMap x) (lossMap y)

namespace CanonicalCompletedNativeTfvdGreenLosslessCorrection

variable {E Loss : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup Loss] [InnerProductSpace ℂ Loss]

/-- The corrected parity jet is obtained from the faithful projective TFVD
jet without replacing its source or its incidence labels. -/
def correctedParityJet
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (base radius : ℕ) : (ℕ ⊕ ℕ) → E :=
  fun i => correction.correctedMap
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- The complementary loss jet on the same faithful TFVD source. -/
def lossParityJet
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (base radius : ℕ) : (ℕ ⊕ ℕ) → Loss :=
  fun i => correction.lossMap
    (br2CameraBracketProjectiveHilbertParityJet base radius i)

/-- Realization of the explicit six-source excess by the loss output.  This
is the remaining geometric construction target; its right side already
contains the completed TFVD/Gpre provenance and is not defined from a fitted
Gram factor. -/
def RealizesSixSourceEnergyExcess
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    inner ℂ (correction.lossParityJet base radius i)
        (correction.lossParityJet base radius j) =
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hq0 hq1 S base radius i j

/-- An injective correction automatically transports the complete native
incidence family into the corrected carrier. -/
def correctedIncidenceJetTransport
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (base radius : ℕ) :
    BR2BracketIncidenceJetTransport base radius
      (correction.correctedParityJet base radius) where
  toLinearMap := correction.correctedMap.comp
    br2CameraBracketProjectiveHilbertMap
  injective := correction.correctedInjective.comp
    br2CameraBracketProjectiveHilbertMap_injective
  even_eq n := by
    unfold correctedParityJet
    simp only [LinearMap.comp_apply]
    rw [br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]
    rfl
  odd_eq n := by
    unfold correctedParityJet
    simp only [LinearMap.comp_apply]
    rw [br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]
    rfl

/-- The Pythagorean split and the loss realization subtract exactly the
six-source excess, leaving the canonical coefficient as the corrected Gram.
This is the central metric-sewing calculation. -/
theorem sixSourceCenterLegCoefficient_eq_corrected_inner
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hq0 hq1 S base radius)
    (i j : ℕ ⊕ ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) =
      inner ℂ (correction.correctedParityJet base radius i)
        (correction.correctedParityJet base radius j) := by
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_br2Gram_sub_energyExcess]
  rw [← hloss i j]
  have hsplit := correction.gramSplit
    (br2CameraBracketProjectiveHilbertParityJet base radius i)
    (br2CameraBracketProjectiveHilbertParityJet base radius j)
  unfold correctedParityJet lossParityJet
  rw [hsplit]
  ring

/-- A geometric loss-channel realization produces the concrete real HP
carrier certificate.  Incidence independence is inherited through the
injective corrected map; the six-source tower supplies the all-order scalar
coefficient recurrence. -/
theorem toRealHPCarrierCertificate
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S base radius) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    CompletedNativeRealHPCarrierCertificate
      (correction.correctedParityJet base radius) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let incidence := canonicalParityCenterLegIncidence
    base radius hbase hradius CameraLegSide.left
  let certificate : BR2CenterLegCoefficientCertificate incidence
      canonicalCompletedNativeLogDerivativeMoment
      (correction.correctedParityJet base radius) :=
    { coeff := nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hqpos.le hq1 S
      coefficientEquation :=
        nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
          M q hqpos hq1 S
      greenOffDiagonalReadout := fun i j _ =>
        correction.sixSourceCenterLegCoefficient_eq_corrected_inner
          M q hqpos.le hq1 S base radius hloss i j }
  have hcomplex := certificate.toComplexMomentKernel
  refine
    { momentKernel := ?_
      evenIndependent :=
        (correction.correctedIncidenceJetTransport base radius).even_linearIndependent
          hbase hradius
      oddIndependent :=
        (correction.correctedIncidenceJetTransport base radius).odd_linearIndependent
          hbase hradius }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (correction.correctedParityJet base radius i)
      (correction.correctedParityJet base radius j)).re
  have h := congrArg Complex.re (hcomplex i j)
  simpa using h

/-- The same loss-channel realization closes the extensional Stieltjes gate.
No separate Hankel, Jacobi, or operator hypothesis is accepted. -/
theorem toStieltjesPositivity
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S base radius) :
    CanonicalCompletedNativeStieltjesPositivity := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  exact canonicalCompletedNativeStieltjesPositivity_of_certificate
    (correction.toRealHPCarrierCertificate
      M q hqpos hq1 S hbase hradius hloss)

/-! ## Forced order-zero calibration -/

/-- In C3 the loss output must carry exactly the missing order-zero energy
`6 - h₀`.  This is a computed calibration of the geometric loss channel. -/
theorem loss_even_zero_inner_eq_six_sub_h0
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S 3 1) :
    inner ℂ (correction.lossParityJet 3 1 (Sum.inl 0))
        (correction.lossParityJet 3 1 (Sum.inl 0)) =
      ((6 - canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by
  rw [hloss]
  exact
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_eq_six_sub_h0
      M q hqpos hq1 S

/-- Equivalently, the squared norm of the first loss vector is exactly
`6 - h₀`. -/
theorem loss_even_zero_norm_sq_eq_six_sub_h0
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S 3 1) :
    ‖correction.lossParityJet 3 1 (Sum.inl 0)‖ ^ 2 =
      6 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := correction.loss_even_zero_inner_eq_six_sub_h0
    M q hqpos hq1 S hloss
  rw [inner_self_eq_norm_sq_to_K] at h
  have hre := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using hre

/-- The corrected order-zero vector has exactly the native energy `h₀`. -/
theorem corrected_even_zero_norm_sq_eq_h0
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S 3 1) :
    ‖correction.correctedParityJet 3 1 (Sum.inl 0)‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := correction.sixSourceCenterLegCoefficient_eq_corrected_inner
    M q hqpos.le hq1 S 3 1 hloss (Sum.inl 0) (Sum.inl 0)
  change nativeC3SeededClockTfvdSixSourceTowerCoefficient
      M q hqpos.le hq1 S 0 0 = _ at h
  rw [(nativeC3SeededClockTfvdSixSourceTower_coefficientEquation
    M q hqpos hq1 S).coeff_zero_zero] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have hre := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using hre.symm

/-- Therefore every valid corrected metric strictly contracts the first
literal C3 bracket.  The correction cannot be an isometry or an orthogonal
positive augmentation of the raw carrier. -/
theorem corrected_even_zero_norm_sq_lt_raw
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S 3 1) :
    ‖correction.correctedParityJet 3 1 (Sum.inl 0)‖ ^ 2 <
      ‖br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0)‖ ^ 2 := by
  rw [correction.corrected_even_zero_norm_sq_eq_h0
    M q hqpos hq1 S hloss]
  have hraw := br2C3CameraBracketVerticalState_inner 0 0
  change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 0) = 6 at hraw
  rw [inner_self_eq_norm_sq_to_K] at hraw
  have hrawReal := congrArg Complex.re hraw
  norm_num [← Complex.ofReal_pow] at hrawReal
  have hraw' :
      ‖br2CameraBracketProjectiveHilbertParityJet 3 1 (Sum.inl 0)‖ ^ 2 = 6 := by
    simpa [br2CameraBracketProjectiveHilbertParityJet] using hrawReal
  rw [hraw']
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- The loss channel is necessarily nonzero already on the first C3 bracket.
This rules out the trivial loss output independently of higher orders. -/
theorem loss_even_zero_ne_zero
    (correction : CanonicalCompletedNativeTfvdGreenLosslessCorrection E Loss)
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hloss : correction.RealizesSixSourceEnergyExcess
      M q hqpos.le hq1 S 3 1) :
    correction.lossParityJet 3 1 (Sum.inl 0) ≠ 0 := by
  intro hzero
  have hnorm := correction.loss_even_zero_norm_sq_eq_six_sub_h0
    M q hqpos hq1 S hloss
  rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hnorm
  have hpos :=
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_scalar_pos
  linarith

end CanonicalCompletedNativeTfvdGreenLosslessCorrection

end

end CarrySelfAdjointOperator
