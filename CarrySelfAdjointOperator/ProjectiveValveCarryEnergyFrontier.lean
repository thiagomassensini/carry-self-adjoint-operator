import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import CarrySelfAdjointOperator.BR2CausalGreenResponseTransport
import CarryGeometry.Universality

/-!
# Derived carry amplitude in the projective Green moment route

The Green ratio is exactly the positional carry amplitude at depth one, and
its powers recover the derived amplitude at every depth. The Green kernel
therefore carries `r * carryAmplitude base r`. The full TFVD energy includes
the causal response, the boundary return and both cross terms.

The source-to-response projective realization is injective at the canonical
carry ratio. Its moment equation remains an explicit obligation; the raw
unweighted C3 obstruction is not asserted for this different metric.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera
open scoped InnerProductSpace

noncomputable section

/-- The actual Green ratio comes from the foundational carry amplitude. -/
theorem canonicalBR2CarryAmplitudeRatio_eq_carryAmplitude (base : ℕ) :
    canonicalBR2CarryAmplitudeRatio base = CarryGeometry.carryAmplitude base 1 := by
  unfold canonicalBR2CarryAmplitudeRatio primeCarryAmplitudeRatio
    CarryGeometry.carryAmplitude
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : 0 ≤ (base : ℝ))]
  congr 1
  norm_num

/-- Every power of the actual Green ratio has the native depth amplitude. -/
theorem canonicalBR2CarryAmplitudeRatio_pow_eq_carryAmplitude (base k : ℕ) :
    canonicalBR2CarryAmplitudeRatio base ^ k = CarryGeometry.carryAmplitude base k := by
  rw [canonicalBR2CarryAmplitudeRatio_eq_carryAmplitude]
  unfold CarryGeometry.carryAmplitude
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (base : ℝ))]
  congr 1
  push_cast
  ring

/-- The amplitude used by Green reproduces the derived positional mass. -/
theorem canonicalBR2CarryAmplitudeRatio_pow_sq_eq_carryMass (base k : ℕ) :
    (canonicalBR2CarryAmplitudeRatio base ^ k) ^ 2 = CarryGeometry.carryMass base k := by
  rw [canonicalBR2CarryAmplitudeRatio_pow_eq_carryAmplitude,
    CarryGeometry.carryAmplitude_sq_eq_carryMass]

/-- The actual causal Green kernel contains exactly the derived depth weight. -/
theorem canonicalCarryGreenKernel_eq_depthAmplitude (base r : ℕ) :
    carryWeightedVerticalGreenKernel (canonicalBR2CarryAmplitudeRatio base) r =
      (r : ℝ) * CarryGeometry.carryAmplitude base r := by
  rw [carryWeightedVerticalGreenKernel,
    canonicalBR2CarryAmplitudeRatio_pow_eq_carryAmplitude]

/-- Its quadratic weight is the Green multiplicity squared times carry mass. -/
theorem canonicalCarryGreenKernel_sq_eq_depthMass (base r : ℕ) :
    (carryWeightedVerticalGreenKernel (canonicalBR2CarryAmplitudeRatio base) r) ^ 2 =
      (r : ℝ) ^ 2 * CarryGeometry.carryMass base r := by
  rw [canonicalCarryGreenKernel_eq_depthAmplitude, mul_pow,
    CarryGeometry.carryAmplitude_sq_eq_carryMass]

/-- The full reconstructed Hilbert pairing contains all four causal/boundary
blocks at the ratio forced by the positional geometry. -/
theorem canonicalCarryTfvd_inner_eq_fourChannel
    {base : ℕ} (hbase : IsSupported base) (x y : CarryVerticalL2) :
    let q := canonicalBR2CarryAmplitudeRatio base
    let Gx := carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q x)
    let Gy := carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q y)
    let Rx := carryWeightedVerticalReturn q
      (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) (carryWeightedVerticalTrace q x)
    let Ry := carryWeightedVerticalReturn q
      (canonicalBR2CarryAmplitudeRatio_pos hbase).le
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) (carryWeightedVerticalTrace q y)
    inner ℂ x y = inner ℂ Gx Gy + inner ℂ Gx Ry + inner ℂ Rx Gy + inner ℂ Rx Ry := by
  dsimp only
  have hx : carryVerticalL2WeightedGreen (canonicalBR2CarryAmplitudeRatio base)
        (carryWeightedVerticalCenteredBracket (canonicalBR2CarryAmplitudeRatio base) x) +
      carryWeightedVerticalReturn (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
        (carryWeightedVerticalTrace (canonicalBR2CarryAmplitudeRatio base) x) = x := by
    ext n
    exact carryWeightedVerticalTfvd_apply _
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) x n
  have hy : carryVerticalL2WeightedGreen (canonicalBR2CarryAmplitudeRatio base)
        (carryWeightedVerticalCenteredBracket (canonicalBR2CarryAmplitudeRatio base) y) +
      carryWeightedVerticalReturn (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
        (carryWeightedVerticalTrace (canonicalBR2CarryAmplitudeRatio base) y) = y := by
    ext n
    exact carryWeightedVerticalTfvd_apply _
      (canonicalBR2CarryAmplitudeRatio_pos hbase)
      (canonicalBR2CarryAmplitudeRatio_lt_one hbase) y n
  calc
    _ = inner ℂ _ _ := congrArg₂ (inner ℂ) hx.symm hy.symm
    _ = _ := by simp only [inner_add_left, inner_add_right]; ring

namespace ProjectiveValve

/-- Realize the projective core through the existing boundary-completed
causal Green map, with the ratio fixed by carry geometry. -/
def canonicalProjectiveCarryGreenMap (base : ℕ) :
    LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] CanonicalCompletedTfvdGreenHilbertCarrier :=
  (br2CameraBracketCausalGreenResponseMap (canonicalBR2CarryAmplitudeRatio base)).comp
    nativeIncidenceProjectiveEquivRange.symm.toLinearMap

/-- Weighted Green retains the full incidence information. -/
theorem canonicalProjectiveCarryGreenMap_injective
    {base : ℕ} (hbase : IsSupported base) :
    Function.Injective (canonicalProjectiveCarryGreenMap base) :=
  (br2CameraBracketCausalGreenResponseMap_injective _
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)).comp
      nativeIncidenceProjectiveEquivRange.symm.injective

/-- The projective path yields the actual carry-weighted causal response.
Its two initial causal seeds are those of the pre-existing response model. -/
theorem projectiveIncidenceRawJet_canonicalCarryGreen
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (n : ℕ) :
    projectiveIncidenceRawJet (canonicalProjectiveCarryGreenMap base) base radius n =
      br2CameraBracketCausalGreenResponse (canonicalBR2CarryAmplitudeRatio base) base radius n := by
  change br2CameraBracketCausalGreenResponseMap (canonicalBR2CarryAmplitudeRatio base)
    (nativeIncidenceProjectiveEquivRange.symm
      (nativeIncidenceProjectiveEquivRange (cameraBracketIncidence base radius n))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence _ hbase hradius n

/-- For this weighted realization all incidence and injectivity premises are
already discharged. The native moment equation is the remaining input. -/
theorem realHPCarrierCertificate_of_canonicalCarryGreenMomentEquation
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hmoment : ProjectiveIncidenceMomentEquation canonicalCompletedNativeLogDerivativeMoment
      (canonicalProjectiveCarryGreenMap base) base radius) :
    letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
      InnerProductSpace.rclikeToReal ℂ CanonicalCompletedTfvdGreenHilbertCarrier
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet
        (projectiveIncidenceRawJet (canonicalProjectiveCarryGreenMap base) base radius)) :=
  realHPCarrierCertificate_of_projectiveMomentEquation _
    (canonicalProjectiveCarryGreenMap_injective hbase) hbase hradius hmoment

end ProjectiveValve

end
end CarrySelfAdjointOperator
