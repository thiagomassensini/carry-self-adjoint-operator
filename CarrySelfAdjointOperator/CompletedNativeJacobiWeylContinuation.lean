import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import CarrySelfAdjointOperator.LinearPMapPointSpectrum
import CarrySelfAdjointOperator.RealLinearPMapComplexification
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Global native continuation of the completed Jacobi Weyl readout

The local Jacobi readout is a function of `u = z^2`.  In the height
coordinate its canonical continuation is `(-F'/F)/(2z)`, with the removable
value at the center supplied by the already reconstructed even germ.

This file proves that the continuation is meromorphic on the full natural
height strip and that its simple poles are exactly the zeros of the completed
native characteristic.  It also names point-spectrum reality for the
complexification of the concrete reduced signed-height operator.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

/-- Canonical global height-coordinate continuation of the completed Jacobi
Weyl readout. -/
def completedNativeJacobiWeylHeightContinuation (z : ℂ) : ℂ :=
  if z = 0 then completedNativeLogDerivative 0
  else completedNativeOperatorLogDerivative z / ((2 : ℂ) * z)

/-- At the center, the global Weyl continuation is exactly the reduced
logarithmic-derivative germ in `u = z^2`. -/
theorem completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq :
    completedNativeJacobiWeylHeightContinuation =ᶠ[nhds 0]
      fun z => completedNativeLogDerivative (z ^ 2) := by
  filter_upwards
      [completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate]
    with z hz
  by_cases hzero : z = 0
  · subst z
    simp [completedNativeJacobiWeylHeightContinuation]
  · rw [completedNativeJacobiWeylHeightContinuation, if_neg hzero, hz]
    field_simp [hzero]

/-- The apparent singularity of the global Weyl continuation at the centered
origin is removable. -/
theorem completedNativeJacobiWeylHeightContinuation_analyticAt_zero :
    AnalyticAt ℂ completedNativeJacobiWeylHeightContinuation 0 := by
  have hsquare : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
  have houter : AnalyticAt ℂ completedNativeLogDerivative
      ((fun z : ℂ => z ^ 2) 0) := by
    simpa using completedNativeLogDerivative_analyticAt
  have hcomp := AnalyticAt.comp (f := fun z : ℂ => z ^ 2) (x := 0)
    houter hsquare
  have hcomp' : AnalyticAt ℂ
      (fun z : ℂ => completedNativeLogDerivative (z ^ 2)) 0 := by
    exact hcomp.congr (Filter.Eventually.of_forall fun _ => rfl)
  exact hcomp'.congr
    completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq.symm

/-- The canonical Weyl continuation is meromorphic at every point of the
natural centered-height strip. -/
theorem completedNativeJacobiWeylHeightContinuation_meromorphicAt
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    MeromorphicAt completedNativeJacobiWeylHeightContinuation z := by
  by_cases hzero : z = 0
  · subst z
    exact completedNativeJacobiWeylHeightContinuation_analyticAt_zero.meromorphicAt
  · have hF := completedNativeOperatorCharacteristic_analyticAt hz
    have hlog : MeromorphicAt completedNativeOperatorLogDerivative z := by
      exact hF.deriv.neg.meromorphicAt.div hF.meromorphicAt
    have hden : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by fun_prop
    have hquot : MeromorphicAt
        (fun w => completedNativeOperatorLogDerivative w / ((2 : ℂ) * w)) z :=
      hlog.div hden.meromorphicAt
    apply hquot.congr
    have hne : ∀ᶠ w : ℂ in nhds z, w ≠ 0 :=
      continuousAt_id.eventually_ne hzero
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with w hw
    simp [completedNativeJacobiWeylHeightContinuation, hw]

/-- Global meromorphicity on the natural centered-height strip. -/
theorem completedNativeJacobiWeylHeightContinuation_meromorphicOn :
    MeromorphicOn completedNativeJacobiWeylHeightContinuation
      completedNativeHeightDomain := by
  intro z hz
  exact completedNativeJacobiWeylHeightContinuation_meromorphicAt hz

/-- Away from the removable center, division by `2z` does not alter
meromorphic order. -/
theorem completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_operatorLogDerivative
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) (hzero : z ≠ 0) :
    meromorphicOrderAt completedNativeJacobiWeylHeightContinuation z =
      meromorphicOrderAt completedNativeOperatorLogDerivative z := by
  have hne : ∀ᶠ w : ℂ in nhds z, w ≠ 0 :=
    continuousAt_id.eventually_ne hzero
  have hcongr : completedNativeJacobiWeylHeightContinuation =ᶠ[𝓝[≠] z]
      fun w => completedNativeOperatorLogDerivative w / ((2 : ℂ) * w) := by
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with w hw
    simp [completedNativeJacobiWeylHeightContinuation, hw]
  rw [meromorphicOrderAt_congr hcongr]
  have hF := completedNativeOperatorCharacteristic_analyticAt hz
  have hlog : MeromorphicAt completedNativeOperatorLogDerivative z :=
    hF.deriv.neg.meromorphicAt.div hF.meromorphicAt
  have hden : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by fun_prop
  change meromorphicOrderAt
      (completedNativeOperatorLogDerivative / fun w => (2 : ℂ) * w) z = _
  rw [meromorphicOrderAt_div hlog hden.meromorphicAt,
    hden.meromorphicOrderAt_eq, hden.analyticOrderAt_eq_zero.mpr]
  · simp
  · exact mul_ne_zero (by norm_num) hzero

/-- Exact global zero--pole identification for the Jacobi Weyl continuation. -/
theorem completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    meromorphicOrderAt completedNativeJacobiWeylHeightContinuation z =
        ((-1 : ℤ) : WithTop ℤ) ↔
      completedNativeOperatorCharacteristic z = 0 := by
  by_cases hzero : z = 0
  · subst z
    constructor
    · intro horder
      have hnonneg :=
        completedNativeJacobiWeylHeightContinuation_analyticAt_zero
          |>.meromorphicOrderAt_nonneg
      rw [horder] at hnonneg
      exact ((not_le_of_gt
        (show ((-1 : ℤ) : WithTop ℤ) < 0 by exact_mod_cast
          (show (-1 : ℤ) < 0 by norm_num))) hnonneg).elim
    · intro hcharacteristic
      exact (completedNativeOperatorCharacteristic_zero_ne_zero
        hcharacteristic).elim
  · rw [
      completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_operatorLogDerivative
        hz hzero,
      completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one_iff_zero hz]

/-- At every native zero, the canonical Jacobi Weyl continuation escapes all
bounded sets in a punctured neighborhood. -/
theorem completedNativeJacobiWeylHeightContinuation_tendsto_cobounded_at_nativeZero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    Tendsto completedNativeJacobiWeylHeightContinuation
      (nhdsWithin z {z}ᶜ) (Bornology.cobounded ℂ) := by
  apply tendsto_cobounded_of_meromorphicOrderAt_neg
  rw [
    (completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
      hz).2 hzero]
  show ((-1 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
  exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The global continuation genuinely continues the concrete local Jacobi
resolvent readout in the height coordinate. -/
theorem CompletedNativeGreenWeylReducedHeightCertificate.completedNativeJacobiWeylHeightContinuation_eventually_eq_readout
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    let readout := fun u : ℝ =>
      inner ℝ (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n)
        (greenJetEvenSectorJet jet 0)
    ∀ᶠ t : ℝ in nhds 0,
      completedNativeJacobiWeylHeightContinuation (t : ℂ) =
        Complex.ofReal (readout (t ^ 2)) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  let readout := fun u : ℝ =>
    inner ℝ (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n)
      (greenJetEvenSectorJet jet 0)
  have hreadout : ∀ᶠ u : ℝ in nhds 0,
      Complex.ofReal (readout u) = completedNativeLogDerivative (u : ℂ) := by
    simpa only [jet, readout] using
      certificate.completedJacobiResolventReadout_eventually_eq_nativeLogDerivative
  have hsquare : Tendsto (fun t : ℝ => t ^ 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  have hofReal : Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := by fun_prop
    have ht := h.tendsto
    norm_num at ht
    exact ht
  filter_upwards [hsquare.eventually hreadout,
    hofReal.eventually
      completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq]
      with t htReadout htWeyl
  have hsq : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by norm_num
  rw [htWeyl, hsq, ← htReadout]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Every point eigenvalue of the concrete complexified reduced signed-height
operator is real. -/
theorem CompletedNativeGreenWeylReducedHeightCertificate.complexifiedReducedHeightOperator_eigenvalue_im_eq_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let data := certificate.toMaximalSelfAdjointReducedHeightData
    ∀ {mu : ℂ},
      LinearPMap.HasEigenvalue data.selfAdjointData.complexification mu →
        mu.im = 0 := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  let data := certificate.toMaximalSelfAdjointReducedHeightData
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  letI : CompleteSpace data.sourceSupport :=
    data.sourceSupport_isClosed.completeSpace_coe
  letI : CompleteSpace (greenJetOddHilbertSubspace jet) :=
    (greenJetOddHilbertSubspace_isClosed jet).completeSpace_coe
  intro mu hmu
  exact LinearPMap.eigenvalue_im_eq_zero_of_isSelfAdjoint
    data.selfAdjointData.complexification_isSelfAdjoint hmu

end

end CarrySelfAdjointOperator
