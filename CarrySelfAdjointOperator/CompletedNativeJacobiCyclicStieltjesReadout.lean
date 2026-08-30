import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolventAnalytic
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.Tactic

/-!
# Cyclic Stieltjes readout of the completed native Jacobi operator

The completed positive Jacobi operator already has a concrete cyclic head and
a global resolvent outside the nonnegative real axis.  This file packages its
standard cyclic readout and proves the exact Herglotz identity directly from
self-adjointness:

`Im <e₀, (J - lambda)⁻¹ e₀> = Im(lambda) * ‖(J - lambda)⁻¹ e₀‖²`.

This is the operator-theoretic half of a Stieltjes representation.  No
spectral measure, positivity hypothesis beyond the carrier certificate, or
zero of the native characteristic is introduced here.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact imaginary-part identity behind the Herglotz sign of a cyclic
resolvent readout. -/
theorem resolventReadout_im_eq
    {A : H →ₗ.[ℂ] H} (hformal : A.IsFormalAdjoint A)
    {lambda : ℂ} {source : H} (x : A.domain)
    (hequation : A x - lambda • (x : H) = source) :
    (inner ℂ source (x : H)).im =
      lambda.im * ‖(x : H)‖ ^ 2 := by
  have hreal :
      (starRingEnd ℂ) (inner ℂ (A x) (x : H)) =
        inner ℂ (A x) (x : H) := by
    calc
      (starRingEnd ℂ) (inner ℂ (A x) (x : H)) =
          (starRingEnd ℂ) (inner ℂ (x : H) (A x)) := by
        rw [hformal x x]
      _ = inner ℂ (A x) (x : H) :=
        inner_conj_symm (A x) (x : H)
  have himA : (inner ℂ (A x) (x : H)).im = 0 := by
    have him := congrArg Complex.im hreal
    rw [Complex.conj_im] at him
    linarith
  have hxre : (inner ℂ (x : H) (x : H)).re = ‖(x : H)‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x : H))
  have hxim : (inner ℂ (x : H) (x : H)).im = 0 := by
    simpa using (inner_self_im (𝕜 := ℂ) (x : H))
  rw [← hequation, inner_sub_left, inner_smul_left]
  rw [Complex.sub_im, Complex.mul_im, starRingEnd_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    hxre, hxim, himA]
  ring

/-- Polarized cyclic resolvent identity.  It realizes the divided-difference
Pick kernel of the scalar readout as the Gram kernel of the corresponding
resolvent vectors. -/
theorem resolventReadout_sub_conj_eq
    {A : H →ₗ.[ℂ] H} (hformal : A.IsFormalAdjoint A)
    {lambda mu : ℂ} {source : H} (x y : A.domain)
    (hx : A x - lambda • (x : H) = source)
    (hy : A y - mu • (y : H) = source) :
    inner ℂ source (x : H) -
        (starRingEnd ℂ) (inner ℂ source (y : H)) =
      (lambda - (starRingEnd ℂ) mu) *
        inner ℂ (y : H) (x : H) := by
  calc
    inner ℂ source (x : H) -
        (starRingEnd ℂ) (inner ℂ source (y : H)) =
      inner ℂ (A y - mu • (y : H)) (x : H) -
        inner ℂ (y : H) (A x - lambda • (x : H)) := by
          rw [hy, hx, inner_conj_symm]
    _ = (lambda - (starRingEnd ℂ) mu) *
        inner ℂ (y : H) (x : H) := by
      rw [inner_sub_left, inner_smul_left,
        inner_sub_right, inner_smul_right, hformal y x]
      ring

end LinearPMap

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance cyclicStieltjesEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- Standard spectral-parameter resolvent vector selected by the cyclic head.
It solves `(J - lambda) x = e₀`. -/
def positiveJacobiCyclicResolventVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
  certificate.positiveJacobiGlobalResolventVector hlambda
    (certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
      hlambda)
    certificate.positiveJacobiCyclicHead

/-- The standard cyclic vector satisfies its exact global graph equation. -/
theorem positiveJacobiCyclicResolventVector_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    certificate.PositiveJacobiResolventEquation lambda
      certificate.positiveJacobiCyclicHead
      (certificate.positiveJacobiCyclicResolventVector lambda hlambda) := by
  exact certificate.positiveJacobiGlobalResolventVector_equation hlambda
    (certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
      hlambda)
    certificate.positiveJacobiCyclicHead

/-- Standard cyclic Weyl/Stieltjes readout of the completed positive Jacobi
operator. -/
def positiveJacobiCyclicResolventReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout (completedJacobiOrbit jet 0)
    (certificate.positiveJacobiCyclicResolventVector lambda hlambda)

/-- The cyclic head is nonzero. -/
theorem positiveJacobiCyclicHead_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.positiveJacobiCyclicHead ≠ 0 := by
  have hm0 : 0 < canonicalCompletedNativeLogDerivativeMoment 0 := by
    have hpos := (certificate.hankelPair_posDef 1).1
    simpa [hankelGram] using
      (hpos.diag_pos (i := (0 : Fin 1)))
  have horbit : completedJacobiOrbit jet 0 ≠ 0 := by
    intro hzero
    have hnorm := certificate.completedJacobiOrbit_norm_sq_eq_canonicalMoment 0
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
    linarith
  intro hzero
  apply horbit
  have hre := congrArg RealHilbertComplexification.re hzero
  simpa [positiveJacobiCyclicHead,
    ComplexifiedOrbitResolvent.ofReal] using hre

/-- The cyclic resolvent vector cannot vanish because its source is the
nonzero cyclic head. -/
theorem positiveJacobiCyclicResolventVector_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    ((certificate.positiveJacobiCyclicResolventVector lambda hlambda :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet)) ≠ 0 := by
  intro hzero
  let x := certificate.positiveJacobiCyclicResolventVector lambda hlambda
  have hxzero : x = 0 := Subtype.ext hzero
  have hequation :=
    certificate.positiveJacobiCyclicResolventVector_equation lambda hlambda
  change certificate.PositiveJacobiResolventEquation lambda
    certificate.positiveJacobiCyclicHead x at hequation
  apply certificate.positiveJacobiCyclicHead_ne_zero
  calc
    certificate.positiveJacobiCyclicHead =
        certificate.completedJacobiEnergySelfAdjointData.complexification x -
          lambda •
            (x : RealHilbertComplexification (EvenCarrier jet)) :=
      hequation.symm
    _ = 0 := by
      rw [hxzero,
        show certificate.completedJacobiEnergySelfAdjointData.complexification
            (0 : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) =
              0 from
          LinearPMap.map_zero
            certificate.completedJacobiEnergySelfAdjointData.complexification]
      rw [show
        ((0 : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
          RealHilbertComplexification (EvenCarrier jet)) = 0 by rfl]
      module

/-- Exact Herglotz identity for the concrete cyclic Jacobi readout. -/
theorem positiveJacobiCyclicResolventReadout_im_eq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    (certificate.positiveJacobiCyclicResolventReadout lambda hlambda).im =
      lambda.im *
        ‖((certificate.positiveJacobiCyclicResolventVector lambda hlambda :
          certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
            RealHilbertComplexification (EvenCarrier jet))‖ ^ 2 := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  let A := data.complexification
  let x := certificate.positiveJacobiCyclicResolventVector lambda hlambda
  have hself : IsSelfAdjoint A :=
    data.complexification_isSelfAdjoint
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjoint
    exact hadjoint
  have hequation : A x - lambda •
      (x : RealHilbertComplexification (EvenCarrier jet)) =
        certificate.positiveJacobiCyclicHead := by
    exact certificate.positiveJacobiCyclicResolventVector_equation
      lambda hlambda
  change
    (inner ℂ certificate.positiveJacobiCyclicHead
      (x : RealHilbertComplexification (EvenCarrier jet))).im = _
  exact LinearPMap.resolventReadout_im_eq hformal x hequation

/-- The polarized Pick kernel of the concrete scalar cyclic readout is
exactly the Gram kernel of the two global resolvent vectors. -/
theorem positiveJacobiCyclicResolventReadout_sub_conj_eq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda mu : ℂ)
    (hlambda : OutsideNonnegativeRealAxis lambda)
    (hmu : OutsideNonnegativeRealAxis mu) :
    certificate.positiveJacobiCyclicResolventReadout lambda hlambda -
        (starRingEnd ℂ)
          (certificate.positiveJacobiCyclicResolventReadout mu hmu) =
      (lambda - (starRingEnd ℂ) mu) *
        inner ℂ
          ((certificate.positiveJacobiCyclicResolventVector mu hmu :
            certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
              RealHilbertComplexification (EvenCarrier jet))
          ((certificate.positiveJacobiCyclicResolventVector lambda hlambda :
            certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
              RealHilbertComplexification (EvenCarrier jet)) := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  let A := data.complexification
  let x := certificate.positiveJacobiCyclicResolventVector lambda hlambda
  let y := certificate.positiveJacobiCyclicResolventVector mu hmu
  have hself : IsSelfAdjoint A := data.complexification_isSelfAdjoint
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjoint
    exact hadjoint
  have hx : A x - lambda •
      (x : RealHilbertComplexification (EvenCarrier jet)) =
        certificate.positiveJacobiCyclicHead :=
    certificate.positiveJacobiCyclicResolventVector_equation lambda hlambda
  have hy : A y - mu •
      (y : RealHilbertComplexification (EvenCarrier jet)) =
        certificate.positiveJacobiCyclicHead :=
    certificate.positiveJacobiCyclicResolventVector_equation mu hmu
  change
    inner ℂ certificate.positiveJacobiCyclicHead
          (x : RealHilbertComplexification (EvenCarrier jet)) -
        (starRingEnd ℂ)
          (inner ℂ certificate.positiveJacobiCyclicHead
            (y : RealHilbertComplexification (EvenCarrier jet))) = _
  exact LinearPMap.resolventReadout_sub_conj_eq
    hformal x y hx hy

/-- Strict upper-half-plane Herglotz sign. -/
theorem positiveJacobiCyclicResolventReadout_im_pos
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda)
    (him : 0 < lambda.im) :
    0 < (certificate.positiveJacobiCyclicResolventReadout
      lambda hlambda).im := by
  rw [certificate.positiveJacobiCyclicResolventReadout_im_eq lambda hlambda]
  exact mul_pos him (pow_pos
    (norm_pos_iff.mpr
      (certificate.positiveJacobiCyclicResolventVector_ne_zero
        lambda hlambda)) 2)

/-- Strict lower-half-plane Herglotz sign. -/
theorem positiveJacobiCyclicResolventReadout_im_neg
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda)
    (him : lambda.im < 0) :
    (certificate.positiveJacobiCyclicResolventReadout
      lambda hlambda).im < 0 := by
  rw [certificate.positiveJacobiCyclicResolventReadout_im_eq lambda hlambda]
  exact mul_neg_of_neg_of_pos him (pow_pos
    (norm_pos_iff.mpr
      (certificate.positiveJacobiCyclicResolventVector_ne_zero
        lambda hlambda)) 2)

/-- Proof-independent ambient cyclic resolvent state.  It agrees with the
canonical graph solution outside `[0, ∞)` and is set to zero only on the
excluded spectral cut. -/
def positiveJacobiCyclicResolventStateTotal
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) : RealHilbertComplexification (EvenCarrier jet) := by
  classical
  exact if hlambda : OutsideNonnegativeRealAxis lambda then
      certificate.positiveJacobiCyclicResolventVector lambda hlambda
    else 0

/-- Proof-independent scalar cyclic resolvent readout. -/
def positiveJacobiCyclicResolventReadoutTotal
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout (completedJacobiOrbit jet 0)
    (certificate.positiveJacobiCyclicResolventStateTotal lambda)

/-- The total scalar readout agrees with the dependent graph-resolvent
readout at every point outside the nonnegative real axis. -/
theorem positiveJacobiCyclicResolventReadoutTotal_eq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    certificate.positiveJacobiCyclicResolventReadoutTotal lambda =
      certificate.positiveJacobiCyclicResolventReadout lambda hlambda := by
  classical
  simp [positiveJacobiCyclicResolventReadoutTotal,
    positiveJacobiCyclicResolventStateTotal,
    positiveJacobiCyclicResolventReadout, hlambda]

/-- The total cyclic state is analytic at every point outside the
nonnegative real axis. -/
theorem positiveJacobiCyclicResolventStateTotal_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀) :
    AnalyticAt ℂ certificate.positiveJacobiCyclicResolventStateTotal
      lambda₀ := by
  classical
  have houtside : ∀ᶠ lambda : ℂ in nhds lambda₀,
      OutsideNonnegativeRealAxis lambda := by
    rcases hlambda₀ with him | hneg
    · filter_upwards
        [Complex.continuous_im.continuousAt.eventually_ne him] with lambda h
      exact Or.inl h
    · have hopen : {lambda : ℂ | lambda.re < 0} ∈ nhds lambda₀ :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hneg
      filter_upwards [hopen] with lambda h
      exact Or.inr h
  have hlocal :=
    certificate.eventually_positiveJacobiLocalResolventState_equation
      lambda₀ hlambda₀ certificate.positiveJacobiCyclicHead
  apply (certificate.positiveJacobiLocalResolventState_analyticAt
    lambda₀ hlambda₀ certificate.positiveJacobiCyclicHead).congr
  filter_upwards [houtside, hlocal] with lambda hlambda hcandidate
  obtain ⟨x, hxState, hxEquation⟩ := hcandidate
  have hcanonical :=
    certificate.positiveJacobiCyclicResolventVector_equation lambda hlambda
  have hunique := certificate.positiveJacobiResolventEquation_unique
    hlambda hxEquation hcanonical
  rw [positiveJacobiCyclicResolventStateTotal, dif_pos hlambda,
    ← hunique]
  exact hxState.symm

/-- The total cyclic scalar readout is analytic off the nonnegative real
axis. -/
theorem positiveJacobiCyclicResolventReadoutTotal_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀) :
    AnalyticAt ℂ certificate.positiveJacobiCyclicResolventReadoutTotal
      lambda₀ := by
  have hstate :=
    certificate.positiveJacobiCyclicResolventStateTotal_analyticAt
      lambda₀ hlambda₀
  have hreadout : AnalyticAt ℂ
      (fun x : RealHilbertComplexification (EvenCarrier jet) ↦
        ComplexifiedOrbitResolvent.headReadout
          (completedJacobiOrbit jet 0) x)
      (certificate.positiveJacobiCyclicResolventStateTotal lambda₀) :=
    (ComplexifiedOrbitResolvent.headReadout
      (completedJacobiOrbit jet 0)).analyticAt _
  exact hreadout.comp (x := lambda₀) hstate

/-- The proof-independent readout is strictly Herglotz in the upper
half-plane. -/
theorem positiveJacobiCyclicResolventReadoutTotal_im_pos
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (him : 0 < lambda.im) :
    0 < (certificate.positiveJacobiCyclicResolventReadoutTotal lambda).im := by
  let hlambda : OutsideNonnegativeRealAxis lambda := Or.inl (ne_of_gt him)
  rw [certificate.positiveJacobiCyclicResolventReadoutTotal_eq lambda hlambda]
  exact certificate.positiveJacobiCyclicResolventReadout_im_pos
    lambda hlambda him

/-- The proof-independent readout has the conjugate strict sign in the lower
half-plane. -/
theorem positiveJacobiCyclicResolventReadoutTotal_im_neg
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (him : lambda.im < 0) :
    (certificate.positiveJacobiCyclicResolventReadoutTotal lambda).im < 0 := by
  let hlambda : OutsideNonnegativeRealAxis lambda := Or.inl (ne_of_lt him)
  rw [certificate.positiveJacobiCyclicResolventReadoutTotal_eq lambda hlambda]
  exact certificate.positiveJacobiCyclicResolventReadout_im_neg
    lambda hlambda him

/-- The height-coordinate resolvent is exactly the standard cyclic resolvent
after the forced reciprocal-square change of variables. -/
theorem positiveJacobiHeightGlobalResolventVector_eq_smul_cyclic
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.positiveJacobiHeightGlobalResolventVector z hz =
      -((z ^ 2)⁻¹) •
        certificate.positiveJacobiCyclicResolventVector
          ((z ^ 2)⁻¹) (inv_sq_mem_outsideNonnegativeRealAxis hz) := by
  let lambda : ℂ := (z ^ 2)⁻¹
  let hlambda : OutsideNonnegativeRealAxis lambda :=
    inv_sq_mem_outsideNonnegativeRealAxis hz
  let hglobal :=
    certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
      hlambda
  let x := certificate.positiveJacobiCyclicResolventVector lambda hlambda
  let c : ℂ := -lambda
  let scaled :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
    c • x
  have hx : certificate.PositiveJacobiResolventEquation lambda
      certificate.positiveJacobiCyclicHead x :=
    certificate.positiveJacobiCyclicResolventVector_equation lambda hlambda
  have hscaled : certificate.PositiveJacobiResolventEquation lambda
      (-(lambda • certificate.positiveJacobiCyclicHead)) scaled := by
    unfold PositiveJacobiResolventEquation at hx ⊢
    change
      certificate.completedJacobiEnergySelfAdjointData.complexification
          (c • x) -
        lambda •
          ((c • x :
            certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
              RealHilbertComplexification (EvenCarrier jet)) =
        -(lambda • certificate.positiveJacobiCyclicHead)
    rw [LinearPMap.map_smul, Submodule.coe_smul,
      smul_smul, mul_comm lambda c, ← smul_smul, ← smul_sub, hx]
    simp [c]
  have hheight : certificate.PositiveJacobiResolventEquation lambda
      (-(lambda • certificate.positiveJacobiCyclicHead))
      (certificate.positiveJacobiHeightGlobalResolventVector z hz) := by
    change certificate.PositiveJacobiResolventEquation lambda
      (-(lambda • certificate.positiveJacobiCyclicHead))
      (certificate.positiveJacobiGlobalResolventVector hlambda hglobal
        (-(lambda • certificate.positiveJacobiCyclicHead)))
    exact certificate.positiveJacobiGlobalResolventVector_equation
      hlambda hglobal
      (-(lambda • certificate.positiveJacobiCyclicHead))
  have heq := certificate.positiveJacobiResolventEquation_unique
    hlambda hheight hscaled
  change certificate.positiveJacobiHeightGlobalResolventVector z hz = scaled
  exact heq

/-- Scalar version of the reciprocal-square coordinate change:
`q(z²) = -(z²)⁻¹ m_J((z²)⁻¹)`. -/
theorem positiveJacobiHeightGlobalBoundaryReadout_eq_cyclic
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.positiveJacobiHeightGlobalBoundaryReadout z hz =
      -((z ^ 2)⁻¹) *
        certificate.positiveJacobiCyclicResolventReadout
          ((z ^ 2)⁻¹) (inv_sq_mem_outsideNonnegativeRealAxis hz) := by
  unfold positiveJacobiHeightGlobalBoundaryReadout
  rw [certificate.positiveJacobiHeightGlobalResolventVector_eq_smul_cyclic
    z hz]
  simp [positiveJacobiCyclicResolventReadout]

/-- Global native/cyclic resolvent identity off the real height axis.  This
is the exact operator form of the Stieltjes change of variables, including
the chain-rule factor `2 * z`. -/
theorem completedNativeOperatorLogDerivative_eq_cyclicStieltjesReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (hzIm : z.im ≠ 0)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeOperatorLogDerivative z =
      ((2 : ℂ) * z) *
        (-((z ^ 2)⁻¹) *
          certificate.positiveJacobiCyclicResolventReadout
            ((z ^ 2)⁻¹)
              (inv_sq_mem_outsideNonnegativeRealAxis hzIm)) := by
  have hbounds := mem_completedNativeHeightDomain_iff_im_bounds.mp hzDomain
  have hdefect : certificate.positiveJacobiWeylODEDefect z = 0 := by
    rcases lt_or_gt_of_ne hzIm with hzNeg | hzPos
    · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_lower
        (Or.inr ⟨hbounds.1, hzNeg⟩)
    · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_upper
        (Or.inr ⟨hzPos, hbounds.2⟩)
  have hreadout : certificate.positiveJacobiHeightGluedBoundaryReadout z =
      -((z ^ 2)⁻¹) *
        certificate.positiveJacobiCyclicResolventReadout
          ((z ^ 2)⁻¹) (inv_sq_mem_outsideNonnegativeRealAxis hzIm) := by
    rw [positiveJacobiHeightGluedBoundaryReadout, if_neg hzIm,
      certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal_eq z hzIm,
      certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_cyclic z hzIm]
  unfold completedNativeOperatorLogDerivative
  apply (div_eq_iff hF).2
  rw [← hreadout]
  unfold positiveJacobiWeylODEDefect at hdefect
  linear_combination -hdefect

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
