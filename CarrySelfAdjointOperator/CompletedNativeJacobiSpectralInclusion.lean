import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Tactic

/-!
# Native zeros lie in the Jacobi graph spectrum

The canonical Jacobi construction already identifies its off-axis cyclic
resolvent with the completed-native logarithmic derivative.  This module
opens a local resolvent chart at an arbitrary graph-regular parameter.  A
native zero cannot be graph-regular: otherwise the local bounded inverse
would keep the cyclic readout finite along an off-axis approach, while the
native Weyl continuation has a pole there.
-/

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace LinearPMap

noncomputable section

/-- Failure of injectivity of the graph resolvent map is exactly point
spectrum. -/
theorem hasEigenvalue_iff_not_injective_graphResolventMap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (lambda : ℂ) :
    HasEigenvalue A lambda ↔
      ¬ Function.Injective
        (CarrySelfAdjointOperator.LinearPMap.graphResolventMap A lambda) := by
  constructor
  · rintro ⟨x, hx, hAx⟩ hinjective
    let p : A.graph := ⟨((x : H), A x), A.mem_graph x⟩
    have hpzero : CarrySelfAdjointOperator.LinearPMap.graphResolventMap A lambda p =
        CarrySelfAdjointOperator.LinearPMap.graphResolventMap A lambda 0 := by
      rw [CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply,
        CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply]
      simp only [p, Submodule.coe_zero, Prod.snd_zero, Prod.fst_zero,
        smul_zero, sub_zero]
      exact sub_eq_zero.mpr hAx
    have hp : p = 0 := hinjective hpzero
    apply hx
    have hfirst := congrArg (fun q : A.graph ↦ q.1.1) hp
    simpa [p] using hfirst
  · intro hnot
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨p, q, hmap, hpq⟩ := hnot
    let r : A.graph := p - q
    have hrne : r ≠ 0 := by
      intro hr
      apply hpq
      exact sub_eq_zero.mp hr
    have hmapzero :
        CarrySelfAdjointOperator.LinearPMap.graphResolventMap A lambda r = 0 := by
      dsimp only [r]
      rw [CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply]
      rw [CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply,
        CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply] at hmap
      simp only [Submodule.coe_sub, Prod.snd_sub, Prod.fst_sub]
      rw [smul_sub]
      have hzero :
          ((p : H × H).2 - lambda • (p : H × H).1) -
              ((q : H × H).2 - lambda • (q : H × H).1) = 0 :=
        sub_eq_zero.mpr hmap
      abel_nf at hzero ⊢
      exact hzero
    obtain ⟨x, hxr, hAxr⟩ := A.mem_graph_iff.mp r.property
    refine ⟨x, ?_, ?_⟩
    · intro hxzero
      apply hrne
      apply Subtype.ext
      apply Prod.ext
      · change r.1.1 = 0
        rw [← hxr, hxzero]
      · change r.1.2 = 0
        have hxzero' : x = 0 := Subtype.ext hxzero
        rw [← hAxr, hxzero', A.map_zero]
    · rw [CarrySelfAdjointOperator.LinearPMap.graphResolventMap_apply] at hmapzero
      change r.1.2 - lambda • r.1.1 = 0 at hmapzero
      rw [← hxr, ← hAxr] at hmapzero
      exact sub_eq_zero.mp hmapzero

end

end LinearPMap

namespace CarrySelfAdjointOperator

noncomputable section

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance spectralInclusionEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- The graph resolvent of the completed positive self-adjoint Jacobi
operator is bijective at every parameter outside the nonnegative real axis. -/
theorem positiveJacobiGraphResolventMap_bijective_of_outsideNonnegativeRealAxis
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda) :
    Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda) := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  constructor
  · intro p q hpq
    by_contra hpne
    have hnotInjective : ¬ Function.Injective
        (LinearPMap.graphResolventMap A lambda) := by
      exact fun hinjective ↦ hpne (hinjective hpq)
    have heigen : LinearPMap.HasEigenvalue A lambda :=
      (LinearPMap.hasEigenvalue_iff_not_injective_graphResolventMap
        A lambda).2 hnotInjective
    have hspectrum :=
      certificate.completedJacobiEnergySelfAdjointData
        |>.complexification_eigenvalue_real_nonneg
          certificate.completedJacobiEnergyOperator_inner_nonneg heigen
    exact hlambda.elim
      (fun him ↦ him hspectrum.1)
      (fun hneg ↦ (not_lt_of_ge hspectrum.2) hneg)
  · have hglobal :=
      certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
        hlambda
    intro source
    obtain ⟨x, hx⟩ := hglobal source
    let p : A.graph := ⟨((x : A.domain), A x), A.mem_graph x⟩
    refine ⟨p, ?_⟩
    rw [LinearPMap.graphResolventMap_apply]
    change A x - lambda •
        (x : RealHilbertComplexification (EvenCarrier jet)) = source
    exact hx

/-- Continuous graph inverse at an arbitrary bijective resolvent parameter. -/
def positiveJacobiGraphResolventInverseOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀)) :
    RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
      certificate.completedJacobiEnergySelfAdjointData.complexification.graph :=
  LinearPMap.graphResolventInverseOfBijective
    certificate.completedJacobiEnergySelfAdjointData.complexification
    (certificate.completedJacobiEnergySelfAdjointData
      |>.complexification_isSelfAdjoint.isClosed)
    lambda₀ hbijective.1 hbijective.2

/-- The arbitrary-parameter graph inverse is a right inverse. -/
theorem positiveJacobiGraphResolventMap_inverseOfBijective_apply
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀))
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀
        (certificate.positiveJacobiGraphResolventInverseOfBijective
          lambda₀ hbijective source) = source := by
  exact LinearPMap.graphResolventMap_inverseOfBijective_apply
    certificate.completedJacobiEnergySelfAdjointData.complexification
    (certificate.completedJacobiEnergySelfAdjointData
      |>.complexification_isSelfAdjoint.isClosed)
    lambda₀ hbijective.1 hbijective.2 source

/-- First-coordinate resolvent operator at an arbitrary graph-regular
parameter. -/
def positiveJacobiResolventOperatorOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀)) :
    RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
      RealHilbertComplexification (EvenCarrier jet) :=
  (ContinuousLinearMap.fst ℂ
      (RealHilbertComplexification (EvenCarrier jet))
      (RealHilbertComplexification (EvenCarrier jet))).comp
    certificate.completedJacobiEnergySelfAdjointData.complexification.graph.subtypeL |>.comp
    (certificate.positiveJacobiGraphResolventInverseOfBijective
      lambda₀ hbijective)

/-- Local resolvent state around an arbitrary graph-regular parameter. -/
def positiveJacobiLocalResolventStateOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀))
    (source : RealHilbertComplexification (EvenCarrier jet))
    (lambda : ℂ) : RealHilbertComplexification (EvenCarrier jet) :=
  let R₀ := certificate.positiveJacobiResolventOperatorOfBijective
    lambda₀ hbijective
  Ring.inverse (1 - (lambda - lambda₀) • R₀) (R₀ source)

/-- The arbitrary-parameter local resolvent state is analytic at its
centre. -/
theorem positiveJacobiLocalResolventStateOfBijective_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀))
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    AnalyticAt ℂ
      (certificate.positiveJacobiLocalResolventStateOfBijective
        lambda₀ hbijective source) lambda₀ := by
  let R₀ := certificate.positiveJacobiResolventOperatorOfBijective
    lambda₀ hbijective
  let B : ℂ →
      (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) :=
    fun lambda ↦ 1 - (lambda - lambda₀) • R₀
  have hB : AnalyticAt ℂ B lambda₀ := by
    dsimp only [B]
    fun_prop
  have hBValue : B lambda₀ = 1 := by
    simp [B]
  have hinverse : AnalyticAt ℂ (fun lambda ↦ Ring.inverse (B lambda)) lambda₀ := by
    have hinverseAtValue : AnalyticAt ℂ Ring.inverse (B lambda₀) := by
      rw [hBValue]
      exact analyticAt_inverse (𝕜 := ℂ)
        (1 : (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
          RealHilbertComplexification (EvenCarrier jet))ˣ)
    exact hinverseAtValue.comp hB
  unfold positiveJacobiLocalResolventStateOfBijective
  change AnalyticAt ℂ
    (fun lambda ↦ Ring.inverse (B lambda)
      ((certificate.positiveJacobiResolventOperatorOfBijective
        lambda₀ hbijective) source)) lambda₀
  let applyMap :
      RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
          RealHilbertComplexification (EvenCarrier jet)) →L[ℂ]
            RealHilbertComplexification (EvenCarrier jet) :=
    ContinuousLinearMap.apply ℂ
      (RealHilbertComplexification (EvenCarrier jet))
  have heval := applyMap.analyticAt_bilinear
    ((certificate.positiveJacobiResolventOperatorOfBijective
      lambda₀ hbijective) source, Ring.inverse (B lambda₀))
  exact heval.comp (x := lambda₀) (analyticAt_const.prod hinverse)

/-- The bounded correction in the arbitrary local chart is eventually a
unit. -/
theorem eventually_isUnit_positiveJacobiLocalCorrectionOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀)) :
    ∀ᶠ lambda in nhds lambda₀,
      IsUnit
        (1 - (lambda - lambda₀) •
          certificate.positiveJacobiResolventOperatorOfBijective
            lambda₀ hbijective) := by
  let R₀ := certificate.positiveJacobiResolventOperatorOfBijective
    lambda₀ hbijective
  let B : ℂ →
      (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) :=
    fun lambda ↦ 1 - (lambda - lambda₀) • R₀
  have hB : ContinuousAt B lambda₀ := by
    fun_prop
  have hBValue : B lambda₀ = 1 := by
    simp [B]
  have hunit : {T | IsUnit T} ∈ nhds (B lambda₀) := by
    rw [hBValue]
    exact Units.isOpen.mem_nhds isUnit_one
  simpa only [B, R₀] using hB.eventually hunit

/-- Near an arbitrary graph-regular parameter, the local analytic formula
is represented by a domain vector satisfying the exact resolvent equation. -/
theorem eventually_positiveJacobiLocalResolventStateOfBijective_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda₀))
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    ∀ᶠ lambda in nhds lambda₀,
      ∃ x :
          certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
        (x : RealHilbertComplexification (EvenCarrier jet)) =
            certificate.positiveJacobiLocalResolventStateOfBijective
              lambda₀ hbijective source lambda ∧
          certificate.PositiveJacobiResolventEquation lambda source x := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let R₀ := certificate.positiveJacobiResolventOperatorOfBijective
    lambda₀ hbijective
  let B : ℂ →
      (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) :=
    fun lambda ↦ 1 - (lambda - lambda₀) • R₀
  filter_upwards
      [certificate.eventually_isUnit_positiveJacobiLocalCorrectionOfBijective
        lambda₀ hbijective] with lambda hunit
  let y : RealHilbertComplexification (EvenCarrier jet) :=
    Ring.inverse (B lambda) source
  let p : A.graph :=
    certificate.positiveJacobiGraphResolventInverseOfBijective
      lambda₀ hbijective y
  obtain ⟨x, hxp, hAxp⟩ := A.mem_graph_iff.mp p.property
  have hunitB : IsUnit (B lambda) := by
    simpa only [B, R₀] using hunit
  have hbase :=
    certificate.positiveJacobiGraphResolventMap_inverseOfBijective_apply
      lambda₀ hbijective y
  change LinearPMap.graphResolventMap A lambda₀ p = y at hbase
  rw [LinearPMap.graphResolventMap_apply, ← hxp, ← hAxp] at hbase
  have hR₀y : R₀ y = p.1.1 := by
    rfl
  have hcommuteUnit : Commute (hunitB.unit :
      RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) R₀ := by
    simpa only [hunitB.unit_spec] using
      (LinearPMap.one_sub_smul_commutes R₀ (lambda - lambda₀))
  have hcommute : Commute (Ring.inverse (B lambda)) R₀ := by
    rw [← hunitB.unit_spec, Ring.inverse_unit]
    exact hcommuteUnit.units_inv_left
  have hcommuteApply :
      Ring.inverse (B lambda) (R₀ source) =
        R₀ (Ring.inverse (B lambda) source) := by
    have h := congrArg
      (fun T : RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet) ↦ T source)
      hcommute.eq
    simpa using h
  refine ⟨x, ?_, ?_⟩
  · calc
      (x : RealHilbertComplexification (EvenCarrier jet)) = p.1.1 := hxp
      _ = R₀ y := hR₀y.symm
      _ = R₀ (Ring.inverse (B lambda) source) := rfl
      _ = Ring.inverse (B lambda) (R₀ source) := hcommuteApply.symm
      _ = certificate.positiveJacobiLocalResolventStateOfBijective
          lambda₀ hbijective source lambda := by
        rfl
  · unfold PositiveJacobiResolventEquation
    change A x - lambda •
        (x : RealHilbertComplexification (EvenCarrier jet)) = source
    calc
      A x - lambda •
          (x : RealHilbertComplexification (EvenCarrier jet)) =
          (A x - lambda₀ •
            (x : RealHilbertComplexification (EvenCarrier jet))) -
            (lambda - lambda₀) •
              (x : RealHilbertComplexification (EvenCarrier jet)) := by
        module
      _ = y - (lambda - lambda₀) • (R₀ y) := by
        rw [hbase, hxp, ← hR₀y]
      _ = B lambda y := by
        simp [B]
      _ = B lambda (Ring.inverse (B lambda) source) := rfl
      _ = source := by
        have hinverse : B lambda * Ring.inverse (B lambda) = 1 :=
          Ring.mul_inverse_cancel (B lambda) hunitB
        have happ := congrArg
          (fun T : RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
            RealHilbertComplexification (EvenCarrier jet) ↦ T source)
          hinverse
        simpa using happ

/-- Height-coordinate local resolvent obtained from a graph-regular
reciprocal-square parameter. -/
def positiveJacobiLocalHeightResolventStateOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (_hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹))
    (z : ℂ) : RealHilbertComplexification (EvenCarrier jet) :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let localState :=
    certificate.positiveJacobiLocalResolventStateOfBijective
      lambda₀ hbijective certificate.positiveJacobiCyclicHead ((z ^ 2)⁻¹)
  SMul.smul (-((z ^ 2)⁻¹)) localState

/-- A graph-regular reciprocal-square parameter gives a full analytic
height-resolvent state at the corresponding nonzero height. -/
theorem positiveJacobiLocalHeightResolventStateOfBijective_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹)) :
    AnalyticAt ℂ
      (certificate.positiveJacobiLocalHeightResolventStateOfBijective
        z₀ hz₀ hbijective) z₀ := by
  have hlambda : AnalyticAt ℂ (fun z : ℂ ↦ (z ^ 2)⁻¹) z₀ := by
    have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) z₀ := by
      fun_prop
    exact hsquare.fun_inv (pow_ne_zero 2 hz₀)
  have hstate :=
    certificate.positiveJacobiLocalResolventStateOfBijective_analyticAt
      ((z₀ ^ 2)⁻¹) hbijective certificate.positiveJacobiCyclicHead
  have hcomp := hstate.comp (x := z₀) hlambda
  have hscalar : AnalyticAt ℂ (fun z : ℂ ↦ -((z ^ 2)⁻¹)) z₀ :=
    hlambda.neg
  change AnalyticAt ℂ
    (fun z : ℂ ↦ -((z ^ 2)⁻¹) •
      certificate.positiveJacobiLocalResolventStateOfBijective
        ((z₀ ^ 2)⁻¹) hbijective certificate.positiveJacobiCyclicHead
        ((z ^ 2)⁻¹)) z₀
  exact (hscalar.smul hcomp).congr
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Near a graph-regular height, the local analytic state is represented by
a domain vector satisfying the canonical equation `x - z² A x = e₀`. -/
theorem eventually_positiveJacobiLocalHeightResolventStateOfBijective_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹)) :
    ∀ᶠ z in nhds z₀,
      ∃ x :
          certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
        (x : RealHilbertComplexification (EvenCarrier jet)) =
            certificate.positiveJacobiLocalHeightResolventStateOfBijective
              z₀ hz₀ hbijective z ∧
          certificate.PositiveJacobiHeightResolventEquation z
            certificate.positiveJacobiCyclicHead x := by
  let lambda : ℂ → ℂ := fun z ↦ (z ^ 2)⁻¹
  have hlambdaContinuous : Tendsto lambda (nhds z₀) (nhds (lambda z₀)) := by
    have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) z₀ := by
      fun_prop
    exact (hsquare.fun_inv (pow_ne_zero 2 hz₀)).continuousAt
  have hequation := hlambdaContinuous.eventually
    (certificate.eventually_positiveJacobiLocalResolventStateOfBijective_equation
      (lambda z₀) hbijective certificate.positiveJacobiCyclicHead)
  have hzne : ∀ᶠ z : ℂ in nhds z₀, z ≠ 0 :=
    continuousAt_id.eventually_ne hz₀
  filter_upwards [hequation, hzne] with z hlocal hz
  obtain ⟨x, hxState, hxEquation⟩ := hlocal
  let c : ℂ := -(lambda z)
  let scaled :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
    c • x
  have hscaledEquation : certificate.PositiveJacobiResolventEquation
      (lambda z) (c • certificate.positiveJacobiCyclicHead) scaled := by
    unfold PositiveJacobiResolventEquation at hxEquation ⊢
    change
      certificate.completedJacobiEnergySelfAdjointData.complexification
          (c • x) -
        lambda z •
          ((c • x :
            certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
              RealHilbertComplexification (EvenCarrier jet)) =
        c • certificate.positiveJacobiCyclicHead
    rw [LinearPMap.map_smul]
    rw [Submodule.coe_smul, smul_smul, mul_comm (lambda z) c,
      ← smul_smul, ← smul_sub]
    exact congrArg (fun v ↦ c • v) hxEquation
  refine ⟨scaled, ?_, ?_⟩
  · change c • (x : RealHilbertComplexification (EvenCarrier jet)) = _
    rw [hxState]
    simp only [positiveJacobiLocalHeightResolventStateOfBijective,
      lambda, c]
    rfl
  · apply (certificate.positiveJacobiHeightResolventEquation_iff
      hz certificate.positiveJacobiCyclicHead scaled).2
    have hsource :
        c • certificate.positiveJacobiCyclicHead =
          -((lambda z) • certificate.positiveJacobiCyclicHead) := by
      exact neg_smul (lambda z) certificate.positiveJacobiCyclicHead
    rw [← hsource]
    exact hscaledEquation

/-- The local analytic chart agrees with the existing global off-axis
resolvent wherever the latter is defined. -/
theorem positiveJacobiLocalHeightResolventStateOfBijective_eq_global_eventually
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹)) :
    ∀ᶠ z in nhds z₀,
      z.im ≠ 0 →
        certificate.positiveJacobiLocalHeightResolventStateOfBijective
            z₀ hz₀ hbijective z =
          certificate.positiveJacobiHeightGlobalResolventState z := by
  filter_upwards
      [certificate.eventually_positiveJacobiLocalHeightResolventStateOfBijective_equation
        z₀ hz₀ hbijective] with z hcandidate
  intro hz
  obtain ⟨x, hxState, hxEquation⟩ := hcandidate
  have hunique := certificate.positiveJacobiHeightGlobalResolventVector_unique
    z hz x hxEquation
  rw [positiveJacobiHeightGlobalResolventState, dif_pos hz, ← hunique]
  exact hxState.symm

/-- Cyclic readout of the arbitrary graph-regular local height chart. -/
def positiveJacobiLocalHeightBoundaryReadoutOfBijective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹))
    (z : ℂ) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout (completedJacobiOrbit jet 0)
    (certificate.positiveJacobiLocalHeightResolventStateOfBijective
      z₀ hz₀ hbijective z)

/-- A graph-regular height has a finite analytic cyclic readout. -/
theorem positiveJacobiLocalHeightBoundaryReadoutOfBijective_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hbijective : Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹)) :
    AnalyticAt ℂ
      (certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
        z₀ hz₀ hbijective) z₀ := by
  exact
    (ComplexifiedOrbitResolvent.headReadout (completedJacobiOrbit jet 0)).analyticAt
      (certificate.positiveJacobiLocalHeightResolventStateOfBijective
        z₀ hz₀ hbijective z₀) |>.comp
      (certificate.positiveJacobiLocalHeightResolventStateOfBijective_analyticAt
        z₀ hz₀ hbijective)

/-- Explicit off-axis approach to an arbitrary height. -/
def positiveJacobiUpperApproach (z₀ : ℂ) (n : ℕ) : ℂ :=
  z₀ + Complex.I * (((n : ℝ) + 1)⁻¹ : ℂ)

/-- The explicit upper approach converges to its base height. -/
theorem positiveJacobiUpperApproach_tendsto (z₀ : ℂ) :
    Tendsto (positiveJacobiUpperApproach z₀) atTop (nhds z₀) := by
  have hcomplex : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1)⁻¹)
      atTop (nhds 0) :=
    by simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  change Tendsto (fun n : ℕ ↦ z₀ + Complex.I * ((n : ℂ) + 1)⁻¹)
    atTop (nhds z₀)
  have hz₀Tendsto : Tendsto (fun _ : ℕ ↦ z₀) atTop (nhds z₀) :=
    tendsto_const_nhds
  have hITendsto : Tendsto (fun _ : ℕ ↦ Complex.I) atTop
      (nhds Complex.I) := tendsto_const_nhds
  convert hz₀Tendsto.add (hITendsto.mul hcomplex) using 1
  all_goals simp

@[simp] theorem positiveJacobiUpperApproach_im_eq
    (z₀ : ℂ) (n : ℕ) :
    (positiveJacobiUpperApproach z₀ n).im =
      z₀.im + ((n : ℝ) + 1)⁻¹ := by
  unfold positiveJacobiUpperApproach
  rw [Complex.add_im, Complex.mul_im]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  rw [Complex.inv_re]
  norm_num [Complex.normSq]

@[simp] theorem positiveJacobiUpperApproach_im
    {z₀ : ℂ} (hz₀ : z₀.im = 0) (n : ℕ) :
    (positiveJacobiUpperApproach z₀ n).im = ((n : ℝ) + 1)⁻¹ := by
  rw [positiveJacobiUpperApproach_im_eq, hz₀, zero_add]

/-- Every point of the upper approach has positive imaginary part when the
base height is real. -/
theorem positiveJacobiUpperApproach_im_pos
    {z₀ : ℂ} (hz₀ : z₀.im = 0) (n : ℕ) :
    0 < (positiveJacobiUpperApproach z₀ n).im := by
  rw [positiveJacobiUpperApproach_im hz₀]
  positivity

/-- The upper approach never meets its base point. -/
theorem positiveJacobiUpperApproach_ne
    (z₀ : ℂ) (n : ℕ) :
    positiveJacobiUpperApproach z₀ n ≠ z₀ := by
  intro h
  have him := congrArg Complex.im h
  rw [positiveJacobiUpperApproach_im_eq] at him
  have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

/-- A completed-native zero is a graph-spectral point of the canonical
positive Jacobi operator: the graph defect map cannot be bijective at the
reciprocal-square parameter.

This is the unconditional zero-to-spectrum implication relative only to the
carrier certificate that constructs the operator.  It does not promote the
spectral point to an eigenvalue; that later promotion requires a discrete or
vector-meromorphic resolvent theorem. -/
theorem completedNativeOperator_zero_not_bijective_graphResolventMap
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    ¬ Function.Bijective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹) := by
  intro hbijective
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  let path : ℕ → ℂ := positiveJacobiUpperApproach z₀
  have hpath : Tendsto path atTop (nhds z₀) :=
    positiveJacobiUpperApproach_tendsto z₀
  have hpathNe : ∀ n : ℕ, path n ≠ z₀ := by
    intro n
    exact positiveJacobiUpperApproach_ne z₀ n
  have hpathPunctured :
      Tendsto path atTop (nhdsWithin z₀ {z₀}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hpath, Filter.Eventually.of_forall (fun n ↦ by simpa using hpathNe n)⟩
  have hF := completedNativeOperatorCharacteristic_analyticAt hzDomain
  have hFne : ∀ᶠ w : ℂ in nhdsWithin z₀ {z₀}ᶜ,
      completedNativeOperatorCharacteristic w ≠ 0 :=
    hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
  have hFpath : ∀ᶠ n : ℕ in atTop,
      completedNativeOperatorCharacteristic (path n) ≠ 0 :=
    hpathPunctured.eventually hFne
  have hbounds :=
    mem_completedNativeHeightDomain_iff_im_bounds.mp hzDomain
  have hinvTendsto : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
      atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpathCone : ∀ᶠ n : ℕ in atTop,
      (0 < (path n).im ∧ (path n).im < (1 : ℝ) / 2) ∨
      (-((1 : ℝ) / 2) < (path n).im ∧ (path n).im < 0) := by
    by_cases hz₀Neg : z₀.im < 0
    · have hgap : 0 < -z₀.im := neg_pos.mpr hz₀Neg
      have hsmall : ∀ᶠ n : ℕ in atTop,
          ((n : ℝ) + 1)⁻¹ < -z₀.im :=
        hinvTendsto.eventually (Iio_mem_nhds hgap)
      filter_upwards [hsmall] with n hn
      right
      rw [show (path n).im = z₀.im + ((n : ℝ) + 1)⁻¹ by
        exact positiveJacobiUpperApproach_im_eq z₀ n]
      have hinvPos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      constructor <;> linarith [hbounds.1]
    · have hz₀Nonneg : 0 ≤ z₀.im := le_of_not_gt hz₀Neg
      have hgap : 0 < (1 : ℝ) / 2 - z₀.im := sub_pos.mpr hbounds.2
      have hsmall : ∀ᶠ n : ℕ in atTop,
          ((n : ℝ) + 1)⁻¹ < (1 : ℝ) / 2 - z₀.im :=
        hinvTendsto.eventually (Iio_mem_nhds hgap)
      filter_upwards [hsmall] with n hn
      left
      rw [show (path n).im = z₀.im + ((n : ℝ) + 1)⁻¹ by
        exact positiveJacobiUpperApproach_im_eq z₀ n]
      have hinvPos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      constructor <;> linarith
  have hlocalEq :=
    hpath.eventually
      (certificate.positiveJacobiLocalHeightResolventStateOfBijective_eq_global_eventually
        z₀ hz₀ne hbijective)
  have hlocalAnalytic :=
    certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective_analyticAt
      z₀ hz₀ne hbijective
  have hlocalTendsto : Tendsto
      (fun n ↦ certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
        z₀ hz₀ne hbijective (path n)) atTop
      (nhds (certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
        z₀ hz₀ne hbijective z₀)) :=
    hlocalAnalytic.continuousAt.tendsto.comp hpath
  have hreadoutEq : ∀ᶠ n : ℕ in atTop,
      certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
          z₀ hz₀ne hbijective (path n) =
        completedNativeJacobiWeylHeightContinuation (path n) := by
    filter_upwards [hlocalEq, hFpath, hpathCone] with n hstate hFn hnCone
    have hnIm : (path n).im ≠ 0 := by
      rcases hnCone with hnUpper | hnLower
      · exact ne_of_gt hnUpper.1
      · exact ne_of_lt hnLower.2
    have hnNe : path n ≠ 0 := by
      intro hnZero
      have him := congrArg Complex.im hnZero
      exact hnIm (by simpa using him)
    have hdefect : certificate.positiveJacobiWeylODEDefect (path n) = 0 := by
      rcases hnCone with hnUpper | hnLower
      · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_upper
          (Or.inr hnUpper)
      · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_lower
          (Or.inr hnLower)
    unfold positiveJacobiWeylODEDefect at hdefect
    unfold positiveJacobiHeightGluedBoundaryReadout at hdefect
    rw [if_neg hnIm] at hdefect
    change
      ((2 : ℂ) * path n) *
            certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal (path n) *
            completedNativeOperatorCharacteristic (path n) +
          deriv completedNativeOperatorCharacteristic (path n) = 0 at hdefect
    have hlog : completedNativeOperatorLogDerivative (path n) =
        ((2 : ℂ) * path n) *
          certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal
            (path n) := by
      unfold completedNativeOperatorLogDerivative
      apply (div_eq_iff hFn).2
      linear_combination -hdefect
    have hlocalGlobal :
        certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
            z₀ hz₀ne hbijective (path n) =
          certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal
            (path n) := by
      unfold positiveJacobiLocalHeightBoundaryReadoutOfBijective
        positiveJacobiHeightGlobalBoundaryReadoutTotal
      rw [hstate hnIm]
    rw [completedNativeJacobiWeylHeightContinuation, if_neg hnNe, hlog]
    rw [hlocalGlobal]
    field_simp [hnNe]
  have hweylCobounded : Tendsto
      (fun n ↦ completedNativeJacobiWeylHeightContinuation (path n))
      atTop (Bornology.cobounded ℂ) :=
    (completedNativeJacobiWeylHeightContinuation_tendsto_cobounded_at_nativeZero
      hzDomain hzero).comp hpathPunctured
  have hlocalCobounded : Tendsto
      (fun n ↦ certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
        z₀ hz₀ne hbijective (path n))
      atTop (Bornology.cobounded ℂ) :=
    hweylCobounded.congr'
      (hreadoutEq.mono fun _ h ↦ h.symm)
  have hnormFinite := hlocalTendsto.norm
  have hnormInfinite : Tendsto
      (fun n ↦ ‖certificate.positiveJacobiLocalHeightBoundaryReadoutOfBijective
        z₀ hz₀ne hbijective (path n)‖) atTop atTop := by
    rwa [tendsto_norm_atTop_iff_cobounded]
  exact (not_tendsto_atTop_of_tendsto_nhds hnormFinite) hnormInfinite

/-- Hilbert--Polya confinement in spectral order: a native zero first enters
the graph spectrum, and positivity plus self-adjointness then force its
reciprocal-square parameter onto the nonnegative real axis. -/
theorem completedNativeOperator_zero_im_eq_zero_of_jacobiSpectralInclusion
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    z₀.im = 0 := by
  by_contra hz₀Im
  have houtside : OutsideNonnegativeRealAxis (z₀ ^ 2)⁻¹ :=
    inv_sq_mem_outsideNonnegativeRealAxis hz₀Im
  exact certificate.completedNativeOperator_zero_not_bijective_graphResolventMap
    hzDomain hzero
    (certificate.positiveJacobiGraphResolventMap_bijective_of_outsideNonnegativeRealAxis
      houtside)

/-- Exact point/continuous-spectrum dichotomy at every native zero.  Failure
of injectivity is already an eigenvalue; otherwise the only possible
obstruction is failure of surjectivity. -/
theorem completedNativeOperator_zero_hasEigenvalue_or_not_surjective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹ ∨
      ¬ Function.Surjective
        (LinearPMap.graphResolventMap
          certificate.completedJacobiEnergySelfAdjointData.complexification
          (z₀ ^ 2)⁻¹) := by
  have hnot :=
    certificate.completedNativeOperator_zero_not_bijective_graphResolventMap
      hzDomain hzero
  by_cases hinjective : Function.Injective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹)
  · exact Or.inr (fun hsurjective ↦ hnot ⟨hinjective, hsurjective⟩)
  · exact Or.inl
      ((LinearPMap.hasEigenvalue_iff_not_injective_graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        (z₀ ^ 2)⁻¹).2 hinjective)

/-- Purely momental specialization of the native zero-to-spectrum theorem. -/
theorem completedNativeOperator_zero_not_bijective_stieltjesGraphResolventMap
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    ¬ Function.Bijective
      (LinearPMap.graphResolventMap
        (canonicalCompletedNativeStieltjesJacobiEnergySelfAdjointData hpos).complexification
        (z₀ ^ 2)⁻¹) := by
  exact
    (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
      |>.completedNativeOperator_zero_not_bijective_graphResolventMap
        hzDomain hzero

/-- Purely momental specialization of the spectral Hilbert--Polya
confinement route. -/
theorem completedNativeOperator_zero_im_eq_zero_of_stieltjesSpectralInclusion
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    z₀.im = 0 := by
  exact
    (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
      |>.completedNativeOperator_zero_im_eq_zero_of_jacobiSpectralInclusion
        hzDomain hzero

end CompletedNativeRealHPCarrierCertificate

end


end CarrySelfAdjointOperator
