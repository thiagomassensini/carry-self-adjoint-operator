import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolvent
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# Analytic local charts of the global positive Jacobi resolvent

The positive Jacobi operator and its global resolvent set were constructed in
`CompletedNativePositiveJacobiResolvent`.  This file does not introduce a new
operator.  It upgrades the bijective closed-graph defect map at one resolvent
point to a continuous linear equivalence and uses the usual local resolvent
identity to obtain analytic graph-valued charts.
-/

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The affine resolvent correction is a polynomial in the fixed bounded
resolvent, hence commutes with it. -/
theorem one_sub_smul_commutes
    (R : H →L[ℂ] H) (d : ℂ) :
    Commute (1 - d • R) R := by
  change (1 - d • R) * R = R * (1 - d • R)
  ext x
  simp

variable [CompleteSpace H]

/-- Continuous inverse of a bijective resolvent defect map on the closed
graph of a partial operator. -/
def graphResolventInverseOfBijective
    (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) (lambda : ℂ)
    (hinjective : Function.Injective (graphResolventMap A lambda))
    (hsurjective : Function.Surjective (graphResolventMap A lambda)) :
    H →L[ℂ] A.graph := by
  letI : CompleteSpace A.graph := hA.completeSpace_coe
  let f : A.graph →L[ℂ] H := graphResolventMap A lambda
  have hclosed : IsClosed (Set.range f) := by
    rw [Set.range_eq_univ.mpr hsurjective]
    exact isClosed_univ
  let rangeLiftLinear : H →ₗ[ℂ] f.range :=
    { toFun := fun y ↦ ⟨y, hsurjective y⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let rangeLift : H →L[ℂ] f.range :=
    LinearMap.mkContinuous rangeLiftLinear 1 (by
      intro x
      simp [rangeLiftLinear])
  exact
    (ContinuousLinearMap.leftInverse_of_injective_of_isClosed_range
      f hinjective hclosed).comp rangeLift

/-- The continuous inverse is a right inverse on every ambient source. -/
theorem graphResolventMap_inverseOfBijective_apply
    (A : H →ₗ.[ℂ] H) (hA : A.IsClosed) (lambda : ℂ)
    (hinjective : Function.Injective (graphResolventMap A lambda))
    (hsurjective : Function.Surjective (graphResolventMap A lambda))
    (source : H) :
    graphResolventMap A lambda
        (graphResolventInverseOfBijective
          A hA lambda hinjective hsurjective source) = source := by
  let f : A.graph →L[ℂ] H := graphResolventMap A lambda
  obtain ⟨p, hp⟩ := hsurjective source
  subst source
  change f (graphResolventInverseOfBijective
    A hA lambda hinjective hsurjective (f p)) = f p
  congr 1
  unfold graphResolventInverseOfBijective
  dsimp only
  exact f.rangeRestrict.leftInverse_apply_of_inj
    (by
      rw [ContinuousLinearMap.ker_codRestrict]
      exact LinearMap.ker_eq_bot.mpr hinjective) p

end LinearPMap

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance positiveJacobiAnalyticEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- The graph defect map of the existing Jacobi operator is injective at
every point outside the nonnegative real axis. -/
theorem positiveJacobiGraphResolventMap_injective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda) :
    Function.Injective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda) := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  intro p q hpq
  obtain ⟨x, hxp, hAxp⟩ := A.mem_graph_iff.mp p.property
  obtain ⟨y, hyq, hAyq⟩ := A.mem_graph_iff.mp q.property
  have hxEquation : certificate.PositiveJacobiResolventEquation lambda
      (LinearPMap.graphResolventMap A lambda p) x := by
    unfold PositiveJacobiResolventEquation
    rw [LinearPMap.graphResolventMap_apply, ← hxp, ← hAxp]
  have hyEquation : certificate.PositiveJacobiResolventEquation lambda
      (LinearPMap.graphResolventMap A lambda p) y := by
    unfold PositiveJacobiResolventEquation
    calc
      A y - lambda • (y : RealHilbertComplexification (EvenCarrier jet)) =
          LinearPMap.graphResolventMap A lambda q := by
        rw [LinearPMap.graphResolventMap_apply, ← hyq, ← hAyq]
      _ = LinearPMap.graphResolventMap A lambda p := hpq.symm
  have hxy : x = y :=
    certificate.positiveJacobiResolventEquation_unique
      hlambda hxEquation hyEquation
  subst y
  apply Subtype.ext
  apply Prod.ext
  · exact hxp.symm.trans hyq
  · exact hAxp.symm.trans hAyq

/-- The graph defect map of the existing Jacobi operator is onto at every
point outside the nonnegative real axis. -/
theorem positiveJacobiGraphResolventMap_surjective
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda) :
    Function.Surjective
      (LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda) := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  intro source
  obtain ⟨x, hx⟩ :=
    certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
      hlambda source
  refine ⟨⟨((x : RealHilbertComplexification (EvenCarrier jet)), A x),
    A.mem_graph x⟩, ?_⟩
  simpa [LinearPMap.graphResolventMap_apply,
    PositiveJacobiResolventEquation] using hx

/-- Continuous inverse of the graph defect map at one global resolvent point.
Its construction uses the closed-range inverse already supplied by the Banach
open mapping theorem. -/
def positiveJacobiGraphResolventInverse
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
      certificate.completedJacobiEnergySelfAdjointData.complexification.graph :=
  LinearPMap.graphResolventInverseOfBijective
    certificate.completedJacobiEnergySelfAdjointData.complexification
    (certificate.completedJacobiEnergySelfAdjointData
      |>.complexification_isSelfAdjoint.isClosed)
    lambda
    (certificate.positiveJacobiGraphResolventMap_injective hlambda)
    (certificate.positiveJacobiGraphResolventMap_surjective hlambda)

/-- The continuous graph inverse is a genuine right inverse of the defect
map. -/
theorem positiveJacobiGraphResolventMap_inverse_apply
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    LinearPMap.graphResolventMap
        certificate.completedJacobiEnergySelfAdjointData.complexification
        lambda
        (certificate.positiveJacobiGraphResolventInverse
          lambda hlambda source) = source := by
  exact LinearPMap.graphResolventMap_inverseOfBijective_apply
    certificate.completedJacobiEnergySelfAdjointData.complexification
    (certificate.completedJacobiEnergySelfAdjointData
      |>.complexification_isSelfAdjoint.isClosed)
    lambda
    (certificate.positiveJacobiGraphResolventMap_injective hlambda)
    (certificate.positiveJacobiGraphResolventMap_surjective hlambda)
    source

/-- Ambient first-coordinate resolvent at one standard spectral parameter. -/
def positiveJacobiResolventOperator
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : OutsideNonnegativeRealAxis lambda) :
    RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
      RealHilbertComplexification (EvenCarrier jet) :=
  (ContinuousLinearMap.fst ℂ
      (RealHilbertComplexification (EvenCarrier jet))
      (RealHilbertComplexification (EvenCarrier jet))).comp
    certificate.completedJacobiEnergySelfAdjointData.complexification.graph.subtypeL |>.comp
    (certificate.positiveJacobiGraphResolventInverse lambda hlambda)

/-- Local ambient resolvent state around a fixed standard resolvent point.

Writing `R₀ = (A - lambda₀)\u207b¹`, the local resolvent identity is
`(A - lambda)\u207b¹ = (1 - (lambda - lambda₀) R₀)\u207b¹ R₀`.  The
right-hand side is formed entirely in the bounded-operator algebra. -/
def positiveJacobiLocalResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀)
    (source : RealHilbertComplexification (EvenCarrier jet))
    (lambda : ℂ) :
    RealHilbertComplexification (EvenCarrier jet) :=
  let R₀ := certificate.positiveJacobiResolventOperator lambda₀ hlambda₀
  Ring.inverse (1 - (lambda - lambda₀) • R₀) (R₀ source)

/-- The local ambient resolvent state is analytic at its centre. -/
theorem positiveJacobiLocalResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    AnalyticAt ℂ
      (certificate.positiveJacobiLocalResolventState
        lambda₀ hlambda₀ source) lambda₀ := by
  let R₀ := certificate.positiveJacobiResolventOperator lambda₀ hlambda₀
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
  unfold positiveJacobiLocalResolventState
  change AnalyticAt ℂ
    (fun lambda ↦ Ring.inverse (B lambda)
      ((certificate.positiveJacobiResolventOperator lambda₀ hlambda₀) source))
      lambda₀
  let applyMap :
      RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
          RealHilbertComplexification (EvenCarrier jet)) →L[ℂ]
            RealHilbertComplexification (EvenCarrier jet) :=
    ContinuousLinearMap.apply ℂ
      (RealHilbertComplexification (EvenCarrier jet))
  have heval := applyMap.analyticAt_bilinear
    ((certificate.positiveJacobiResolventOperator lambda₀ hlambda₀) source,
      Ring.inverse (B lambda₀))
  exact heval.comp (x := lambda₀) (analyticAt_const.prod hinverse)

/-- Near the centre of a local chart, its bounded correction operator is a
unit.  This is the exact neighborhood on which `Ring.inverse` is the genuine
operator inverse. -/
theorem eventually_isUnit_positiveJacobiLocalCorrection
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀) :
    ∀ᶠ lambda in nhds lambda₀,
      IsUnit
        (1 - (lambda - lambda₀) •
          certificate.positiveJacobiResolventOperator lambda₀ hlambda₀) := by
  let R₀ := certificate.positiveJacobiResolventOperator lambda₀ hlambda₀
  let B : ℂ →
      (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) :=
    fun lambda ↦ 1 - (lambda - lambda₀) • R₀
  have hB : ContinuousAt B lambda₀ := by
    fun_prop
  have hBValue : B lambda₀ = 1 := by
    simp [B]
  have hunit : {T |
      IsUnit T} ∈ nhds (B lambda₀) := by
    rw [hBValue]
    exact Units.isOpen.mem_nhds isUnit_one
  simpa only [B, R₀] using hB.eventually hunit

/-- The analytic local formula is, near its centre, represented by a vector
in the domain of the same Jacobi operator and satisfies its exact resolvent
equation.  No continuation carrier is introduced. -/
theorem eventually_positiveJacobiLocalResolventState_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : OutsideNonnegativeRealAxis lambda₀)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    ∀ᶠ lambda in nhds lambda₀,
      ∃ x :
          certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
        (x : RealHilbertComplexification (EvenCarrier jet)) =
            certificate.positiveJacobiLocalResolventState
              lambda₀ hlambda₀ source lambda ∧
          certificate.PositiveJacobiResolventEquation lambda source x := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let R₀ := certificate.positiveJacobiResolventOperator lambda₀ hlambda₀
  let B : ℂ →
      (RealHilbertComplexification (EvenCarrier jet) →L[ℂ]
        RealHilbertComplexification (EvenCarrier jet)) :=
    fun lambda ↦ 1 - (lambda - lambda₀) • R₀
  filter_upwards
      [certificate.eventually_isUnit_positiveJacobiLocalCorrection
        lambda₀ hlambda₀] with lambda hunit
  let y : RealHilbertComplexification (EvenCarrier jet) :=
    Ring.inverse (B lambda) source
  let p : A.graph :=
    certificate.positiveJacobiGraphResolventInverse
      lambda₀ hlambda₀ y
  obtain ⟨x, hxp, hAxp⟩ := A.mem_graph_iff.mp p.property
  have hunitB : IsUnit (B lambda) := by
    simpa only [B, R₀] using hunit
  have hbase := certificate.positiveJacobiGraphResolventMap_inverse_apply
    lambda₀ hlambda₀ y
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
      _ = certificate.positiveJacobiLocalResolventState
          lambda₀ hlambda₀ source lambda := by
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

/-- Local height-coordinate state obtained from the standard resolvent chart
by the exact substitution `lambda = (z²)⁻¹` and source
`-lambda * e₀`. -/
def positiveJacobiLocalHeightResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0)
    (z : ℂ) : RealHilbertComplexification (EvenCarrier jet) :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let localState := positiveJacobiLocalResolventState certificate
    lambda₀ (inv_sq_mem_outsideNonnegativeRealAxis hz₀)
    (positiveJacobiCyclicHead certificate) ((z ^ 2)⁻¹)
  SMul.smul (-((z ^ 2)⁻¹)) localState

/-- The local height-coordinate resolvent state is analytic at every
off-axis centre. -/
theorem positiveJacobiLocalHeightResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ
      (certificate.positiveJacobiLocalHeightResolventState z₀ hz₀) z₀ := by
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    subst z₀
    exact hz₀ rfl
  have hlambda : AnalyticAt ℂ (fun z : ℂ ↦ (z ^ 2)⁻¹) z₀ := by
    have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) z₀ := by
      fun_prop
    exact hsquare.fun_inv (pow_ne_zero 2 hz₀ne)
  have hstate := certificate.positiveJacobiLocalResolventState_analyticAt
    ((z₀ ^ 2)⁻¹) (inv_sq_mem_outsideNonnegativeRealAxis hz₀)
    certificate.positiveJacobiCyclicHead
  have hcomp := hstate.comp (x := z₀) hlambda
  have hscalar : AnalyticAt ℂ (fun z : ℂ ↦ -((z ^ 2)⁻¹)) z₀ := by
    exact hlambda.neg
  change AnalyticAt ℂ
    (fun z : ℂ ↦ -((z ^ 2)⁻¹) •
      certificate.positiveJacobiLocalResolventState
        ((z₀ ^ 2)⁻¹) (inv_sq_mem_outsideNonnegativeRealAxis hz₀)
        certificate.positiveJacobiCyclicHead ((z ^ 2)⁻¹)) z₀
  exact (hscalar.smul hcomp).congr
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Near an off-axis centre, the local height state is represented by a
domain vector satisfying `x - z² A x = e₀`. -/
theorem eventually_positiveJacobiLocalHeightResolventState_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    ∀ᶠ z in nhds z₀,
      ∃ x :
          certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
        (x : RealHilbertComplexification (EvenCarrier jet)) =
            certificate.positiveJacobiLocalHeightResolventState z₀ hz₀ z ∧
          certificate.PositiveJacobiHeightResolventEquation z
            certificate.positiveJacobiCyclicHead x := by
  let lambda : ℂ → ℂ := fun z ↦ (z ^ 2)⁻¹
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    subst z₀
    exact hz₀ rfl
  have hlambdaContinuous : Tendsto lambda (nhds z₀) (nhds (lambda z₀)) := by
    have hsquare : AnalyticAt ℂ (fun z : ℂ ↦ z ^ 2) z₀ := by
      fun_prop
    exact (hsquare.fun_inv (pow_ne_zero 2 hz₀ne)).continuousAt
  have hequation := hlambdaContinuous.eventually
    (certificate.eventually_positiveJacobiLocalResolventState_equation
      (lambda z₀) (inv_sq_mem_outsideNonnegativeRealAxis hz₀)
      certificate.positiveJacobiCyclicHead)
  have hzne : ∀ᶠ z : ℂ in nhds z₀, z ≠ 0 :=
    continuousAt_id.eventually_ne hz₀ne
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
    rfl
  · apply (certificate.positiveJacobiHeightResolventEquation_iff
      hz certificate.positiveJacobiCyclicHead scaled).2
    have hsource :
        c • certificate.positiveJacobiCyclicHead =
          -((lambda z) • certificate.positiveJacobiCyclicHead) := by
      exact neg_smul (lambda z) certificate.positiveJacobiCyclicHead
    rw [← hsource]
    exact hscaledEquation

/-- Total ambient state of the global height resolvent, extended by zero on
the real axis only to avoid carrying a proof argument in analytic statements. -/
def positiveJacobiHeightGlobalResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) : RealHilbertComplexification (EvenCarrier jet) :=
  if hz : z.im ≠ 0 then
    certificate.positiveJacobiHeightGlobalResolventVector z hz
  else 0

/-- Resolvent uniqueness identifies each local analytic chart with the
global ambient state at every off-axis centre. -/
theorem positiveJacobiHeightGlobalResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ certificate.positiveJacobiHeightGlobalResolventState z₀ := by
  have him : ∀ᶠ z : ℂ in nhds z₀, z.im ≠ 0 := by
    exact (Complex.continuous_im.continuousAt.eventually_ne hz₀)
  have hlocal :=
    certificate.eventually_positiveJacobiLocalHeightResolventState_equation
      z₀ hz₀
  apply (certificate.positiveJacobiLocalHeightResolventState_analyticAt
    z₀ hz₀).congr
  filter_upwards [him, hlocal] with z hz hcandidate
  obtain ⟨x, hxState, hxEquation⟩ := hcandidate
  have hunique := certificate.positiveJacobiHeightGlobalResolventVector_unique
    z hz x hxEquation
  rw [positiveJacobiHeightGlobalResolventState, dif_pos hz, ← hunique]
  exact hxState.symm

/-- Proof-independent cyclic-head readout of the global off-axis resolvent
state. -/
def positiveJacobiHeightGlobalBoundaryReadoutTotal
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout (completedJacobiOrbit jet 0)
    (certificate.positiveJacobiHeightGlobalResolventState z)

/-- The proof-independent readout agrees with the original dependent global
readout at every off-axis height. -/
theorem positiveJacobiHeightGlobalBoundaryReadoutTotal_eq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal z =
      certificate.positiveJacobiHeightGlobalBoundaryReadout z hz := by
  simp [positiveJacobiHeightGlobalBoundaryReadoutTotal,
    positiveJacobiHeightGlobalResolventState,
    positiveJacobiHeightGlobalBoundaryReadout, hz]

/-- The global cyclic readout is analytic at every off-axis height. -/
theorem positiveJacobiHeightGlobalBoundaryReadoutTotal_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ
      certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal z₀ := by
  have hstate :=
    certificate.positiveJacobiHeightGlobalResolventState_analyticAt z₀ hz₀
  let head := ComplexifiedOrbitResolvent.ofReal
    (completedJacobiOrbit jet 0)
  have hinner : AnalyticAt ℂ
      (fun x : RealHilbertComplexification (EvenCarrier jet) ↦
        inner ℂ head x)
      (certificate.positiveJacobiHeightGlobalResolventState z₀) := by
    exact (ComplexifiedOrbitResolvent.headReadout
      (completedJacobiOrbit jet 0)).analyticAt _
  have hcomp := hinner.comp (x := z₀) hstate
  exact hcomp.congr (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- On off-axis points near the Taylor centre, the global resolvent readout
is exactly the already-constructed Jacobi/Weyl germ.  This is the first
scalar consequence of the vector uniqueness theorem. -/
theorem positiveJacobiHeightGlobalBoundaryReadoutTotal_eventuallyEq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal =ᶠ[
      nhdsWithin 0 {z : ℂ | z.im ≠ 0}]
      completedNativeJacobiWeylHeightContinuation := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let germ := certificate.completedJacobiComplexGraphResolvent_heightGerm
  filter_upwards
      [germ.eventually_mem_graph.filter_mono nhdsWithin_le_nhds,
        germ.eventually_resolventEquation.filter_mono nhdsWithin_le_nhds,
        germ.eventually_readout_eq.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hzGraph hzEquation hzReadout hz
  obtain ⟨x, hxFirst, hxSecond⟩ := A.mem_graph_iff.mp hzGraph
  have hxHeight : certificate.PositiveJacobiHeightResolventEquation z
      certificate.positiveJacobiCyclicHead x := by
    unfold PositiveJacobiHeightResolventEquation
    change (x : RealHilbertComplexification (EvenCarrier jet)) -
      z ^ 2 • A x = certificate.positiveJacobiCyclicHead
    rw [hxFirst, hxSecond]
    exact hzEquation
  have hunique := certificate.positiveJacobiHeightGlobalResolventVector_unique
    z hz x hxHeight
  calc
    certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal z =
        ComplexifiedOrbitResolvent.headReadout
          (completedJacobiOrbit jet 0) x := by
      rw [positiveJacobiHeightGlobalBoundaryReadoutTotal,
        positiveJacobiHeightGlobalResolventState, dif_pos hz, ← hunique]
    _ = germ.readout (germ.graphResolvent z) := by
      rw [hxFirst]
      rfl
    _ = completedNativeJacobiWeylHeightContinuation z := hzReadout

/-- Scalar readout glued to the already-constructed centre germ on the real
axis.  Off the axis it is the global resolvent readout. -/
def positiveJacobiHeightGluedBoundaryReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) : ℂ :=
  if z.im = 0 then completedNativeJacobiWeylHeightContinuation z
  else certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal z

/-- The glued readout is exactly the Weyl germ in a full neighborhood of the
Taylor centre. -/
theorem positiveJacobiHeightGluedBoundaryReadout_eventuallyEq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.positiveJacobiHeightGluedBoundaryReadout =ᶠ[nhds 0]
      completedNativeJacobiWeylHeightContinuation := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let germ := certificate.completedJacobiComplexGraphResolvent_heightGerm
  filter_upwards [germ.eventually_mem_graph,
    germ.eventually_resolventEquation, germ.eventually_readout_eq] with
      z hzGraph hzEquation hzReadout
  by_cases hz : z.im = 0
  · simp [positiveJacobiHeightGluedBoundaryReadout, hz]
  · obtain ⟨x, hxFirst, hxSecond⟩ := A.mem_graph_iff.mp hzGraph
    have hxHeight : certificate.PositiveJacobiHeightResolventEquation z
        certificate.positiveJacobiCyclicHead x := by
      unfold PositiveJacobiHeightResolventEquation
      change (x : RealHilbertComplexification (EvenCarrier jet)) -
        z ^ 2 • A x = certificate.positiveJacobiCyclicHead
      rw [hxFirst, hxSecond]
      exact hzEquation
    have hunique := certificate.positiveJacobiHeightGlobalResolventVector_unique
      z hz x hxHeight
    rw [positiveJacobiHeightGluedBoundaryReadout, if_neg hz,
      positiveJacobiHeightGlobalBoundaryReadoutTotal,
      positiveJacobiHeightGlobalResolventState, dif_pos hz, ← hunique]
    calc
      ComplexifiedOrbitResolvent.headReadout
          (completedJacobiOrbit jet 0) x =
          germ.readout (germ.graphResolvent z) := by
        rw [hxFirst]
        rfl
      _ = completedNativeJacobiWeylHeightContinuation z := hzReadout

/-- The glued scalar readout is analytic at the Taylor centre. -/
theorem positiveJacobiHeightGluedBoundaryReadout_analyticAt_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticAt ℂ certificate.positiveJacobiHeightGluedBoundaryReadout 0 :=
  completedNativeJacobiWeylHeightContinuation_analyticAt_zero.congr
    certificate.positiveJacobiHeightGluedBoundaryReadout_eventuallyEq_weyl.symm

/-- Away from the real axis the glued readout is analytic because it is the
global positive-Jacobi resolvent readout. -/
theorem positiveJacobiHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ certificate.positiveJacobiHeightGluedBoundaryReadout z₀ := by
  apply (certificate.positiveJacobiHeightGlobalBoundaryReadoutTotal_analyticAt
    z₀ hz₀).congr
  filter_upwards
      [Complex.continuous_im.continuousAt.eventually_ne hz₀] with z hz
  simp [positiveJacobiHeightGluedBoundaryReadout, hz]

/-- Connected upper height cone, with the Taylor centre adjoined as its
star-centre. -/
def completedNativeUpperHeightCone : Set ℂ :=
  {z | z = 0 ∨ (0 < z.im ∧ z.im < (1 : ℝ) / 2)}

@[simp] theorem zero_mem_completedNativeUpperHeightCone :
    (0 : ℂ) ∈ completedNativeUpperHeightCone :=
  Or.inl rfl

/-- Every point of the upper cone lies in the natural centred-height strip. -/
theorem completedNativeUpperHeightCone_subset_heightDomain :
    completedNativeUpperHeightCone ⊆ completedNativeHeightDomain := by
  intro z hz
  rcases hz with rfl | ⟨hzpos, hzupper⟩
  · exact zero_mem_completedNativeHeightDomain
  · unfold completedNativeHeightDomain
    change 0 < (operatorHeightParameter z).re ∧
      (operatorHeightParameter z).re < 1
    simp only [operatorHeightParameter, Complex.add_re, Complex.div_re,
      Complex.one_re, Complex.I_mul_re]
    norm_num
    constructor <;> linarith

/-- The upper cone is star-convex at the Taylor centre. -/
theorem completedNativeUpperHeightCone_starConvex :
    StarConvex ℝ (0 : ℂ) completedNativeUpperHeightCone := by
  rw [starConvex_iff_forall_pos zero_mem_completedNativeUpperHeightCone]
  intro y hy a b ha hb hab
  rcases hy with rfl | ⟨hypos, hyupper⟩
  · left
    simp
  · right
    rw [smul_zero, zero_add, Complex.smul_im]
    constructor
    · exact mul_pos hb hypos
    · have hbOne : b < 1 := by linarith
      have hmul : b * y.im < y.im := by
        simpa using mul_lt_mul_of_pos_right hbOne hypos
      change b * y.im < (1 : ℝ) / 2
      exact hmul.trans hyupper

/-- The upper cone is preconnected, so the analytic identity principle
propagates identities from the Taylor centre throughout it. -/
theorem isPreconnected_completedNativeUpperHeightCone :
    IsPreconnected completedNativeUpperHeightCone :=
  (completedNativeUpperHeightCone_starConvex.isPathConnected
    zero_mem_completedNativeUpperHeightCone).isConnected.isPreconnected

/-- Division-free ODE defect coupling the global Jacobi readout to the native
characteristic. -/
def positiveJacobiWeylODEDefect
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) : ℂ :=
  ((2 : ℂ) * z) * certificate.positiveJacobiHeightGluedBoundaryReadout z *
      completedNativeOperatorCharacteristic z +
    deriv completedNativeOperatorCharacteristic z

/-- The division-free ODE defect is analytic throughout the upper cone. -/
theorem positiveJacobiWeylODEDefect_analyticOnNhd_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticOnNhd ℂ certificate.positiveJacobiWeylODEDefect
      completedNativeUpperHeightCone := by
  intro z hz
  have hF := completedNativeOperatorCharacteristic_analyticAt
    (completedNativeUpperHeightCone_subset_heightDomain hz)
  have hm : AnalyticAt ℂ
      certificate.positiveJacobiHeightGluedBoundaryReadout z := by
    rcases hz with rfl | hz
    · exact certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_zero
    · exact certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_gt hz.1)
  have hzMap : AnalyticAt ℂ (fun w : ℂ ↦ (2 : ℂ) * w) z := by
    fun_prop
  exact (((hzMap.mul hm).mul hF).add hF.deriv).congr
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- The ODE defect vanishes in a full neighborhood of the Taylor centre. -/
theorem positiveJacobiWeylODEDefect_eventuallyEq_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.positiveJacobiWeylODEDefect =ᶠ[nhds 0] 0 := by
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hFne : ∀ᶠ z : ℂ in nhds 0,
      completedNativeOperatorCharacteristic z ≠ 0 :=
    (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).continuousAt.eventually_ne hF0
  have hderiv0 : deriv completedNativeOperatorCharacteristic 0 = 0 := by
    have hlog := completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate.self_of_nhds
    have hquot :
        -deriv completedNativeOperatorCharacteristic 0 /
            completedNativeOperatorCharacteristic 0 = 0 := by
      simpa [completedNativeOperatorLogDerivative] using hlog
    have hneg : -deriv completedNativeOperatorCharacteristic 0 = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right hF0
    exact neg_eq_zero.mp hneg
  filter_upwards
      [certificate.positiveJacobiHeightGluedBoundaryReadout_eventuallyEq_weyl,
        hFne] with z hreadout hFz
  change certificate.positiveJacobiWeylODEDefect z = (0 : ℂ)
  by_cases hz : z = 0
  · subst z
    simp [positiveJacobiWeylODEDefect, hderiv0]
  · rw [positiveJacobiWeylODEDefect, hreadout,
      completedNativeJacobiWeylHeightContinuation, if_neg hz,
      completedNativeOperatorLogDerivative]
    field_simp [hz, hFz]
    ring

/-- Global division-free Jacobi/Weyl ODE on the connected upper height cone. -/
theorem positiveJacobiWeylODEDefect_eq_zero_on_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    Set.EqOn certificate.positiveJacobiWeylODEDefect 0
      completedNativeUpperHeightCone :=
  certificate.positiveJacobiWeylODEDefect_analyticOnNhd_upper
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_completedNativeUpperHeightCone
      zero_mem_completedNativeUpperHeightCone
      certificate.positiveJacobiWeylODEDefect_eventuallyEq_zero

/-- The global analytic Jacobi readout excludes native zeros in the open
upper part of the centred-height strip. -/
theorem completedNativeOperatorCharacteristic_ne_zero_on_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hz : z ∈ completedNativeUpperHeightCone) :
    completedNativeOperatorCharacteristic z ≠ 0 := by
  rcases hz with rfl | hzUpper
  · exact completedNativeOperatorCharacteristic_zero_ne_zero
  · intro hzero
    have hzDomain : z ∈ completedNativeHeightDomain :=
      completedNativeUpperHeightCone_subset_heightDomain (Or.inr hzUpper)
    have hF := completedNativeOperatorCharacteristic_analyticAt hzDomain
    have hFne : ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
        completedNativeOperatorCharacteristic w ≠ 0 :=
      hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
    have hUpperOpen : IsOpen {w : ℂ |
        0 < w.im ∧ w.im < (1 : ℝ) / 2} := by
      exact (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have hdefect : ∀ᶠ w : ℂ in nhds z,
        certificate.positiveJacobiWeylODEDefect w = 0 := by
      filter_upwards [hUpperOpen.mem_nhds hzUpper] with w hw
      exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_upper
        (Or.inr hw)
    have hlogEq : completedNativeOperatorLogDerivative =ᶠ[nhdsWithin z {z}ᶜ]
        fun w ↦ ((2 : ℂ) * w) *
          certificate.positiveJacobiHeightGluedBoundaryReadout w := by
      filter_upwards [hFne, hdefect.filter_mono nhdsWithin_le_nhds] with
          w hFw hdefectw
      unfold completedNativeOperatorLogDerivative
      apply (div_eq_iff hFw).2
      unfold positiveJacobiWeylODEDefect at hdefectw
      linear_combination -hdefectw
    have hm :=
      certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_gt hzUpper.1)
    have hfactor : AnalyticAt ℂ (fun w : ℂ ↦ (2 : ℂ) * w) z := by
      fun_prop
    have hrhs : AnalyticAt ℂ
        (fun w ↦ ((2 : ℂ) * w) *
          certificate.positiveJacobiHeightGluedBoundaryReadout w) z :=
      hfactor.mul hm
    have horder := meromorphicOrderAt_congr hlogEq
    rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
      hzDomain hzero] at horder
    have hnonneg := hrhs.meromorphicOrderAt_nonneg
    rw [← horder] at hnonneg
    exact (not_le_of_gt
      (show ((-1 : ℤ) : WithTop ℤ) < 0 by
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hnonneg

/-- Connected lower height cone, again with the Taylor centre as its
star-centre. -/
def completedNativeLowerHeightCone : Set ℂ :=
  {z | z = 0 ∨ (-((1 : ℝ) / 2) < z.im ∧ z.im < 0)}

@[simp] theorem zero_mem_completedNativeLowerHeightCone :
    (0 : ℂ) ∈ completedNativeLowerHeightCone :=
  Or.inl rfl

theorem completedNativeLowerHeightCone_subset_heightDomain :
    completedNativeLowerHeightCone ⊆ completedNativeHeightDomain := by
  intro z hz
  rcases hz with rfl | ⟨hzlower, hzneg⟩
  · exact zero_mem_completedNativeHeightDomain
  · unfold completedNativeHeightDomain
    change 0 < (operatorHeightParameter z).re ∧
      (operatorHeightParameter z).re < 1
    simp only [operatorHeightParameter, Complex.add_re, Complex.div_re,
      Complex.one_re, Complex.I_mul_re]
    norm_num
    constructor <;> linarith

theorem completedNativeLowerHeightCone_starConvex :
    StarConvex ℝ (0 : ℂ) completedNativeLowerHeightCone := by
  rw [starConvex_iff_forall_pos zero_mem_completedNativeLowerHeightCone]
  intro y hy a b ha hb hab
  rcases hy with rfl | ⟨hylower, hyneg⟩
  · left
    simp
  · right
    rw [smul_zero, zero_add, Complex.smul_im]
    constructor
    · have hbOne : b < 1 := by linarith
      have hmul : y.im < b * y.im := by
        simpa using mul_lt_mul_of_neg_right hbOne hyneg
      exact hylower.trans hmul
    · exact mul_neg_of_pos_of_neg hb hyneg

theorem isPreconnected_completedNativeLowerHeightCone :
    IsPreconnected completedNativeLowerHeightCone :=
  (completedNativeLowerHeightCone_starConvex.isPathConnected
    zero_mem_completedNativeLowerHeightCone).isConnected.isPreconnected

theorem positiveJacobiWeylODEDefect_analyticOnNhd_lower
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticOnNhd ℂ certificate.positiveJacobiWeylODEDefect
      completedNativeLowerHeightCone := by
  intro z hz
  have hF := completedNativeOperatorCharacteristic_analyticAt
    (completedNativeLowerHeightCone_subset_heightDomain hz)
  have hm : AnalyticAt ℂ
      certificate.positiveJacobiHeightGluedBoundaryReadout z := by
    rcases hz with rfl | hz
    · exact certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_zero
    · exact certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_lt hz.2)
  have hzMap : AnalyticAt ℂ (fun w : ℂ ↦ (2 : ℂ) * w) z := by
    fun_prop
  exact (((hzMap.mul hm).mul hF).add hF.deriv).congr
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Global division-free Jacobi/Weyl ODE on the connected lower height cone. -/
theorem positiveJacobiWeylODEDefect_eq_zero_on_lower
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    Set.EqOn certificate.positiveJacobiWeylODEDefect 0
      completedNativeLowerHeightCone :=
  certificate.positiveJacobiWeylODEDefect_analyticOnNhd_lower
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_completedNativeLowerHeightCone
      zero_mem_completedNativeLowerHeightCone
      certificate.positiveJacobiWeylODEDefect_eventuallyEq_zero

/-- The same order contradiction excludes native zeros in the open lower
part of the centred-height strip. -/
theorem completedNativeOperatorCharacteristic_ne_zero_on_lower
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hz : z ∈ completedNativeLowerHeightCone) :
    completedNativeOperatorCharacteristic z ≠ 0 := by
  rcases hz with rfl | hzLower
  · exact completedNativeOperatorCharacteristic_zero_ne_zero
  · intro hzero
    have hzDomain : z ∈ completedNativeHeightDomain :=
      completedNativeLowerHeightCone_subset_heightDomain (Or.inr hzLower)
    have hF := completedNativeOperatorCharacteristic_analyticAt hzDomain
    have hFne : ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
        completedNativeOperatorCharacteristic w ≠ 0 :=
      hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
    have hLowerOpen : IsOpen {w : ℂ |
        -((1 : ℝ) / 2) < w.im ∧ w.im < 0} := by
      exact (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have hdefect : ∀ᶠ w : ℂ in nhds z,
        certificate.positiveJacobiWeylODEDefect w = 0 := by
      filter_upwards [hLowerOpen.mem_nhds hzLower] with w hw
      exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_lower
        (Or.inr hw)
    have hlogEq : completedNativeOperatorLogDerivative =ᶠ[nhdsWithin z {z}ᶜ]
        fun w ↦ ((2 : ℂ) * w) *
          certificate.positiveJacobiHeightGluedBoundaryReadout w := by
      filter_upwards [hFne, hdefect.filter_mono nhdsWithin_le_nhds] with
          w hFw hdefectw
      unfold completedNativeOperatorLogDerivative
      apply (div_eq_iff hFw).2
      unfold positiveJacobiWeylODEDefect at hdefectw
      linear_combination -hdefectw
    have hm :=
      certificate.positiveJacobiHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_lt hzLower.2)
    have hfactor : AnalyticAt ℂ (fun w : ℂ ↦ (2 : ℂ) * w) z := by
      fun_prop
    have hrhs : AnalyticAt ℂ
        (fun w ↦ ((2 : ℂ) * w) *
          certificate.positiveJacobiHeightGluedBoundaryReadout w) z :=
      hfactor.mul hm
    have horder := meromorphicOrderAt_congr hlogEq
    rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
      hzDomain hzero] at horder
    have hnonneg := hrhs.meromorphicOrderAt_nonneg
    rw [← horder] at hnonneg
    exact (not_le_of_gt
      (show ((-1 : ℤ) : WithTop ℤ) < 0 by
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hnonneg

/-- Explicit centred-height description of the natural strip. -/
theorem mem_completedNativeHeightDomain_iff_im_bounds
    {z : ℂ} :
    z ∈ completedNativeHeightDomain ↔
      -((1 : ℝ) / 2) < z.im ∧ z.im < (1 : ℝ) / 2 := by
  unfold completedNativeHeightDomain
  change (0 < (operatorHeightParameter z).re ∧
      (operatorHeightParameter z).re < 1) ↔ _
  simp only [operatorHeightParameter, Complex.add_re, Complex.div_re,
    Complex.one_re, Complex.I_mul_re]
  norm_num
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

set_option maxHeartbeats 800000 in
/-- Final carrier-correct Hilbert--Polya confinement theorem.

The hypothesis is only the real HP carrier certificate that constructs the
existing positive self-adjoint Jacobi operator.  The former pointwise
`HasGlobalGraphResolventAt` continuation hypothesis does not occur: global
resolvent existence, local analytic gluing, and the division-free ODE identity
are theorems above. -/
theorem completedNativeOperator_zero_im_eq_zero_of_positiveJacobiResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  by_contra him
  have hbounds := mem_completedNativeHeightDomain_iff_im_bounds.mp hzDomain
  rcases lt_or_gt_of_ne him with hneg | hpos
  · exact certificate.completedNativeOperatorCharacteristic_ne_zero_on_lower
      (Or.inr ⟨hbounds.1, hneg⟩) hzero
  · exact certificate.completedNativeOperatorCharacteristic_ne_zero_on_upper
      (Or.inr ⟨hpos, hbounds.2⟩) hzero

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
