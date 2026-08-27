import CarrySelfAdjointOperator.CompletedNativeHPConfinement
import CarrySelfAdjointOperator.BR2ProjectiveHilbertIncidenceTransport
import CarrySelfAdjointOperator.BR2CenterLegCoefficientRecurrence
import Mathlib.Tactic

/-!
# Audit and corrected carrier for the completed native HP route

The normalized product ledger contains the radial phase.  Consequently its
first complex Taylor jet at the center is zero: the state is not complex
differentiable there.  This makes the former reduced certificate, whose odd
family starts with that jet, uninhabited.

The viable all-order route is real.  The exact bracket--TFVD transport already
lands in one concrete infinite-dimensional Hilbert carrier and proves global
independence of both parity families.  The corrected certificate below keeps
that carrier and asks only for the remaining Gram identification with the
canonical completed-native moments.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open Filter Topology

noncomputable section

/-! ## The complex radial Taylor certificate is uninhabited -/

/-- The first odd complex Taylor jet of the normalized completed product
ledger is zero for every choice of the auxiliary completion-factor state. -/
theorem canonicalCompletedNativeGreenParityJet_firstOdd_eq_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    canonicalCompletedNativeGreenParityJet xiState (Sum.inr 0) = 0 := by
  simp only [canonicalCompletedNativeGreenParityJet,
    completedGreenParityJet, Nat.mul_zero, zero_add]
  unfold completedGreenTaylorJet
  rw [show iteratedDeriv 1
        (canonicalCompletedNativeNormalizedGreenState xiState) 0 = 0 by
    simpa [canonicalCompletedNativeNormalizedGreenState, iteratedDeriv_one]
      using deriv_zero_of_not_differentiableAt
        (normalizedCompletedNativeC3ProductLedger_not_differentiableAt_zero
          xiState)]
  simp

/-- Therefore the complex-Taylor reduced certificate used by the former HP
interface has no inhabitant.  This is a carrier mismatch, not a failure of the
real all-order bracket--TFVD transport. -/
theorem not_completedNativeGreenWeylReducedHeightCertificate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (moments : ℕ → ℝ) :
    ¬ CompletedNativeGreenWeylReducedHeightCertificate xiState moments := by
  intro certificate
  exact certificate.oddIndependent.ne_zero 0
    (canonicalCompletedNativeGreenParityJet_firstOdd_eq_zero xiState)

/-! ## Correct real projective TFVD/Hilbert carrier -/

/-- Carrier-honest HP input.  The jet is an arbitrary real Hilbert realization
of the canonical completed-native moment Gram, with its two parity families
kept globally independent. -/
structure CompletedNativeRealHPCarrierCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) : Prop where
  momentKernel :
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment jet
  evenIndependent :
    LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inl n))
  oddIndependent :
    LinearIndependent ℝ (fun n : ℕ ↦ jet (Sum.inr n))

namespace CompletedNativeRealHPCarrierCertificate

open ComplexifiedOrbitResolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

/-- Automatically completed jet used by the closed Jacobi construction. -/
abbrev completedJet (jet : (ℕ ⊕ ℕ) → E) :=
  completedGreenJet jet

/-- Closed even cyclic carrier of the corrected real HP realization. -/
abbrev EvenCarrier (jet : (ℕ ⊕ ℕ) → E) :=
  greenJetEvenHilbertSubspace (completedJet jet)

local instance evenCarrierCompleteSpace (jet : (ℕ ⊕ ℕ) → E) :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- A carrier-honest certificate supplies strict positivity of every canonical
completed-native Hankel pair. -/
theorem hankelPair_posDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef ∧
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosDef := by
  exact
    ⟨hankelGram_posDef_of_gramRepresentation
        (greenWronskianMomentKernel_even_momentGram
          certificate.momentKernel) N
        (greenJetEven_prefix_linearIndependent
          certificate.evenIndependent N),
      shiftedHankel_posDef_of_gramRepresentation
        (greenWronskianMomentKernel_odd_shiftedMomentGram
          certificate.momentKernel) N
        (greenJetOdd_prefix_linearIndependent
          certificate.oddIndependent N)⟩

/-- The same certificate constructs the canonical reduced maximal
self-adjoint signed-height operator after Hilbert completion. -/
def toReducedMaximalSelfAdjointHeightData
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :=
  canonicalCompletedGreenJetReducedReciprocalSignedHeightData
    certificate.momentKernel certificate.evenIndependent
      certificate.oddIndependent

/-- Concrete positive Jacobi operator on the completed real carrier. -/
def completedJacobiEnergyOperator
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    EvenCarrier jet →ₗ.[ℝ] EvenCarrier jet :=
  closedGreenJetEnergyAdjointSquare
    (completedGreenJet_gramRepresentation certificate.momentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent)

/-- The corrected concrete Jacobi operator bundled with maximal
self-adjointness. -/
def completedJacobiEnergySelfAdjointData
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    LinearPMap.RealMaximalSelfAdjointData (EvenCarrier jet) :=
  { operator := certificate.completedJacobiEnergyOperator
    denseDomain := closedGreenJetEnergyAdjointSquare_dense_domain
      (completedGreenJet_gramRepresentation certificate.momentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent)
    adjoint_eq := closedGreenJetEnergyAdjointSquare_isMaximalRealSelfAdjoint
      (completedGreenJet_gramRepresentation certificate.momentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent) }

/-- Positivity of the corrected concrete Jacobi operator. -/
theorem completedJacobiEnergyOperator_inner_nonneg
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (x : certificate.completedJacobiEnergyOperator.domain) :
    0 ≤ inner ℝ (certificate.completedJacobiEnergyOperator x)
      (x : EvenCarrier jet) := by
  exact closedGreenJetEnergyAdjointSquare_inner_nonneg
    (completedGreenJet_gramRepresentation certificate.momentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent) x

/-- Cyclic orbit on which the positive Jacobi operator is the forward shift. -/
def completedJacobiOrbit (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    EvenCarrier jet :=
  greenJetEvenSectorJet (completedJet jet) n

/-- Squared orbit norms are the even canonical moments. -/
theorem completedJacobiOrbit_norm_sq_eq_canonicalMoment
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (n : ℕ) :
    ‖completedJacobiOrbit jet n‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment (2 * n) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
      (greenJetEvenSectorJet (completedGreenJet jet) n)
      (greenJetEvenSectorJet (completedGreenJet jet) n) = _
  rw [inner_greenJetEvenSectorJet_eq_moment
    (completedGreenJet_gramRepresentation certificate.momentKernel)]
  congr 1
  omega

/-- Analyticity of the native logarithmic derivative bounds the corrected
cyclic orbit geometrically. -/
theorem completedJacobiOrbit_geometricBound
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖completedJacobiOrbit jet n‖ ≤ D * r ^ n := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    canonicalCompletedNativeLogDerivativeMoment_geometricBound
  refine ⟨Real.sqrt C, r, Real.sqrt_pos.2 hC, hr, fun n ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr.le _))).mp
  calc
    ‖completedJacobiOrbit jet n‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment (2 * n) :=
      certificate.completedJacobiOrbit_norm_sq_eq_canonicalMoment n
    _ ≤ |canonicalCompletedNativeLogDerivativeMoment (2 * n)| :=
      le_abs_self _
    _ ≤ C * r ^ (2 * n) := hbound (2 * n)
    _ = (Real.sqrt C * r ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC.le, ← pow_mul]
      congr 2
      omega

/-- The corrected Jacobi orbit lies in the natural operator domain and is
shifted exactly by one. -/
theorem completedJacobiOrbit_isOperatorOrbit
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ∀ n : ℕ, ∃ x : certificate.completedJacobiEnergyOperator.domain,
      (x : EvenCarrier jet) = completedJacobiOrbit jet n ∧
        certificate.completedJacobiEnergyOperator x =
          completedJacobiOrbit jet (n + 1) := by
  intro n
  let x : certificate.completedJacobiEnergyOperator.domain :=
    greenJetEvenCoreInClosedAdjointSquareDomain
      (completedGreenJet_gramRepresentation certificate.momentKernel)
      (completedGreenJet_even_linearIndependent certificate.evenIndependent)
      (completedGreenJet_odd_linearIndependent certificate.oddIndependent)
      (greenJetEvenCoreJet (completedJet jet) n)
  refine ⟨x, rfl, ?_⟩
  exact closedGreenJetEnergyAdjointSquare_apply_cyclicJet
    (completedGreenJet_gramRepresentation certificate.momentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent) n

/-- The cyclic head readout is exactly the canonical native moment. -/
theorem completedJacobiOrbit_head_inner_eq_canonicalMoment
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (n : ℕ) :
    (inner ℝ (completedJacobiOrbit jet 0)
        (completedJacobiOrbit jet n) : ℂ) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  have hmoment : inner ℝ (completedJacobiOrbit jet n)
      (completedJacobiOrbit jet 0) =
        canonicalCompletedNativeLogDerivativeMoment n := by
    simpa only [completedJacobiOrbit, completedJet, Nat.add_zero] using
      inner_greenJetEvenSectorJet_eq_moment
        (completedGreenJet_gramRepresentation certificate.momentKernel) n 0
  rw [real_inner_comm, hmoment]

set_option maxHeartbeats 300000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Local vector graph resolvent on the corrected real HP carrier. -/
def completedJacobiComplexGraphResolvent_germ
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    GermCertificate (E := EvenCarrier jet)
      certificate.completedJacobiEnergyOperator
      (ofReal (E := EvenCarrier jet) (completedJacobiOrbit jet 0))
      completedNativeLogDerivative :=
  germCertificate_of_orbit
    (E := EvenCarrier jet)
    certificate.completedJacobiEnergyOperator
    (by
      unfold completedJacobiEnergyOperator
      exact closedGreenJetEnergyAdjointSquare_isClosed
        (completedGreenJet_gramRepresentation certificate.momentKernel)
        (completedGreenJet_even_linearIndependent certificate.evenIndependent)
        (completedGreenJet_odd_linearIndependent certificate.oddIndependent))
    (v := completedJacobiOrbit jet)
    (coeff := fun n ↦
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
    (f := completedNativeLogDerivative)
    (completedJacobiOrbit_geometricBound (jet := jet) certificate)
    (completedJacobiOrbit_isOperatorOrbit (jet := jet) certificate)
    (completedJacobiOrbit_head_inner_eq_canonicalMoment
      (jet := jet) certificate)
    completedNativeLogDerivative_eventually_hasSum_canonical

/-- The corrected local graph germ in the signed-height coordinate. -/
def completedJacobiComplexGraphResolvent_heightGerm
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    HeightGermCertificate (E := EvenCarrier jet)
      certificate.completedJacobiEnergyOperator
      (ofReal (E := EvenCarrier jet) (completedJacobiOrbit jet 0))
      completedNativeJacobiWeylHeightContinuation :=
  certificate.completedJacobiComplexGraphResolvent_germ
    |>.squareReparameterization
    |>.congrScalar
      completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq.symm

/-! ## Exact global continuation gate on the corrected carrier -/

/-- Extension of the already-constructed local graph state to one selected
height.  The operator, source equation, and scalar readout are unchanged. -/
def HasGlobalGraphResolventAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) : Prop :=
  let data := certificate.completedJacobiEnergySelfAdjointData
  ∃ (graphResolvent : ℂ →
        RealHilbertComplexification (EvenCarrier jet) ×
          RealHilbertComplexification (EvenCarrier jet))
      (source : RealHilbertComplexification (EvenCarrier jet))
      (readout :
        (RealHilbertComplexification (EvenCarrier jet) ×
          RealHilbertComplexification (EvenCarrier jet)) →L[ℂ] ℂ),
    MeromorphicAt graphResolvent z₀ ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        graphResolvent z ∈ data.complexification.graph) ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        (graphResolvent z).1 - z ^ 2 • (graphResolvent z).2 = source) ∧
      (∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        readout (graphResolvent z) =
          completedNativeJacobiWeylHeightContinuation z)

/-- The global interface is already satisfied at the Taylor center by the
concrete local graph germ.  Thus only continuation away from the center is a
remaining issue. -/
theorem hasGlobalGraphResolventAt_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.HasGlobalGraphResolventAt 0 := by
  let germ := certificate.completedJacobiComplexGraphResolvent_heightGerm
  refine ⟨germ.graphResolvent,
    ofReal (E := EvenCarrier jet) (completedJacobiOrbit jet 0), germ.readout,
    germ.analyticAt.meromorphicAt, ?_, ?_, ?_⟩
  · exact germ.eventually_mem_graph.filter_mono nhdsWithin_le_nhds
  · exact germ.eventually_resolventEquation.filter_mono nhdsWithin_le_nhds
  · exact germ.eventually_readout_eq.filter_mono nhdsWithin_le_nhds

/-- The same concrete graph state satisfies the global interface at every
point in a neighborhood of the Taylor center.  Thus the unresolved part of
the global gate is genuinely continuation beyond the constructed germ. -/
theorem eventually_hasGlobalGraphResolventAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ∀ᶠ z₀ : ℂ in nhds 0, certificate.HasGlobalGraphResolventAt z₀ := by
  let germ := certificate.completedJacobiComplexGraphResolvent_heightGerm
  filter_upwards [germ.analyticAt.eventually_analyticAt,
    germ.eventually_mem_graph.eventually_nhds,
    germ.eventually_resolventEquation.eventually_nhds,
    germ.eventually_readout_eq.eventually_nhds] with
      z₀ hzAnalytic hzGraph hzEquation hzReadout
  refine ⟨germ.graphResolvent,
    ofReal (E := EvenCarrier jet) (completedJacobiOrbit jet 0), germ.readout,
    hzAnalytic.meromorphicAt, ?_, ?_, ?_⟩
  · exact hzGraph.filter_mono nhdsWithin_le_nhds
  · exact hzEquation.filter_mono nhdsWithin_le_nhds
  · exact hzReadout.filter_mono nhdsWithin_le_nhds

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- At a native zero, the corrected global graph continuation produces the
reciprocal-square point eigenvalue of the concrete positive Jacobi operator. -/
theorem completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_globalGraphResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hglobal : certificate.HasGlobalGraphResolventAt z₀) :
    LinearPMap.HasEigenvalue
      certificate.completedJacobiEnergySelfAdjointData.complexification
      (z₀ ^ 2)⁻¹ := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  rcases hglobal with
    ⟨graphResolvent, source, readout, hmeromorphic,
      hgraph, hresolvent, hreadout⟩
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have hreadoutCobounded :
      Tendsto (fun z ↦ readout (graphResolvent z))
        (nhdsWithin z₀ {z₀}ᶜ) (Bornology.cobounded ℂ) := by
    have hreadoutSymm : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        completedNativeJacobiWeylHeightContinuation z =
          readout (graphResolvent z) := by
      filter_upwards [hreadout] with z hz
      exact hz.symm
    exact
      (completedNativeJacobiWeylHeightContinuation_tendsto_cobounded_at_nativeZero
        hzDomain hzero).congr' hreadoutSymm
  exact
    LinearPMap.hasEigenvalue_inv_parameter_of_meromorphic_graphResolvent_readout
      data.complexification data.complexification_isClosed
      (parameter := fun z : ℂ ↦ z ^ 2)
      (by fun_prop) (pow_ne_zero 2 hz₀)
      hmeromorphic readout hreadoutCobounded hgraph hresolvent

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Carrier-correct Hilbert--Polya implication.  No complex radial Taylor
certificate occurs in this theorem. -/
theorem zero_im_eq_zero_of_globalGraphResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ}
    (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hglobal : certificate.HasGlobalGraphResolventAt z₀) :
    z₀.im = 0 := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have heigen :
      LinearPMap.HasEigenvalue data.complexification (z₀ ^ 2)⁻¹ := by
    exact certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_globalGraphResolvent
      hzDomain hzero hglobal
  have hspectrum :=
    data.complexification_eigenvalue_real_nonneg
      certificate.completedJacobiEnergyOperator_inner_nonneg heigen
  exact complex_im_eq_zero_of_sq_inv_real_nonneg
    hz₀ hspectrum.1 hspectrum.2

end CompletedNativeRealHPCarrierCertificate

section ProjectiveTfvdCarrier

local instance canonicalCompletedTfvdGreenRealInnerProductSpace :
    InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
  InnerProductSpace.rclikeToReal ℂ _

/-- Exact vector bridge still required on the concrete completed TFVD/Green
Hilbert carrier.  It keeps the target jet, the injective all-order incidence
transport, and the canonical native moment Gram in one typed object.  The
transport is not assumed to preserve the raw incidence inner product. -/
structure CanonicalCompletedNativeRealTfvdGreenMomentTransport
    (base radius : ℕ) where
  jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier
  incidenceTransport : BR2BracketIncidenceJetTransport base radius jet
  momentKernel :
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment jet

/-- The exact state-level identity needed after the scalar coefficient
recurrence has been discharged.  It compares the canonical polarized Green
coefficient with the complex Hilbert inner product of the same TFVD carrier
jets, while retaining the center--leg off-diagonal witness. -/
def HasCanonicalCompletedNativeTfvdGreenCenterLegReadout
    (incidence : BR2CameraIncidence)
    (jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    incidence.centerCoordinate i ≠ incidence.legCoordinate j →
      polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment
          (br2ParityJetNumber i) (br2ParityJetNumber j) =
        inner ℂ (jet i) (jet j)

/-- A center--leg readout on the concrete completed TFVD carrier produces the
real moment Gram required by the carrier-correct HP certificate.  The scalar
coefficient recurrence is supplied internally by the canonical moments. -/
def canonicalCompletedNativeRealTfvdGreenMomentTransport_of_centerLegReadout
    {base radius : ℕ}
    {jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (incidence : BR2CameraIncidence)
    (hreadout :
      HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence jet) :
    CanonicalCompletedNativeRealTfvdGreenMomentTransport base radius := by
  let certificate : BR2CenterLegCoefficientCertificate incidence
      canonicalCompletedNativeLogDerivativeMoment jet :=
    { coeff := polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment
      coefficientEquation :=
        polarizedGreenMomentCoefficient_coefficientEquation _
      greenOffDiagonalReadout := hreadout }
  refine
    { jet := jet
      incidenceTransport := transport
      momentKernel := ?_ }
  intro i j
  change greenWronskianMomentKernel
      canonicalCompletedNativeLogDerivativeMoment i j =
    (inner ℂ (jet i) (jet j)).re
  have h := congrArg Complex.re (certificate.toComplexMomentKernel i j)
  simpa using h

/-- A concrete TFVD/Green moment transport discharges both independence
fields through the existing all-order incidence theorem and supplies the
carrier-correct HP certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_tfvdGreenMomentTransport
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (transport :
      CanonicalCompletedNativeRealTfvdGreenMomentTransport base radius) :
    CompletedNativeRealHPCarrierCertificate transport.jet where
  momentKernel := transport.momentKernel
  evenIndependent := transport.incidenceTransport.even_linearIndependent
    hbase hradius
  oddIndependent := transport.incidenceTransport.odd_linearIndependent
    hbase hradius

/-- Direct carrier-correct HP constructor from the one remaining center--leg
state identity.  Incidence injectivity supplies both global parity
independence fields; the coefficient recurrence supplies all four moment
blocks. -/
theorem completedNativeRealHPCarrierCertificate_of_centerLegReadout
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    {jet : (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier}
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (incidence : BR2CameraIncidence)
    (hreadout :
      HasCanonicalCompletedNativeTfvdGreenCenterLegReadout incidence jet) :
    CompletedNativeRealHPCarrierCertificate jet :=
  completedNativeRealHPCarrierCertificate_of_tfvdGreenMomentTransport
    hbase hradius
      (canonicalCompletedNativeRealTfvdGreenMomentTransport_of_centerLegReadout
        transport incidence hreadout)

end ProjectiveTfvdCarrier

end

end CarrySelfAdjointOperator
