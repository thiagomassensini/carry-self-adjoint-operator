import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolventAnalytic
import CarrySelfAdjointOperator.GreenJetReciprocalSignedHeightOperator
import Mathlib.Logic.Equiv.Nat
import Mathlib.Tactic

/-!
# Direct signed-generator resolvent for the completed native operator

The native moment germ is even in the height coordinate.  Rather than
globalizing it through the positive square `B* B`, this file keeps the two
parity channels and uses the already constructed maximal self-adjoint signed
generator

`K = [[0, B*], [B, 0]]`.

Its reciprocal on the nonzero support is the signed-height operator.  The
cyclic orbit alternates exactly between the completed even and odd Green jets,
so its scalar readout is the native height-coordinate Weyl germ without a
positivity argument.
-/

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A self-adjoint graph resolvent map is injective at every nonreal
parameter. -/
theorem graphResolventMap_injective_of_isSelfAdjoint_of_im_ne_zero
    {A : H →ₗ.[ℂ] H} (hself : IsSelfAdjoint A)
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Injective (graphResolventMap A lambda) := by
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjoint
    exact hadjoint
  have hanti := graphResolventMap_antilipschitz A lambda
    (abs_pos.mpr hlambda)
    (abs_im_mul_norm_le_norm_resolventDefect hformal lambda)
  exact hanti.injective

/-- A self-adjoint graph resolvent map is surjective at every nonreal
parameter.  This is the usual closed-range proof and does not use a positivity
bound. -/
theorem graphResolventMap_surjective_of_isSelfAdjoint_of_im_ne_zero
    {A : H →ₗ.[ℂ] H} (hself : IsSelfAdjoint A)
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    Function.Surjective (graphResolventMap A lambda) := by
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjoint
    exact hadjoint
  have hanti := graphResolventMap_antilipschitz A lambda
    (abs_pos.mpr hlambda)
    (abs_im_mul_norm_le_norm_resolventDefect hformal lambda)
  letI : CompleteSpace A.graph := hself.isClosed.completeSpace_coe
  have hRangeClosed : IsClosed
      ((graphResolventMap A lambda).range : Set H) := by
    change IsClosed (Set.range (graphResolventMap A lambda))
    exact hanti.isClosed_range
      (graphResolventMap A lambda).uniformContinuous
  letI : CompleteSpace (graphResolventMap A lambda).range :=
    hRangeClosed.completeSpace_coe
  have hnoEigen :
      ¬ LinearPMap.HasEigenvalue A (starRingEnd ℂ lambda) := by
    intro heigen
    have him := LinearPMap.eigenvalue_im_eq_zero_of_isSelfAdjoint
      hself heigen
    change -lambda.im = 0 at him
    exact hlambda (by linarith)
  have hRangeOrthogonal :
      (graphResolventMap A lambda).rangeᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    exact eq_zero_of_mem_graphResolventMap_range_orthogonal
      hself lambda hnoEigen hy
  have hRangeTop : (graphResolventMap A lambda).range = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hRangeOrthogonal
  intro source
  have hsource : source ∈ (graphResolventMap A lambda).range := by
    rw [hRangeTop]
    exact Submodule.mem_top
  exact hsource

end LinearPMap

/-- Inversion preserves nonreality. -/
theorem complex_inv_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    z⁻¹.im ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  intro hinv
  rw [Complex.inv_im] at hinv
  have hnorm : Complex.normSq z ≠ 0 := by
    intro hzero
    exact hz0 (Complex.normSq_eq_zero.mp hzero)
  have hneg : -z.im = 0 := (div_eq_zero_iff.mp hinv).resolve_right hnorm
  exact hz (neg_eq_zero.mp hneg)

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

abbrev OddCarrier (jet : (ℕ ⊕ ℕ) → E) :=
  greenJetOddHilbertSubspace (completedJet jet)

abbrev SignedGeneratorCarrier (jet : (ℕ ⊕ ℕ) → E) :=
  WithLp 2 (EvenCarrier jet × OddCarrier jet)

local instance signedGeneratorEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

local instance signedGeneratorOddCarrierCompleteSpace :
    CompleteSpace (OddCarrier jet) :=
  (greenJetOddHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- The concrete maximal self-adjoint signed generator on the completed HP
carrier. -/
def completedSignedGeneratorData
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    LinearPMap.RealMaximalSelfAdjointData (SignedGeneratorCarrier jet) :=
  closedGreenJetSignedGeneratorData
    (completedGreenJet_gramRepresentation certificate.momentKernel)
    (completedGreenJet_even_linearIndependent certificate.evenIndependent)
    (completedGreenJet_odd_linearIndependent certificate.oddIndependent)

/-- Even half of the alternating signed-generator orbit. -/
def completedSignedGeneratorEvenOrbit
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) : SignedGeneratorCarrier jet :=
  WithLp.toLp 2 ((completedJacobiOrbit jet n), 0)

/-- Odd half of the alternating signed-generator orbit. -/
def completedSignedGeneratorOddOrbit
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) : SignedGeneratorCarrier jet :=
  WithLp.toLp 2
    (0, greenJetOddSectorJet (completedJet jet) n)

/-- Single all-order orbit obtained by interleaving the even and odd Green
jets. -/
def completedSignedGeneratorOrbit
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) : SignedGeneratorCarrier jet :=
  Sum.elim (completedSignedGeneratorEvenOrbit jet)
    (completedSignedGeneratorOddOrbit jet)
      (Equiv.natSumNatEquivNat.symm n)

@[simp] theorem completedSignedGeneratorOrbit_even
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    completedSignedGeneratorOrbit jet (2 * n) =
      completedSignedGeneratorEvenOrbit jet n := by
  simp [completedSignedGeneratorOrbit]

@[simp] theorem completedSignedGeneratorOrbit_odd
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    completedSignedGeneratorOrbit jet (2 * n + 1) =
      completedSignedGeneratorOddOrbit jet n := by
  simp [completedSignedGeneratorOrbit]

/-- Scalar coefficients read by the even cyclic head from the alternating
orbit. -/
def completedSignedGeneratorCoefficient (n : ℕ) : ℂ :=
  Sum.elim
    (fun k : ℕ => (canonicalCompletedNativeLogDerivativeMoment k : ℂ))
    (fun _ : ℕ => 0)
    (Equiv.natSumNatEquivNat.symm n)

@[simp] theorem completedSignedGeneratorCoefficient_even (n : ℕ) :
    completedSignedGeneratorCoefficient (2 * n) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  simp [completedSignedGeneratorCoefficient]

@[simp] theorem completedSignedGeneratorCoefficient_odd (n : ℕ) :
    completedSignedGeneratorCoefficient (2 * n + 1) = 0 := by
  simp [completedSignedGeneratorCoefficient]

/-- Odd Green-jet norms are the odd canonical moments. -/
theorem completedSignedGeneratorOddOrbit_norm_sq_eq_canonicalMoment
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (n : ℕ) :
    ‖completedSignedGeneratorOddOrbit jet n‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment (2 * n + 1) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(0 : EvenCarrier jet)‖ ^ 2 +
      ‖greenJetOddSectorJet (completedJet jet) n‖ ^ 2 = _
  rw [norm_zero]
  norm_num
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
      (greenJetOddSectorJet (completedJet jet) n)
      (greenJetOddSectorJet (completedJet jet) n) = _
  have hodd := greenWronskianMomentKernel_odd_shiftedMomentGram
    (completedGreenJet_gramRepresentation certificate.momentKernel) n n
  change canonicalCompletedNativeLogDerivativeMoment (n + n + 1) =
      inner ℝ
        (greenJetOddSectorJet (completedJet jet) n)
        (greenJetOddSectorJet (completedJet jet) n) at hodd
  rw [← hodd]
  congr 1
  omega

/-- The full alternating orbit has squared norm equal to the canonical moment
with the same all-order index. -/
theorem completedSignedGeneratorOrbit_norm_sq_eq_canonicalMoment
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (n : ℕ) :
    ‖completedSignedGeneratorOrbit jet n‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [completedSignedGeneratorOrbit_even]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖completedJacobiOrbit jet k‖ ^ 2 +
        ‖(0 : OddCarrier jet)‖ ^ 2 = _
    rw [norm_zero]
    norm_num
    exact certificate.completedJacobiOrbit_norm_sq_eq_canonicalMoment k
  · rw [completedSignedGeneratorOrbit_odd]
    exact certificate.completedSignedGeneratorOddOrbit_norm_sq_eq_canonicalMoment k

/-- Analyticity of the native logarithmic derivative gives geometric growth
of the all-order alternating orbit itself. -/
theorem completedSignedGeneratorOrbit_geometricBound
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖completedSignedGeneratorOrbit jet n‖ ≤ D * r ^ n := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    canonicalCompletedNativeLogDerivativeMoment_geometricBound
  refine ⟨Real.sqrt C, Real.sqrt r, Real.sqrt_pos.2 hC,
    Real.sqrt_pos.2 hr, fun n => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mp
  calc
    ‖completedSignedGeneratorOrbit jet n‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment n :=
      certificate.completedSignedGeneratorOrbit_norm_sq_eq_canonicalMoment n
    _ ≤ |canonicalCompletedNativeLogDerivativeMoment n| := le_abs_self _
    _ ≤ C * r ^ n := hbound n
    _ = (Real.sqrt C * Real.sqrt r ^ n) ^ 2 := by
      symm
      rw [mul_pow, Real.sq_sqrt hC.le]
      congr 1
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul,
        Real.sq_sqrt hr.le]

set_option maxHeartbeats 800000 in
/-- The interleaved Green jets are the exact operator orbit of the signed
generator, channel by channel. -/
theorem completedSignedGeneratorOrbit_isOperatorOrbit
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ∀ n : ℕ, ∃ x : certificate.completedSignedGeneratorData.operator.domain,
      (x : SignedGeneratorCarrier jet) =
          completedSignedGeneratorOrbit jet n ∧
        certificate.completedSignedGeneratorData.operator x =
          completedSignedGeneratorOrbit jet (n + 1) := by
  let hrep : IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment (completedJet jet) :=
    completedGreenJet_gramRepresentation certificate.momentKernel
  let heven : LinearIndependent ℝ
      (fun n : ℕ => completedJet jet (Sum.inl n)) :=
    completedGreenJet_even_linearIndependent certificate.evenIndependent
  let hodd : LinearIndependent ℝ
      (fun n : ℕ => completedJet jet (Sum.inr n)) :=
    completedGreenJet_odd_linearIndependent certificate.oddIndependent
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · let x := closedGreenJetSignedGeneratorEvenCoreDomain
      hrep heven hodd k
    refine ⟨x, ?_, ?_⟩
    · rw [completedSignedGeneratorOrbit_even]
      exact closedGreenJetSignedGeneratorEvenCoreDomain_coe
        hrep heven hodd k
    ·
      rw [show 2 * k + 1 = 2 * k + 1 by rfl,
        completedSignedGeneratorOrbit_odd]
      exact closedGreenJetSignedGenerator_apply_evenCore
        hrep heven hodd k
  · let x := closedGreenJetSignedGeneratorOddCoreDomain
      hrep heven hodd k
    refine ⟨x, ?_, ?_⟩
    · rw [completedSignedGeneratorOrbit_odd]
      exact closedGreenJetSignedGeneratorOddCoreDomain_coe
        hrep heven hodd k
    ·
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
        completedSignedGeneratorOrbit_even]
      exact closedGreenJetSignedGenerator_apply_oddCore
        hrep heven hodd k

/-- The cyclic-head readout of the alternating orbit is exactly the
interleaved native coefficient sequence. -/
theorem completedSignedGeneratorOrbit_head_inner_eq_coefficient
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (n : ℕ) :
    (inner ℝ (completedSignedGeneratorOrbit jet 0)
        (completedSignedGeneratorOrbit jet n) : ℂ) =
      completedSignedGeneratorCoefficient n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [completedSignedGeneratorOrbit_even,
      completedSignedGeneratorCoefficient_even]
    have hzero : completedSignedGeneratorOrbit jet 0 =
        completedSignedGeneratorEvenOrbit jet 0 := by
      simpa using completedSignedGeneratorOrbit_even jet 0
    rw [hzero]
    simpa [completedSignedGeneratorEvenOrbit,
      WithLp.prod_inner_apply] using
        certificate.completedJacobiOrbit_head_inner_eq_canonicalMoment k
  · rw [completedSignedGeneratorOrbit_odd,
      completedSignedGeneratorCoefficient_odd]
    have hzero : completedSignedGeneratorOrbit jet 0 =
        completedSignedGeneratorEvenOrbit jet 0 := by
      simpa using completedSignedGeneratorOrbit_even jet 0
    rw [hzero]
    simp [completedSignedGeneratorEvenOrbit,
      completedSignedGeneratorOddOrbit, WithLp.prod_inner_apply]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Pointwise interleaving of the even native power series with its zero odd
part. -/
theorem completedSignedGeneratorCoefficient_hasSum_weyl
    (z : ℂ)
    (hsum : HasSum (fun n : ℕ =>
      (z ^ 2) ^ n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (completedNativeLogDerivative (z ^ 2)))
    (hweyl : completedNativeJacobiWeylHeightContinuation z =
      completedNativeLogDerivative (z ^ 2)) :
    HasSum (fun n : ℕ =>
      z ^ n * completedSignedGeneratorCoefficient n)
      (completedNativeJacobiWeylHeightContinuation z) := by
  have heven : HasSum
      (fun n : ℕ => z ^ (2 * n) *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (completedNativeLogDerivative (z ^ 2)) := by
    convert hsum using 1
    funext n
    rw [pow_mul]
  have hodd : HasSum
      (fun n : ℕ => z ^ (2 * n + 1) * (0 : ℂ)) 0 := by
    simpa only [mul_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  rw [hweyl]
  have hall : HasSum
      (fun n : ℕ => z ^ n * completedSignedGeneratorCoefficient n)
      (completedNativeLogDerivative (z ^ 2) + 0) := by
    apply HasSum.even_add_odd
    · simpa using heven
    · simpa only [completedSignedGeneratorCoefficient_odd] using hodd
  simpa using hall

/-- The interleaved coefficient series is exactly the native Weyl germ in
the height coordinate. -/
theorem completedSignedGeneratorCoefficient_eventually_hasSum_weyl :
    ∀ᶠ z : ℂ in nhds 0,
      HasSum (fun n : ℕ =>
        z ^ n * completedSignedGeneratorCoefficient n)
        (completedNativeJacobiWeylHeightContinuation z) := by
  have hsquare : Tendsto (fun z : ℂ => z ^ 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun z : ℂ => z ^ 2) 0 := by fun_prop
    simpa using h.tendsto
  filter_upwards
      [hsquare.eventually completedNativeLogDerivative_eventually_hasSum_canonical,
        completedNativeJacobiWeylHeightContinuation_eventuallyEq_reducedLogDerivative_sq]
      with z hsum hweyl
  exact completedSignedGeneratorCoefficient_hasSum_weyl z hsum hweyl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- Local graph-resolvent germ of the signed generator whose scalar readout
is already the canonical native Weyl continuation. -/
def completedSignedGeneratorComplexGraphResolvent_germ
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    ComplexifiedOrbitResolvent.GermCertificate
      certificate.completedSignedGeneratorData.operator
      (ComplexifiedOrbitResolvent.ofReal
        (completedSignedGeneratorOrbit jet 0))
      completedNativeJacobiWeylHeightContinuation :=
  ComplexifiedOrbitResolvent.germCertificate_of_orbit
    certificate.completedSignedGeneratorData.operator
    certificate.completedSignedGeneratorData.isClosed
    (v := completedSignedGeneratorOrbit jet)
    (coeff := completedSignedGeneratorCoefficient)
    (f := completedNativeJacobiWeylHeightContinuation)
    (certificate.completedSignedGeneratorOrbit_geometricBound)
    (certificate.completedSignedGeneratorOrbit_isOperatorOrbit)
    (certificate.completedSignedGeneratorOrbit_head_inner_eq_coefficient)
    completedSignedGeneratorCoefficient_eventually_hasSum_weyl

/-! ## Global nonreal resolvent of the signed generator -/

/-- Standard graph resolvent equation for the complexified signed generator. -/
def SignedGeneratorResolventEquation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ)
    (source : RealHilbertComplexification (SignedGeneratorCarrier jet))
    (x : certificate.completedSignedGeneratorData.complexification.domain) :
    Prop :=
  certificate.completedSignedGeneratorData.complexification x -
      lambda •
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
    source

/-- Every nonreal parameter is a global resolvent point of the signed
generator. -/
theorem hasGlobalSignedGeneratorResolventAt_of_im_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    ∀ source : RealHilbertComplexification (SignedGeneratorCarrier jet),
      ∃ x : certificate.completedSignedGeneratorData.complexification.domain,
        certificate.SignedGeneratorResolventEquation lambda source x := by
  let A := certificate.completedSignedGeneratorData.complexification
  have hsurjective : Function.Surjective
      (LinearPMap.graphResolventMap A lambda) :=
    LinearPMap.graphResolventMap_surjective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda
  intro source
  obtain ⟨p, hp⟩ := hsurjective source
  obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp p.property
  refine ⟨x, ?_⟩
  unfold SignedGeneratorResolventEquation
  change A x - lambda •
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) = source
  calc
    A x - lambda •
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
        LinearPMap.graphResolventMap A lambda p := by
      rw [LinearPMap.graphResolventMap_apply, ← hx, ← hAx]
    _ = source := hp

/-- Continuous inverse of the signed-generator graph defect at one nonreal
spectral parameter. -/
def signedGeneratorGraphResolventInverse
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
      certificate.completedSignedGeneratorData.complexification.graph :=
  LinearPMap.graphResolventInverseOfBijective
    certificate.completedSignedGeneratorData.complexification
    certificate.completedSignedGeneratorData.complexification_isClosed
    lambda
    (LinearPMap.graphResolventMap_injective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda)
    (LinearPMap.graphResolventMap_surjective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda)

/-- The graph inverse is a right inverse of the signed-generator defect map. -/
theorem signedGeneratorGraphResolventMap_inverse_apply
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (source : RealHilbertComplexification (SignedGeneratorCarrier jet)) :
    LinearPMap.graphResolventMap
        certificate.completedSignedGeneratorData.complexification lambda
        (certificate.signedGeneratorGraphResolventInverse
          lambda hlambda source) = source := by
  exact LinearPMap.graphResolventMap_inverseOfBijective_apply
    certificate.completedSignedGeneratorData.complexification
    certificate.completedSignedGeneratorData.complexification_isClosed
    lambda
    (LinearPMap.graphResolventMap_injective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda)
    (LinearPMap.graphResolventMap_surjective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda)
    source

/-- Ambient first-coordinate standard resolvent operator. -/
def signedGeneratorResolventOperator
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
      RealHilbertComplexification (SignedGeneratorCarrier jet) :=
  (ContinuousLinearMap.fst ℂ
      (RealHilbertComplexification (SignedGeneratorCarrier jet))
      (RealHilbertComplexification (SignedGeneratorCarrier jet))).comp
    certificate.completedSignedGeneratorData.complexification.graph.subtypeL
      |>.comp
    (certificate.signedGeneratorGraphResolventInverse lambda hlambda)

/-- Local standard-resolvent chart around a fixed nonreal parameter. -/
def signedGeneratorLocalResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : lambda₀.im ≠ 0)
    (source : RealHilbertComplexification (SignedGeneratorCarrier jet))
    (lambda : ℂ) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) :=
  let R₀ := certificate.signedGeneratorResolventOperator lambda₀ hlambda₀
  Ring.inverse (1 - (lambda - lambda₀) • R₀) (R₀ source)

/-- The local standard-resolvent chart is analytic at its centre. -/
theorem signedGeneratorLocalResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : lambda₀.im ≠ 0)
    (source : RealHilbertComplexification (SignedGeneratorCarrier jet)) :
    AnalyticAt ℂ
      (certificate.signedGeneratorLocalResolventState
        lambda₀ hlambda₀ source) lambda₀ := by
  let R₀ := certificate.signedGeneratorResolventOperator lambda₀ hlambda₀
  let B : ℂ →
      (RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
        RealHilbertComplexification (SignedGeneratorCarrier jet)) :=
    fun lambda => 1 - (lambda - lambda₀) • R₀
  have hB : AnalyticAt ℂ B lambda₀ := by
    dsimp only [B]
    fun_prop
  have hBValue : B lambda₀ = 1 := by simp [B]
  have hinverse : AnalyticAt ℂ (fun lambda => Ring.inverse (B lambda))
      lambda₀ := by
    have hinverseAtValue : AnalyticAt ℂ Ring.inverse (B lambda₀) := by
      rw [hBValue]
      exact analyticAt_inverse (𝕜 := ℂ)
        (1 : (RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
          RealHilbertComplexification (SignedGeneratorCarrier jet))ˣ)
    exact hinverseAtValue.comp hB
  unfold signedGeneratorLocalResolventState
  change AnalyticAt ℂ
    (fun lambda => Ring.inverse (B lambda)
      ((certificate.signedGeneratorResolventOperator
        lambda₀ hlambda₀) source)) lambda₀
  let applyMap :
      RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
        (RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
          RealHilbertComplexification (SignedGeneratorCarrier jet)) →L[ℂ]
            RealHilbertComplexification (SignedGeneratorCarrier jet) :=
    ContinuousLinearMap.apply ℂ
      (RealHilbertComplexification (SignedGeneratorCarrier jet))
  have heval := applyMap.analyticAt_bilinear
    ((certificate.signedGeneratorResolventOperator lambda₀ hlambda₀ source),
      Ring.inverse (B lambda₀))
  exact heval.comp (x := lambda₀) (analyticAt_const.prod hinverse)

/-- Near the chart centre, the local formula is represented by a domain
vector satisfying the exact signed-generator resolvent equation. -/
theorem eventually_signedGeneratorLocalResolventState_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda₀ : ℂ) (hlambda₀ : lambda₀.im ≠ 0)
    (source : RealHilbertComplexification (SignedGeneratorCarrier jet)) :
    ∀ᶠ lambda in nhds lambda₀,
      ∃ x : certificate.completedSignedGeneratorData.complexification.domain,
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
            certificate.signedGeneratorLocalResolventState
              lambda₀ hlambda₀ source lambda ∧
          certificate.SignedGeneratorResolventEquation lambda source x := by
  let A := certificate.completedSignedGeneratorData.complexification
  let R₀ := certificate.signedGeneratorResolventOperator lambda₀ hlambda₀
  let B : ℂ →
      (RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
        RealHilbertComplexification (SignedGeneratorCarrier jet)) :=
    fun lambda => 1 - (lambda - lambda₀) • R₀
  have hunit : ∀ᶠ lambda in nhds lambda₀, IsUnit (B lambda) := by
    have hB : ContinuousAt B lambda₀ := by fun_prop
    have hBValue : B lambda₀ = 1 := by simp [B]
    have hopen : {T | IsUnit T} ∈ nhds (B lambda₀) := by
      rw [hBValue]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hB.eventually hopen
  filter_upwards [hunit] with lambda hunitB
  let y : RealHilbertComplexification (SignedGeneratorCarrier jet) :=
    Ring.inverse (B lambda) source
  let p : A.graph := certificate.signedGeneratorGraphResolventInverse
    lambda₀ hlambda₀ y
  obtain ⟨x, hxp, hAxp⟩ := A.mem_graph_iff.mp p.property
  have hbase := certificate.signedGeneratorGraphResolventMap_inverse_apply
    lambda₀ hlambda₀ y
  change LinearPMap.graphResolventMap A lambda₀ p = y at hbase
  rw [LinearPMap.graphResolventMap_apply, ← hxp, ← hAxp] at hbase
  have hR₀y : R₀ y = p.1.1 := by rfl
  have hcommuteUnit : Commute (hunitB.unit :
      RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
        RealHilbertComplexification (SignedGeneratorCarrier jet)) R₀ := by
    simpa only [hunitB.unit_spec] using
      (LinearPMap.one_sub_smul_commutes R₀ (lambda - lambda₀))
  have hcommute : Commute (Ring.inverse (B lambda)) R₀ := by
    rw [← hunitB.unit_spec, Ring.inverse_unit]
    exact hcommuteUnit.units_inv_left
  have hcommuteApply :
      Ring.inverse (B lambda) (R₀ source) =
        R₀ (Ring.inverse (B lambda) source) := by
    have h := congrArg
      (fun T : RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
        RealHilbertComplexification (SignedGeneratorCarrier jet) => T source)
      hcommute.eq
    simpa using h
  refine ⟨x, ?_, ?_⟩
  · calc
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) = p.1.1 := hxp
      _ = R₀ y := hR₀y.symm
      _ = R₀ (Ring.inverse (B lambda) source) := rfl
      _ = Ring.inverse (B lambda) (R₀ source) := hcommuteApply.symm
      _ = certificate.signedGeneratorLocalResolventState
          lambda₀ hlambda₀ source lambda := by rfl
  · unfold SignedGeneratorResolventEquation
    change A x - lambda •
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) = source
    calc
      A x - lambda •
          (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
          (A x - lambda₀ •
            (x : RealHilbertComplexification (SignedGeneratorCarrier jet))) -
            (lambda - lambda₀) •
              (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) := by
        module
      _ = y - (lambda - lambda₀) • (R₀ y) := by
        rw [hbase, hxp, ← hR₀y]
      _ = B lambda y := by simp [B]
      _ = B lambda (Ring.inverse (B lambda) source) := rfl
      _ = source := by
        have hinverse : B lambda * Ring.inverse (B lambda) = 1 :=
          Ring.mul_inverse_cancel (B lambda) hunitB
        have happ := congrArg
          (fun T : RealHilbertComplexification (SignedGeneratorCarrier jet) →L[ℂ]
            RealHilbertComplexification (SignedGeneratorCarrier jet) => T source)
          hinverse
        simpa using happ

/-- The signed-generator resolvent equation is unique at a nonreal
parameter. -/
theorem signedGeneratorResolventEquation_unique
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : lambda.im ≠ 0)
    {source : RealHilbertComplexification (SignedGeneratorCarrier jet)}
    {x y : certificate.completedSignedGeneratorData.complexification.domain}
    (hx : certificate.SignedGeneratorResolventEquation lambda source x)
    (hy : certificate.SignedGeneratorResolventEquation lambda source y) :
    x = y := by
  let A := certificate.completedSignedGeneratorData.complexification
  have hinjective : Function.Injective
      (LinearPMap.graphResolventMap A lambda) :=
    LinearPMap.graphResolventMap_injective_of_isSelfAdjoint_of_im_ne_zero
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint
      hlambda
  let px : A.graph := ⟨((x : _), A x), A.mem_graph x⟩
  let py : A.graph := ⟨((y : _), A y), A.mem_graph y⟩
  have hmaps : LinearPMap.graphResolventMap A lambda px =
      LinearPMap.graphResolventMap A lambda py := by
    rw [LinearPMap.graphResolventMap_apply,
      LinearPMap.graphResolventMap_apply]
    exact hx.trans hy.symm
  have hp : px = py := hinjective hmaps
  apply Subtype.ext
  exact congrArg (fun p : A.graph => p.1.1) hp

/-- Canonical signed cyclic head in the complexified two-parity carrier. -/
def completedSignedGeneratorCyclicHead
    (_certificate : CompletedNativeRealHPCarrierCertificate jet) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) :=
  ComplexifiedOrbitResolvent.ofReal (completedSignedGeneratorOrbit jet 0)

/-- Height-coordinate graph equation `x - z Kx = e₀` for the same signed
generator whose local orbit germ was constructed above. -/
def SignedGeneratorHeightResolventEquation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ)
    (head : RealHilbertComplexification (SignedGeneratorCarrier jet))
    (x : certificate.completedSignedGeneratorData.complexification.domain) :
    Prop :=
  (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) -
      z • certificate.completedSignedGeneratorData.complexification x = head

/-- For nonzero height, the signed height equation is the standard resolvent
equation at `lambda = z⁻¹` with source `-lambda * head`. -/
theorem signedGeneratorHeightResolventEquation_iff
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hz : z ≠ 0)
    (head : RealHilbertComplexification (SignedGeneratorCarrier jet))
    (x : certificate.completedSignedGeneratorData.complexification.domain) :
    certificate.SignedGeneratorHeightResolventEquation z head x ↔
      certificate.SignedGeneratorResolventEquation z⁻¹
        (-(z⁻¹ • head)) x := by
  let A := certificate.completedSignedGeneratorData.complexification
  have hmul : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have hinvmul : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  constructor
  · intro hheight
    unfold SignedGeneratorHeightResolventEquation at hheight
    unfold SignedGeneratorResolventEquation
    change A x - z⁻¹ •
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
      -(z⁻¹ • head)
    have hscaled := congrArg
      (fun v : RealHilbertComplexification (SignedGeneratorCarrier jet) =>
        z⁻¹ • v) hheight
    rw [smul_sub z⁻¹
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet))
      (z • A x)] at hscaled
    rw [smul_smul z⁻¹ z (A x), hinvmul, one_smul] at hscaled
    rw [← hscaled]
    abel
  · intro hresolvent
    unfold SignedGeneratorResolventEquation at hresolvent
    unfold SignedGeneratorHeightResolventEquation
    change (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) -
        z • A x = head
    have hscaled := congrArg
      (fun v : RealHilbertComplexification (SignedGeneratorCarrier jet) =>
        z • v) hresolvent
    rw [smul_sub z (A x)
      (z⁻¹ • (x : RealHilbertComplexification (SignedGeneratorCarrier jet)))]
      at hscaled
    rw [smul_smul z z⁻¹
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet)),
      smul_neg z (z⁻¹ • head), smul_smul z z⁻¹ head,
      hmul, one_smul] at hscaled
    have hscaled' : z • A x -
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
          -head := by
      simpa only [one_smul] using hscaled
    calc
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) - z • A x =
          -(z • A x -
            (x : RealHilbertComplexification (SignedGeneratorCarrier jet))) := by
        abel
      _ = -(-head) := congrArg Neg.neg hscaled'
      _ = head := neg_neg head

/-- Unique global height-resolvent vector of the signed generator at every
off-axis height. -/
def signedGeneratorHeightGlobalResolventVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.completedSignedGeneratorData.complexification.domain :=
  (certificate.hasGlobalSignedGeneratorResolventAt_of_im_ne_zero
    (complex_inv_im_ne_zero hz)
    (-(z⁻¹ • certificate.completedSignedGeneratorCyclicHead))).choose

/-- The selected global vector satisfies `x - z Kx = e₀`. -/
theorem signedGeneratorHeightGlobalResolventVector_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.SignedGeneratorHeightResolventEquation z
      certificate.completedSignedGeneratorCyclicHead
      (certificate.signedGeneratorHeightGlobalResolventVector z hz) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  apply (certificate.signedGeneratorHeightResolventEquation_iff hz0
    certificate.completedSignedGeneratorCyclicHead _).2
  exact (certificate.hasGlobalSignedGeneratorResolventAt_of_im_ne_zero
    (complex_inv_im_ne_zero hz)
    (-(z⁻¹ • certificate.completedSignedGeneratorCyclicHead))).choose_spec

/-- Any domain vector satisfying the same height equation is the selected
global signed-generator resolvent vector. -/
theorem signedGeneratorHeightGlobalResolventVector_unique
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0)
    (candidate :
      certificate.completedSignedGeneratorData.complexification.domain)
    (hcandidate : certificate.SignedGeneratorHeightResolventEquation z
      certificate.completedSignedGeneratorCyclicHead candidate) :
    candidate = certificate.signedGeneratorHeightGlobalResolventVector z hz := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  apply certificate.signedGeneratorResolventEquation_unique
    (complex_inv_im_ne_zero hz)
  · exact (certificate.signedGeneratorHeightResolventEquation_iff hz0
      certificate.completedSignedGeneratorCyclicHead candidate).1 hcandidate
  · exact (certificate.signedGeneratorHeightResolventEquation_iff hz0
      certificate.completedSignedGeneratorCyclicHead _).1
      (certificate.signedGeneratorHeightGlobalResolventVector_equation z hz)

/-! ## Analytic gluing to the native Weyl germ -/

/-- Local height chart obtained from the standard signed-generator resolvent
by `lambda = z⁻¹` and source scaling by `-lambda`. -/
def signedGeneratorLocalHeightResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) (z : ℂ) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) :=
  -(z⁻¹) • certificate.signedGeneratorLocalResolventState
    z₀⁻¹ (complex_inv_im_ne_zero hz₀)
    certificate.completedSignedGeneratorCyclicHead z⁻¹

/-- The local height chart is analytic at every off-axis centre. -/
theorem signedGeneratorLocalHeightResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ
      (certificate.signedGeneratorLocalHeightResolventState z₀ hz₀) z₀ := by
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    subst z₀
    exact hz₀ rfl
  have hid : AnalyticAt ℂ (fun z : ℂ => z) z₀ := analyticAt_id
  have hlambda : AnalyticAt ℂ (fun z : ℂ => z⁻¹) z₀ :=
    hid.fun_inv hz₀ne
  have hstate := certificate.signedGeneratorLocalResolventState_analyticAt
    z₀⁻¹ (complex_inv_im_ne_zero hz₀)
    certificate.completedSignedGeneratorCyclicHead
  have hcomp := hstate.comp (x := z₀) hlambda
  have hscalar : AnalyticAt ℂ (fun z : ℂ => -(z⁻¹)) z₀ :=
    hlambda.neg
  unfold signedGeneratorLocalHeightResolventState
  change AnalyticAt ℂ
    (fun z : ℂ => -(z⁻¹) •
      certificate.signedGeneratorLocalResolventState
        z₀⁻¹ (complex_inv_im_ne_zero hz₀)
        certificate.completedSignedGeneratorCyclicHead z⁻¹) z₀
  exact (hscalar.smul hcomp).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Near an off-axis centre, the local height chart is represented by a
domain vector satisfying `x - z Kx = e₀`. -/
theorem eventually_signedGeneratorLocalHeightResolventState_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    ∀ᶠ z in nhds z₀,
      ∃ x : certificate.completedSignedGeneratorData.complexification.domain,
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) =
            certificate.signedGeneratorLocalHeightResolventState z₀ hz₀ z ∧
          certificate.SignedGeneratorHeightResolventEquation z
            certificate.completedSignedGeneratorCyclicHead x := by
  let lambda : ℂ → ℂ := fun z => z⁻¹
  have hz₀ne : z₀ ≠ 0 := by
    intro hzero
    subst z₀
    exact hz₀ rfl
  have hid : AnalyticAt ℂ (fun z : ℂ => z) z₀ := analyticAt_id
  have hlambdaContinuous : Tendsto lambda (nhds z₀) (nhds (lambda z₀)) :=
    (hid.fun_inv hz₀ne).continuousAt
  have hequation := hlambdaContinuous.eventually
    (certificate.eventually_signedGeneratorLocalResolventState_equation
      (lambda z₀) (complex_inv_im_ne_zero hz₀)
      certificate.completedSignedGeneratorCyclicHead)
  have hzne : ∀ᶠ z : ℂ in nhds z₀, z ≠ 0 :=
    continuousAt_id.eventually_ne hz₀ne
  filter_upwards [hequation, hzne] with z hlocal hz
  obtain ⟨x, hxState, hxEquation⟩ := hlocal
  let c : ℂ := -(lambda z)
  let scaled : certificate.completedSignedGeneratorData.complexification.domain :=
    c • x
  have hscaledEquation : certificate.SignedGeneratorResolventEquation
      (lambda z) (c • certificate.completedSignedGeneratorCyclicHead) scaled := by
    unfold SignedGeneratorResolventEquation at hxEquation ⊢
    change certificate.completedSignedGeneratorData.complexification (c • x) -
        lambda z •
          ((c • x : certificate.completedSignedGeneratorData.complexification.domain) :
            RealHilbertComplexification (SignedGeneratorCarrier jet)) =
      c • certificate.completedSignedGeneratorCyclicHead
    rw [LinearPMap.map_smul]
    rw [Submodule.coe_smul, smul_smul, mul_comm (lambda z) c,
      ← smul_smul, ← smul_sub]
    exact congrArg (fun v => c • v) hxEquation
  refine ⟨scaled, ?_, ?_⟩
  · change c •
      (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) = _
    rw [hxState]
    rfl
  · apply (certificate.signedGeneratorHeightResolventEquation_iff
      hz certificate.completedSignedGeneratorCyclicHead scaled).2
    have hsource : c • certificate.completedSignedGeneratorCyclicHead =
        -((lambda z) • certificate.completedSignedGeneratorCyclicHead) :=
      neg_smul (lambda z) certificate.completedSignedGeneratorCyclicHead
    rw [← hsource]
    exact hscaledEquation

/-- Total global signed-generator height state, extended by zero on the real
axis only to remove proof arguments from analytic statements. -/
def signedGeneratorHeightGlobalResolventState
    (certificate : CompletedNativeRealHPCarrierCertificate jet) (z : ℂ) :
    RealHilbertComplexification (SignedGeneratorCarrier jet) :=
  if hz : z.im ≠ 0 then
    certificate.signedGeneratorHeightGlobalResolventVector z hz
  else 0

/-- Local charts and the global signed state coincide by resolvent
uniqueness. -/
theorem signedGeneratorHeightGlobalResolventState_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ certificate.signedGeneratorHeightGlobalResolventState z₀ := by
  have him : ∀ᶠ z : ℂ in nhds z₀, z.im ≠ 0 :=
    Complex.continuous_im.continuousAt.eventually_ne hz₀
  have hlocal :=
    certificate.eventually_signedGeneratorLocalHeightResolventState_equation
      z₀ hz₀
  apply (certificate.signedGeneratorLocalHeightResolventState_analyticAt
    z₀ hz₀).congr
  filter_upwards [him, hlocal] with z hz hcandidate
  obtain ⟨x, hxState, hxEquation⟩ := hcandidate
  have hunique := certificate.signedGeneratorHeightGlobalResolventVector_unique
    z hz x hxEquation
  rw [signedGeneratorHeightGlobalResolventState, dif_pos hz, ← hunique]
  exact hxState.symm

/-- Proof-independent cyclic readout of the global signed-generator state. -/
def signedGeneratorHeightGlobalBoundaryReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet) (z : ℂ) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout
    (completedSignedGeneratorOrbit jet 0)
    (certificate.signedGeneratorHeightGlobalResolventState z)

/-- The global signed-generator readout is analytic at every off-axis
height. -/
theorem signedGeneratorHeightGlobalBoundaryReadout_analyticAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ certificate.signedGeneratorHeightGlobalBoundaryReadout z₀ := by
  have hstate :=
    certificate.signedGeneratorHeightGlobalResolventState_analyticAt z₀ hz₀
  have hinner : AnalyticAt ℂ
      (ComplexifiedOrbitResolvent.headReadout
        (completedSignedGeneratorOrbit jet 0))
      (certificate.signedGeneratorHeightGlobalResolventState z₀) :=
    (ComplexifiedOrbitResolvent.headReadout
      (completedSignedGeneratorOrbit jet 0)).analyticAt _
  exact (hinner.comp (x := z₀) hstate).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Near the Taylor centre and off the real axis, the global signed readout is
the native Weyl germ. -/
theorem signedGeneratorHeightGlobalBoundaryReadout_eventuallyEq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.signedGeneratorHeightGlobalBoundaryReadout =ᶠ[
      nhdsWithin 0 {z : ℂ | z.im ≠ 0}]
      completedNativeJacobiWeylHeightContinuation := by
  let A := certificate.completedSignedGeneratorData.complexification
  let germ := certificate.completedSignedGeneratorComplexGraphResolvent_germ
  filter_upwards
      [germ.eventually_mem_graph.filter_mono nhdsWithin_le_nhds,
        germ.eventually_resolventEquation.filter_mono nhdsWithin_le_nhds,
        germ.eventually_readout_eq.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z hzGraph hzEquation hzReadout hz
  obtain ⟨x, hxFirst, hxSecond⟩ := A.mem_graph_iff.mp hzGraph
  have hxHeight : certificate.SignedGeneratorHeightResolventEquation z
      certificate.completedSignedGeneratorCyclicHead x := by
    unfold SignedGeneratorHeightResolventEquation
    change (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) -
      z • A x = certificate.completedSignedGeneratorCyclicHead
    rw [hxFirst, hxSecond]
    exact hzEquation
  have hunique := certificate.signedGeneratorHeightGlobalResolventVector_unique
    z hz x hxHeight
  calc
    certificate.signedGeneratorHeightGlobalBoundaryReadout z =
        ComplexifiedOrbitResolvent.headReadout
          (completedSignedGeneratorOrbit jet 0) x := by
      rw [signedGeneratorHeightGlobalBoundaryReadout,
        signedGeneratorHeightGlobalResolventState, dif_pos hz, ← hunique]
    _ = germ.readout (germ.graphResolvent z) := by
      rw [hxFirst]
      rfl
    _ = completedNativeJacobiWeylHeightContinuation z := hzReadout

/-- Signed-generator readout glued to the native germ on the real axis. -/
def signedGeneratorHeightGluedBoundaryReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet) (z : ℂ) : ℂ :=
  if z.im = 0 then completedNativeJacobiWeylHeightContinuation z
  else certificate.signedGeneratorHeightGlobalBoundaryReadout z

/-- The glued signed readout equals the native Weyl germ in a full
neighborhood of zero. -/
theorem signedGeneratorHeightGluedBoundaryReadout_eventuallyEq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.signedGeneratorHeightGluedBoundaryReadout =ᶠ[nhds 0]
      completedNativeJacobiWeylHeightContinuation := by
  let A := certificate.completedSignedGeneratorData.complexification
  let germ := certificate.completedSignedGeneratorComplexGraphResolvent_germ
  filter_upwards [germ.eventually_mem_graph,
    germ.eventually_resolventEquation, germ.eventually_readout_eq] with
      z hzGraph hzEquation hzReadout
  by_cases hz : z.im = 0
  · simp [signedGeneratorHeightGluedBoundaryReadout, hz]
  · obtain ⟨x, hxFirst, hxSecond⟩ := A.mem_graph_iff.mp hzGraph
    have hxHeight : certificate.SignedGeneratorHeightResolventEquation z
        certificate.completedSignedGeneratorCyclicHead x := by
      unfold SignedGeneratorHeightResolventEquation
      change (x : RealHilbertComplexification (SignedGeneratorCarrier jet)) -
        z • A x = certificate.completedSignedGeneratorCyclicHead
      rw [hxFirst, hxSecond]
      exact hzEquation
    have hunique := certificate.signedGeneratorHeightGlobalResolventVector_unique
      z hz x hxHeight
    rw [signedGeneratorHeightGluedBoundaryReadout, if_neg hz,
      signedGeneratorHeightGlobalBoundaryReadout,
      signedGeneratorHeightGlobalResolventState, dif_pos hz, ← hunique]
    calc
      ComplexifiedOrbitResolvent.headReadout
          (completedSignedGeneratorOrbit jet 0) x =
          germ.readout (germ.graphResolvent z) := by
        rw [hxFirst]
        rfl
      _ = completedNativeJacobiWeylHeightContinuation z := hzReadout

theorem signedGeneratorHeightGluedBoundaryReadout_analyticAt_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticAt ℂ certificate.signedGeneratorHeightGluedBoundaryReadout 0 :=
  completedNativeJacobiWeylHeightContinuation_analyticAt_zero.congr
    certificate.signedGeneratorHeightGluedBoundaryReadout_eventuallyEq_weyl.symm

theorem signedGeneratorHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀ : z₀.im ≠ 0) :
    AnalyticAt ℂ certificate.signedGeneratorHeightGluedBoundaryReadout z₀ := by
  apply (certificate.signedGeneratorHeightGlobalBoundaryReadout_analyticAt
    z₀ hz₀).congr
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hz₀] with z hz
  simp [signedGeneratorHeightGluedBoundaryReadout, hz]

/-! ## Division-free native ODE and confinement -/

/-- Division-free ODE defect formed with the global signed-generator
readout. -/
def signedGeneratorWeylODEDefect
    (certificate : CompletedNativeRealHPCarrierCertificate jet) (z : ℂ) : ℂ :=
  ((2 : ℂ) * z) * certificate.signedGeneratorHeightGluedBoundaryReadout z *
      completedNativeOperatorCharacteristic z +
    deriv completedNativeOperatorCharacteristic z

theorem signedGeneratorWeylODEDefect_analyticOnNhd_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticOnNhd ℂ certificate.signedGeneratorWeylODEDefect
      completedNativeUpperHeightCone := by
  intro z hz
  have hF := completedNativeOperatorCharacteristic_analyticAt
    (completedNativeUpperHeightCone_subset_heightDomain hz)
  have hm : AnalyticAt ℂ
      certificate.signedGeneratorHeightGluedBoundaryReadout z := by
    rcases hz with rfl | hz
    · exact certificate.signedGeneratorHeightGluedBoundaryReadout_analyticAt_zero
    · exact certificate.signedGeneratorHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_gt hz.1)
  have hzMap : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by
    fun_prop
  exact (((hzMap.mul hm).mul hF).add hF.deriv).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The signed-generator ODE defect vanishes in a full neighborhood of the
Taylor centre. -/
theorem signedGeneratorWeylODEDefect_eventuallyEq_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    certificate.signedGeneratorWeylODEDefect =ᶠ[nhds 0] 0 := by
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hFne : ∀ᶠ z : ℂ in nhds 0,
      completedNativeOperatorCharacteristic z ≠ 0 :=
    (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).continuousAt.eventually_ne hF0
  have hderiv0 : deriv completedNativeOperatorCharacteristic 0 = 0 := by
    have hlog :=
      completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate.self_of_nhds
    have hquot :
        -deriv completedNativeOperatorCharacteristic 0 /
            completedNativeOperatorCharacteristic 0 = 0 := by
      simpa [completedNativeOperatorLogDerivative] using hlog
    have hneg : -deriv completedNativeOperatorCharacteristic 0 = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right hF0
    exact neg_eq_zero.mp hneg
  filter_upwards
      [certificate.signedGeneratorHeightGluedBoundaryReadout_eventuallyEq_weyl,
        hFne] with z hreadout hFz
  change certificate.signedGeneratorWeylODEDefect z = (0 : ℂ)
  by_cases hz : z = 0
  · subst z
    simp [signedGeneratorWeylODEDefect, hderiv0]
  · rw [signedGeneratorWeylODEDefect, hreadout,
      completedNativeJacobiWeylHeightContinuation, if_neg hz,
      completedNativeOperatorLogDerivative]
    field_simp [hz, hFz]
    ring

theorem signedGeneratorWeylODEDefect_eq_zero_on_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    Set.EqOn certificate.signedGeneratorWeylODEDefect 0
      completedNativeUpperHeightCone :=
  certificate.signedGeneratorWeylODEDefect_analyticOnNhd_upper
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_completedNativeUpperHeightCone
      zero_mem_completedNativeUpperHeightCone
      certificate.signedGeneratorWeylODEDefect_eventuallyEq_zero

theorem signedGeneratorWeylODEDefect_analyticOnNhd_lower
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    AnalyticOnNhd ℂ certificate.signedGeneratorWeylODEDefect
      completedNativeLowerHeightCone := by
  intro z hz
  have hF := completedNativeOperatorCharacteristic_analyticAt
    (completedNativeLowerHeightCone_subset_heightDomain hz)
  have hm : AnalyticAt ℂ
      certificate.signedGeneratorHeightGluedBoundaryReadout z := by
    rcases hz with rfl | hz
    · exact certificate.signedGeneratorHeightGluedBoundaryReadout_analyticAt_zero
    · exact certificate.signedGeneratorHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
        z (ne_of_lt hz.2)
  have hzMap : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by
    fun_prop
  exact (((hzMap.mul hm).mul hF).add hF.deriv).congr
    (Filter.Eventually.of_forall fun _ => rfl)

theorem signedGeneratorWeylODEDefect_eq_zero_on_lower
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    Set.EqOn certificate.signedGeneratorWeylODEDefect 0
      completedNativeLowerHeightCone :=
  certificate.signedGeneratorWeylODEDefect_analyticOnNhd_lower
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_completedNativeLowerHeightCone
      zero_mem_completedNativeLowerHeightCone
      certificate.signedGeneratorWeylODEDefect_eventuallyEq_zero

/-- At an off-axis point, local vanishing of the signed-generator ODE defect
is incompatible with a zero of the native characteristic. -/
theorem completedNativeOperatorCharacteristic_ne_zero_of_signedGeneratorDefect
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (him : z.im ≠ 0)
    (hdefect : ∀ᶠ w : ℂ in nhds z,
      certificate.signedGeneratorWeylODEDefect w = 0) :
    completedNativeOperatorCharacteristic z ≠ 0 := by
  intro hzero
  have hF := completedNativeOperatorCharacteristic_analyticAt hzDomain
  have hFne : ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
      completedNativeOperatorCharacteristic w ≠ 0 :=
    hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
  have hlogEq : completedNativeOperatorLogDerivative =ᶠ[nhdsWithin z {z}ᶜ]
      fun w => ((2 : ℂ) * w) *
        certificate.signedGeneratorHeightGluedBoundaryReadout w := by
    filter_upwards [hFne, hdefect.filter_mono nhdsWithin_le_nhds] with
        w hFw hdefectw
    unfold completedNativeOperatorLogDerivative
    apply (div_eq_iff hFw).2
    unfold signedGeneratorWeylODEDefect at hdefectw
    linear_combination -hdefectw
  have hm :=
    certificate.signedGeneratorHeightGluedBoundaryReadout_analyticAt_of_im_ne_zero
      z him
  have hfactor : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by
    fun_prop
  have hrhs : AnalyticAt ℂ
      (fun w => ((2 : ℂ) * w) *
        certificate.signedGeneratorHeightGluedBoundaryReadout w) z :=
    hfactor.mul hm
  have horder := meromorphicOrderAt_congr hlogEq
  rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
    hzDomain hzero] at horder
  have hnonneg := hrhs.meromorphicOrderAt_nonneg
  rw [← horder] at hnonneg
  exact (not_le_of_gt
    (show ((-1 : ℤ) : WithTop ℤ) < 0 by
      exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hnonneg

set_option maxHeartbeats 800000 in
/-- Direct signed-generator Hilbert--Polya confinement.  The conclusion uses
the maximal self-adjoint signed generator and its global nonreal resolvent;
no positive-Jacobi resolvent theorem or external continuation hypothesis is
used. -/
theorem completedNativeOperator_zero_im_eq_zero_of_signedGeneratorResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  by_contra him
  have hbounds := mem_completedNativeHeightDomain_iff_im_bounds.mp hzDomain
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hLower : -((1 : ℝ) / 2) < z.im ∧ z.im < 0 :=
      ⟨hbounds.1, hneg⟩
    have hLowerOpen : IsOpen {w : ℂ |
        -((1 : ℝ) / 2) < w.im ∧ w.im < 0} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have hdefect : ∀ᶠ w : ℂ in nhds z,
        certificate.signedGeneratorWeylODEDefect w = 0 := by
      filter_upwards [hLowerOpen.mem_nhds hLower] with w hw
      exact certificate.signedGeneratorWeylODEDefect_eq_zero_on_lower
        (Or.inr hw)
    exact certificate.completedNativeOperatorCharacteristic_ne_zero_of_signedGeneratorDefect
      hzDomain him hdefect hzero
  · have hUpper : 0 < z.im ∧ z.im < (1 : ℝ) / 2 :=
      ⟨hpos, hbounds.2⟩
    have hUpperOpen : IsOpen {w : ℂ |
        0 < w.im ∧ w.im < (1 : ℝ) / 2} :=
      (isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have hdefect : ∀ᶠ w : ℂ in nhds z,
        certificate.signedGeneratorWeylODEDefect w = 0 := by
      filter_upwards [hUpperOpen.mem_nhds hUpper] with w hw
      exact certificate.signedGeneratorWeylODEDefect_eq_zero_on_upper
        (Or.inr hw)
    exact certificate.completedNativeOperatorCharacteristic_ne_zero_of_signedGeneratorDefect
      hzDomain him hdefect hzero

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
