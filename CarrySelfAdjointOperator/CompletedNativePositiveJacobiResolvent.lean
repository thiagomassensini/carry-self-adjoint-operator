import CarrySelfAdjointOperator.CompletedNativeHPGateAudit
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic

/-!
# Global resolvent interface for the completed positive Jacobi operator

The completed Jacobi energy operator is already constructed as the maximal
positive self-adjoint square `B* B`.  This file does not construct another
operator.  It records the global resolvent equation for its existing complex
extension and proves uniqueness at every parameter outside the nonnegative
real axis.  In particular, the reciprocal-square parameter `(z^2)⁻¹` is in
that region whenever the centered height `z` is off the real axis.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The bounded map from the closed graph of a partial operator to the
standard resolvent defect `A x - lambda x`. -/
def graphResolventMap (A : H →ₗ.[ℂ] H) (lambda : ℂ) :
    A.graph →L[ℂ] H :=
  (ContinuousLinearMap.snd ℂ H H -
      lambda • ContinuousLinearMap.fst ℂ H H).comp
    A.graph.subtypeL

@[simp] theorem graphResolventMap_apply
    (A : H →ₗ.[ℂ] H) (lambda : ℂ) (p : A.graph) :
    graphResolventMap A lambda p = p.1.2 - lambda • p.1.1 :=
  rfl

/-- The imaginary part of a nonreal spectral parameter controls the norm of
a domain vector through the resolvent defect of a symmetric operator. -/
theorem abs_im_mul_norm_le_norm_resolventDefect
    {A : H →ₗ.[ℂ] H} (hformal : A.IsFormalAdjoint A)
    (lambda : ℂ) (x : A.domain) :
    |lambda.im| * ‖(x : H)‖ ≤ ‖A x - lambda • (x : H)‖ := by
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
  have himDefect :
      (inner ℂ (A x - lambda • (x : H)) (x : H)).im =
        lambda.im * ‖(x : H)‖ ^ 2 := by
    have hxre : (inner ℂ (x : H) (x : H)).re = ‖(x : H)‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x : H))
    have hxim : (inner ℂ (x : H) (x : H)).im = 0 := by
      simpa using (inner_self_im (𝕜 := ℂ) (x : H))
    rw [inner_sub_left, inner_smul_left]
    rw [Complex.sub_im, Complex.mul_im, starRingEnd_apply,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      hxre, hxim, himA]
    ring
  have hproduct :
      |lambda.im| * ‖(x : H)‖ ^ 2 ≤
        ‖A x - lambda • (x : H)‖ * ‖(x : H)‖ := by
    calc
      |lambda.im| * ‖(x : H)‖ ^ 2 =
          |(inner ℂ (A x - lambda • (x : H)) (x : H)).im| := by
        simp [himDefect, abs_mul]
      _ ≤ ‖inner ℂ (A x - lambda • (x : H)) (x : H)‖ :=
        Complex.abs_im_le_norm _
      _ ≤ ‖A x - lambda • (x : H)‖ * ‖(x : H)‖ :=
        norm_inner_le_norm _ _
  by_cases hx : (x : H) = 0
  · simp [hx]
  · have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx
    nlinarith

/-- Positivity gives the analogous lower resolvent bound on the negative real
axis. -/
theorem neg_re_mul_norm_le_norm_resolventDefect
    {A : H →ₗ.[ℂ] H}
    (hpositive : ∀ x : A.domain,
      0 ≤ (inner ℂ (A x) (x : H)).re)
    {lambda : ℂ} (_hlambda : lambda.re < 0) (x : A.domain) :
    -lambda.re * ‖(x : H)‖ ≤ ‖A x - lambda • (x : H)‖ := by
  have hreDefect :
      (inner ℂ (A x - lambda • (x : H)) (x : H)).re =
        (inner ℂ (A x) (x : H)).re -
          lambda.re * ‖(x : H)‖ ^ 2 := by
    have hxre : (inner ℂ (x : H) (x : H)).re = ‖(x : H)‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x : H))
    have hxim : (inner ℂ (x : H) (x : H)).im = 0 := by
      simpa using (inner_self_im (𝕜 := ℂ) (x : H))
    rw [inner_sub_left, inner_smul_left]
    rw [Complex.sub_re, Complex.mul_re, starRingEnd_apply,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      hxre, hxim]
    ring
  have hproduct :
      -lambda.re * ‖(x : H)‖ ^ 2 ≤
        ‖A x - lambda • (x : H)‖ * ‖(x : H)‖ := by
    calc
      -lambda.re * ‖(x : H)‖ ^ 2 ≤
          (inner ℂ (A x - lambda • (x : H)) (x : H)).re := by
        rw [hreDefect]
        linarith [hpositive x]
      _ ≤ |(inner ℂ (A x - lambda • (x : H)) (x : H)).re| :=
        le_abs_self _
      _ ≤ ‖inner ℂ (A x - lambda • (x : H)) (x : H)‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖A x - lambda • (x : H)‖ * ‖(x : H)‖ :=
        norm_inner_le_norm _ _
  by_cases hx : (x : H) = 0
  · simp [hx]
  · have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx
    nlinarith

/-- A coercive estimate on domain vectors controls the full closed-graph norm
of the resolvent defect map. -/
theorem graphResolventMap_antilipschitz
    (A : H →ₗ.[ℂ] H) (lambda : ℂ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hbound : ∀ x : A.domain,
      delta * ‖(x : H)‖ ≤ ‖A x - lambda • (x : H)‖) :
    AntilipschitzWith
      ⟨1 + (1 + ‖lambda‖) / delta, by positivity⟩
      (graphResolventMap A lambda) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  rintro ⟨⟨u, v⟩, hp⟩
  obtain ⟨x, hxu, hxv⟩ := A.mem_graph_iff.mp hp
  change (x : H) = u at hxu
  change A x = v at hxv
  subst u
  subst v
  have hxle :
      ‖(x : H)‖ ≤ ‖A x - lambda • (x : H)‖ / delta := by
    exact (le_div_iff₀ hdelta).2 (by
      simpa [mul_comm] using hbound x)
  have hAx :
      ‖A x‖ ≤ ‖A x - lambda • (x : H)‖ +
        ‖lambda‖ * ‖(x : H)‖ := by
    calc
      ‖A x‖ = ‖(A x - lambda • (x : H)) +
          lambda • (x : H)‖ := by congr 1; abel
      _ ≤ ‖A x - lambda • (x : H)‖ +
          ‖lambda • (x : H)‖ := norm_add_le _ _
      _ = ‖A x - lambda • (x : H)‖ +
          ‖lambda‖ * ‖(x : H)‖ := by rw [norm_smul]
  change max ‖(x : H)‖ ‖A x‖ ≤
    (1 + (1 + ‖lambda‖) / delta) *
      ‖A x - lambda • (x : H)‖
  apply max_le
  · calc
      ‖(x : H)‖ ≤
          ‖A x - lambda • (x : H)‖ / delta := hxle
      _ ≤ (1 + (1 + ‖lambda‖) / delta) *
          ‖A x - lambda • (x : H)‖ := by
        have hnorm : 0 ≤ ‖A x - lambda • (x : H)‖ := norm_nonneg _
        have hinv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
        have hnormInv :
            0 ≤ ‖A x - lambda • (x : H)‖ * delta⁻¹ :=
          mul_nonneg hnorm hinv
        have hlambdaNormInv :
            0 ≤ ‖lambda‖ *
              (‖A x - lambda • (x : H)‖ * delta⁻¹) :=
          mul_nonneg (norm_nonneg _) hnormInv
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith
  · calc
      ‖A x‖ ≤ ‖A x - lambda • (x : H)‖ +
          ‖lambda‖ * ‖(x : H)‖ := hAx
      _ ≤ ‖A x - lambda • (x : H)‖ +
          ‖lambda‖ *
            (‖A x - lambda • (x : H)‖ / delta) := by
        gcongr
      _ ≤ (1 + (1 + ‖lambda‖) / delta) *
          ‖A x - lambda • (x : H)‖ := by
        have hnorm : 0 ≤ ‖A x - lambda • (x : H)‖ := norm_nonneg _
        have hinv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
        have hnormInv :
            0 ≤ ‖A x - lambda • (x : H)‖ * delta⁻¹ :=
          mul_nonneg hnorm hinv
        have hlambdaNormInv :
            0 ≤ ‖lambda‖ *
              (‖A x - lambda • (x : H)‖ * delta⁻¹) :=
          mul_nonneg (norm_nonneg _) hnormInv
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith

/-- A vector orthogonal to the resolvent range of a self-adjoint operator is
an eigenvector at the conjugate parameter.  Thus absence of that eigenvalue
forces the orthogonal complement of the range to vanish. -/
theorem eq_zero_of_mem_graphResolventMap_range_orthogonal
    [CompleteSpace H] {A : H →ₗ.[ℂ] H}
    (hself : IsSelfAdjoint A) (lambda : ℂ)
    (hnoEigen : ¬ LinearPMap.HasEigenvalue A (starRingEnd ℂ lambda))
    {y : H}
    (hy : y ∈ (graphResolventMap A lambda).rangeᗮ) :
    y = 0 := by
  have horth : ∀ x : A.domain,
      inner ℂ (A x - lambda • (x : H)) y = 0 := by
    intro x
    simpa using
      ((Submodule.mem_orthogonal
        (K := (graphResolventMap A lambda).range) y).1 hy
        (graphResolventMap A lambda
          ⟨((x : H), A x), A.mem_graph x⟩)
        ⟨⟨((x : H), A x), A.mem_graph x⟩, rfl⟩)
  have hwitness : ∀ x : A.domain,
      inner ℂ ((starRingEnd ℂ lambda) • y) (x : H) =
        inner ℂ y (A x) := by
    intro x
    have hleft : inner ℂ (A x) y =
        inner ℂ (lambda • (x : H)) y := by
      apply sub_eq_zero.mp
      simpa only [inner_sub_left] using horth x
    have hright : inner ℂ y (A x) =
        inner ℂ y (lambda • (x : H)) := by
      calc
        inner ℂ y (A x) =
            (starRingEnd ℂ) (inner ℂ (A x) y) :=
          (inner_conj_symm y (A x)).symm
        _ = (starRingEnd ℂ)
            (inner ℂ (lambda • (x : H)) y) :=
          congrArg (starRingEnd ℂ) hleft
        _ = inner ℂ y (lambda • (x : H)) :=
          inner_conj_symm y (lambda • (x : H))
    calc
      inner ℂ ((starRingEnd ℂ lambda) • y) (x : H) =
          lambda * inner ℂ y (x : H) := by
        rw [inner_smul_left]
        change (star (star lambda)) * inner ℂ y (x : H) = _
        rw [star_star]
      _ = inner ℂ y (lambda • (x : H)) := by
        rw [inner_smul_right]
      _ = inner ℂ y (A x) := hright.symm
  have hyAdjointDomain : y ∈ A.adjoint.domain :=
    A.mem_adjoint_domain_of_exists y
      ⟨(starRingEnd ℂ lambda) • y, hwitness⟩
  have hselfEq : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hself
  have hyDomain : y ∈ A.domain := by
    rwa [hselfEq] at hyAdjointDomain
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [hselfEq] at hadjoint
    exact hadjoint
  have hAy : A ⟨y, hyDomain⟩ =
      (starRingEnd ℂ lambda) • y := by
    apply hself.dense_domain.eq_of_inner_left ℂ
    intro x hx
    let xDomain : A.domain := ⟨x, hx⟩
    calc
      inner ℂ (A ⟨y, hyDomain⟩) x =
          inner ℂ y (A xDomain) := hformal ⟨y, hyDomain⟩ xDomain
      _ = inner ℂ ((starRingEnd ℂ lambda) • y) x :=
        (hwitness xDomain).symm
  by_contra hy0
  exact hnoEigen ⟨⟨y, hyDomain⟩, hy0, hAy⟩

/-- Closed range plus vanishing orthogonal complement makes the graph
resolvent defect map onto.  This is the functional-analytic core of the
global resolvent theorem, stated independently of the concrete Jacobi model. -/
theorem graphResolventMap_surjective
    [CompleteSpace H] {A : H →ₗ.[ℂ] H}
    (hself : IsSelfAdjoint A)
    (hpositive : ∀ x : A.domain,
      0 ≤ (inner ℂ (A x) (x : H)).re)
    {lambda : ℂ}
    (hlambda : lambda.im ≠ 0 ∨ lambda.re < 0)
    (hnoEigen : ¬ LinearPMap.HasEigenvalue A (starRingEnd ℂ lambda)) :
    Function.Surjective (graphResolventMap A lambda) := by
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjoint
    exact hadjoint
  obtain ⟨delta, hdelta, hbound⟩ :
      ∃ delta : ℝ, 0 < delta ∧
        ∀ x : A.domain,
          delta * ‖(x : H)‖ ≤ ‖A x - lambda • (x : H)‖ := by
    rcases hlambda with him | hneg
    · exact ⟨|lambda.im|, abs_pos.mpr him,
        abs_im_mul_norm_le_norm_resolventDefect hformal lambda⟩
    · exact ⟨-lambda.re, neg_pos.mpr hneg,
        neg_re_mul_norm_le_norm_resolventDefect hpositive hneg⟩
  have hanti := graphResolventMap_antilipschitz
    A lambda hdelta hbound
  letI : CompleteSpace A.graph := hself.isClosed.completeSpace_coe
  have hRangeClosed : IsClosed
      ((graphResolventMap A lambda).range : Set H) := by
    change IsClosed (Set.range (graphResolventMap A lambda))
    exact hanti.isClosed_range
      (graphResolventMap A lambda).uniformContinuous
  letI : CompleteSpace (graphResolventMap A lambda).range :=
    hRangeClosed.completeSpace_coe
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

/-- A complex parameter lies outside the nonnegative real axis. -/
def OutsideNonnegativeRealAxis (lambda : ℂ) : Prop :=
  lambda.im ≠ 0 ∨ lambda.re < 0

/-- The reciprocal-square spectral parameter attached to an off-axis height
lies outside the nonnegative real axis. -/
theorem inv_sq_mem_outsideNonnegativeRealAxis
    {z : ℂ} (hz : z.im ≠ 0) :
    OutsideNonnegativeRealAxis (z ^ 2)⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  by_cases him : (z ^ 2)⁻¹.im = 0
  · right
    have hnot : ¬ 0 ≤ (z ^ 2)⁻¹.re := by
      intro hnonneg
      exact hz (complex_im_eq_zero_of_sq_inv_real_nonneg
        hz0 him hnonneg)
    exact lt_of_not_ge hnot
  · exact Or.inl him

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance positiveJacobiResolventEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- Positivity of the existing real Jacobi energy operator survives its
two-quadrature complexification without discarding either channel. -/
theorem completedJacobiEnergyComplexification_inner_re_nonneg
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
    0 ≤ (inner ℂ
      (certificate.completedJacobiEnergySelfAdjointData.complexification x)
      (x : RealHilbertComplexification (EvenCarrier jet))).re := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  change 0 ≤ (inner ℂ (data.complexification x)
    (x : RealHilbertComplexification (EvenCarrier jet))).re
  rw [RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner_re]
  simp only [LinearPMap.RealMaximalSelfAdjointData.complexification,
    LinearPMap.re_complexification_apply,
    LinearPMap.im_complexification_apply]
  exact add_nonneg
    (certificate.completedJacobiEnergyOperator_inner_nonneg
      (data.operator.complexificationDomainRe x))
    (certificate.completedJacobiEnergyOperator_inner_nonneg
      (data.operator.complexificationDomainIm x))

/-- The standard resolvent equation of the existing complexified positive
Jacobi operator. -/
def PositiveJacobiResolventEquation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ)
    (source : RealHilbertComplexification (EvenCarrier jet))
    (x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
    Prop :=
  certificate.completedJacobiEnergySelfAdjointData.complexification x -
      lambda •
        (x : RealHilbertComplexification (EvenCarrier jet)) =
    source

/-- A global resolvent point means that the existing Jacobi graph equation
has a solution for every ambient source.  Uniqueness is proved below from the
operator's positivity and self-adjointness, so it is not included as data. -/
def HasGlobalPositiveJacobiResolventAt
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (lambda : ℂ) : Prop :=
  ∀ source : RealHilbertComplexification (EvenCarrier jet),
    ∃ x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
      certificate.PositiveJacobiResolventEquation lambda source x

/-- The existing positive self-adjoint Jacobi energy operator has a global
resolvent at every complex parameter outside `[0, ∞)`. -/
theorem hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda) :
    certificate.HasGlobalPositiveJacobiResolventAt lambda := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  let A := data.complexification
  have hself : IsSelfAdjoint A :=
    data.complexification_isSelfAdjoint
  have hpositive : ∀ x : A.domain,
      0 ≤ (inner ℂ (A x)
        (x : RealHilbertComplexification (EvenCarrier jet))).re := by
    intro x
    exact certificate.completedJacobiEnergyComplexification_inner_re_nonneg x
  have hnoEigen :
      ¬ LinearPMap.HasEigenvalue A (starRingEnd ℂ lambda) := by
    intro heigen
    have hspectrum :=
      data.complexification_eigenvalue_real_nonneg
        certificate.completedJacobiEnergyOperator_inner_nonneg heigen
    rcases hlambda with him | hneg
    · apply him
      have hstarIm := hspectrum.1
      change -lambda.im = 0 at hstarIm
      linarith
    · have hstarRe := hspectrum.2
      change 0 ≤ lambda.re at hstarRe
      exact (not_lt_of_ge hstarRe) hneg
  have hsurjective : Function.Surjective
      (LinearPMap.graphResolventMap A lambda) :=
    LinearPMap.graphResolventMap_surjective
      hself hpositive hlambda hnoEigen
  intro source
  obtain ⟨p, hp⟩ := hsurjective source
  obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp p.property
  refine ⟨x, ?_⟩
  unfold PositiveJacobiResolventEquation
  change A x - lambda •
      (x : RealHilbertComplexification (EvenCarrier jet)) = source
  calc
    A x - lambda •
        (x : RealHilbertComplexification (EvenCarrier jet)) =
        LinearPMap.graphResolventMap A lambda p := by
      rw [LinearPMap.graphResolventMap_apply, ← hx, ← hAx]
    _ = source := hp

/-- Reciprocal-square specialization of the global resolvent theorem. -/
theorem hasGlobalPositiveJacobiResolventAt_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hz : z.im ≠ 0) :
    certificate.HasGlobalPositiveJacobiResolventAt (z ^ 2)⁻¹ :=
  certificate.hasGlobalPositiveJacobiResolventAt_of_outsideNonnegativeRealAxis
    (inv_sq_mem_outsideNonnegativeRealAxis hz)

/-- Height-coordinate graph equation for the same positive Jacobi operator.
The cyclic head is supplied separately so the equivalence with the standard
resolvent equation is transparent. -/
def PositiveJacobiHeightResolventEquation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ)
    (head : RealHilbertComplexification (EvenCarrier jet))
    (x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
    Prop :=
  (x : RealHilbertComplexification (EvenCarrier jet)) -
      z ^ 2 •
        certificate.completedJacobiEnergySelfAdjointData.complexification x =
    head

/-- For nonzero height, `x - z² A x = head` is exactly the standard
resolvent equation at `lambda = (z²)⁻¹` with source `-lambda head`. -/
theorem positiveJacobiHeightResolventEquation_iff
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hz : z ≠ 0)
    (head : RealHilbertComplexification (EvenCarrier jet))
    (x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
    certificate.PositiveJacobiHeightResolventEquation z head x ↔
      certificate.PositiveJacobiResolventEquation (z ^ 2)⁻¹
        (- (((z ^ 2)⁻¹) • head)) x := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  have hzsq : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hmul : z ^ 2 * (z ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hzsq
  have hinvmul : (z ^ 2)⁻¹ * z ^ 2 = 1 := inv_mul_cancel₀ hzsq
  constructor
  · intro hheight
    unfold PositiveJacobiHeightResolventEquation at hheight
    unfold PositiveJacobiResolventEquation
    change A x - (z ^ 2)⁻¹ •
        (x : RealHilbertComplexification (EvenCarrier jet)) =
      - (((z ^ 2)⁻¹) • head)
    have hscaled := congrArg
      (fun v : RealHilbertComplexification (EvenCarrier jet) ↦
        (z ^ 2)⁻¹ • v) hheight
    rw [smul_sub (z ^ 2)⁻¹
      (x : RealHilbertComplexification (EvenCarrier jet))
      (z ^ 2 • A x)] at hscaled
    rw [smul_smul (z ^ 2)⁻¹ (z ^ 2) (A x)] at hscaled
    rw [hinvmul, one_smul] at hscaled
    rw [← hscaled]
    abel
  · intro hresolvent
    unfold PositiveJacobiResolventEquation at hresolvent
    unfold PositiveJacobiHeightResolventEquation
    change (x : RealHilbertComplexification (EvenCarrier jet)) -
        z ^ 2 • A x = head
    have hscaled := congrArg
      (fun v : RealHilbertComplexification (EvenCarrier jet) ↦
        z ^ 2 • v) hresolvent
    rw [smul_sub (z ^ 2) (A x)
      ((z ^ 2)⁻¹ •
        (x : RealHilbertComplexification (EvenCarrier jet)))] at hscaled
    rw [smul_smul (z ^ 2) (z ^ 2)⁻¹
      (x : RealHilbertComplexification (EvenCarrier jet))] at hscaled
    rw [smul_neg (z ^ 2) ((z ^ 2)⁻¹ • head),
      smul_smul (z ^ 2) (z ^ 2)⁻¹ head] at hscaled
    rw [hmul, one_smul] at hscaled
    have hone : (1 : ℂ) • head = head := one_smul ℂ head
    rw [hone] at hscaled
    change z ^ 2 • A x -
      (x : RealHilbertComplexification (EvenCarrier jet)) = -head at hscaled
    calc
      (x : RealHilbertComplexification (EvenCarrier jet)) - z ^ 2 • A x =
          -(z ^ 2 • A x -
            (x : RealHilbertComplexification (EvenCarrier jet))) := by abel
      _ = -(-head) := congrArg Neg.neg hscaled
      _ = head := neg_neg head

/-- Outside the nonnegative real axis, two domain vectors satisfying the
same resolvent equation for the existing positive Jacobi operator coincide. -/
theorem positiveJacobiResolventEquation_unique
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda)
    {source : RealHilbertComplexification (EvenCarrier jet)}
    {x y : certificate.completedJacobiEnergySelfAdjointData.complexification.domain}
    (hx : certificate.PositiveJacobiResolventEquation lambda source x)
    (hy : certificate.PositiveJacobiResolventEquation lambda source y) :
    x = y := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  by_contra hxy
  have hsub :
      ((x - y : data.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet)) ≠ 0 := by
    intro hzero
    apply hxy
    apply Subtype.ext
    exact sub_eq_zero.mp hzero
  have heq :
      data.complexification (x - y) =
        lambda •
          ((x - y : data.complexification.domain) :
            RealHilbertComplexification (EvenCarrier jet)) := by
    unfold PositiveJacobiResolventEquation at hx hy
    calc
      data.complexification (x - y) =
          data.complexification x - data.complexification y :=
        data.complexification.map_sub x y
      _ = lambda • (x : RealHilbertComplexification (EvenCarrier jet)) -
          lambda • (y : RealHilbertComplexification (EvenCarrier jet)) := by
        have hx' : data.complexification x =
            source + lambda •
              (x : RealHilbertComplexification (EvenCarrier jet)) :=
          (sub_eq_iff_eq_add).mp hx
        have hy' : data.complexification y =
            source + lambda •
              (y : RealHilbertComplexification (EvenCarrier jet)) :=
          (sub_eq_iff_eq_add).mp hy
        rw [hx', hy']
        abel
      _ = lambda •
          ((x - y : data.complexification.domain) :
            RealHilbertComplexification (EvenCarrier jet)) := by
        exact (smul_sub lambda
          (x : RealHilbertComplexification (EvenCarrier jet))
          (y : RealHilbertComplexification (EvenCarrier jet))).symm
  have heigen : LinearPMap.HasEigenvalue data.complexification lambda :=
    ⟨x - y, hsub, heq⟩
  have hspectrum :=
    data.complexification_eigenvalue_real_nonneg
      certificate.completedJacobiEnergyOperator_inner_nonneg heigen
  rcases hlambda with him | hneg
  · exact him hspectrum.1
  · exact (not_lt_of_ge hspectrum.2) hneg

/-- At a global resolvent point outside the nonnegative real axis, every
source has a unique domain-valued resolvent vector. -/
theorem existsUnique_positiveJacobiResolvent
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda)
    (hglobal : certificate.HasGlobalPositiveJacobiResolventAt lambda)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    ∃! x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain,
      certificate.PositiveJacobiResolventEquation lambda source x := by
  obtain ⟨x, hx⟩ := hglobal source
  exact ⟨x, hx, fun y hy ↦
    certificate.positiveJacobiResolventEquation_unique hlambda hy hx⟩

/-- The global resolvent vector selected from the unique graph solution. -/
def positiveJacobiGlobalResolventVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda)
    (hglobal : certificate.HasGlobalPositiveJacobiResolventAt lambda)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
  (certificate.existsUnique_positiveJacobiResolvent
    hlambda hglobal source).choose

/-- The selected global vector satisfies the exact resolvent equation. -/
theorem positiveJacobiGlobalResolventVector_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : OutsideNonnegativeRealAxis lambda)
    (hglobal : certificate.HasGlobalPositiveJacobiResolventAt lambda)
    (source : RealHilbertComplexification (EvenCarrier jet)) :
    certificate.PositiveJacobiResolventEquation lambda source
      (certificate.positiveJacobiGlobalResolventVector
        hlambda hglobal source) :=
  (certificate.existsUnique_positiveJacobiResolvent
    hlambda hglobal source).choose_spec.1

/-- Canonical cyclic head of the already constructed completed Jacobi
operator, embedded in its complexification. -/
def positiveJacobiCyclicHead
    (_certificate : CompletedNativeRealHPCarrierCertificate jet) :
    RealHilbertComplexification (EvenCarrier jet) :=
  ComplexifiedOrbitResolvent.ofReal
    (completedJacobiOrbit jet 0)

/-- Global height-coordinate resolvent vector of the existing positive
Jacobi operator.  Its construction uses the proved global resolvent theorem,
not an additional continuation hypothesis. -/
def positiveJacobiHeightGlobalResolventVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
  certificate.positiveJacobiGlobalResolventVector
    (inv_sq_mem_outsideNonnegativeRealAxis hz)
    (certificate.hasGlobalPositiveJacobiResolventAt_inv_sq hz)
    (- (((z ^ 2)⁻¹) • certificate.positiveJacobiCyclicHead))

/-- The global vector satisfies the exact height graph equation
`x - z² A x = e₀`. -/
theorem positiveJacobiHeightGlobalResolventVector_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.PositiveJacobiHeightResolventEquation z
      certificate.positiveJacobiCyclicHead
      (certificate.positiveJacobiHeightGlobalResolventVector z hz) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  apply (certificate.positiveJacobiHeightResolventEquation_iff
    hz0 certificate.positiveJacobiCyclicHead
    (certificate.positiveJacobiHeightGlobalResolventVector z hz)).2
  exact certificate.positiveJacobiGlobalResolventVector_equation
    (inv_sq_mem_outsideNonnegativeRealAxis hz)
    (certificate.hasGlobalPositiveJacobiResolventAt_inv_sq hz)
    (- (((z ^ 2)⁻¹) • certificate.positiveJacobiCyclicHead))

/-- Any domain-valued candidate satisfying the same global height equation
is the canonical global resolvent vector.  This is the uniqueness statement
used to identify a transported Gamma field before taking a scalar readout. -/
theorem positiveJacobiHeightGlobalResolventVector_unique
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0)
    (candidate :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain)
    (hcandidate : certificate.PositiveJacobiHeightResolventEquation z
      certificate.positiveJacobiCyclicHead candidate) :
    candidate = certificate.positiveJacobiHeightGlobalResolventVector z hz := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz rfl
  apply certificate.positiveJacobiResolventEquation_unique
    (inv_sq_mem_outsideNonnegativeRealAxis hz)
  · exact (certificate.positiveJacobiHeightResolventEquation_iff
      hz0 certificate.positiveJacobiCyclicHead candidate).1 hcandidate
  · exact certificate.positiveJacobiGlobalResolventVector_equation
      (inv_sq_mem_outsideNonnegativeRealAxis hz)
      (certificate.hasGlobalPositiveJacobiResolventAt_inv_sq hz)
      (- (((z ^ 2)⁻¹) • certificate.positiveJacobiCyclicHead))

/-- Cyclic-head scalar readout of the global positive Jacobi resolvent. -/
def positiveJacobiHeightGlobalBoundaryReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) : ℂ :=
  ComplexifiedOrbitResolvent.headReadout
    (completedJacobiOrbit jet 0)
    (certificate.positiveJacobiHeightGlobalResolventVector z hz)

/-- Boundary identification by resolvent uniqueness: once a candidate Gamma
vector is shown to satisfy the same global Jacobi equation in this carrier,
its cyclic boundary readout is forced to be the global resolvent readout. -/
theorem positiveJacobiCandidateBoundaryReadout_eq_global
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0)
    (candidate :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain)
    (hcandidate : certificate.PositiveJacobiHeightResolventEquation z
      certificate.positiveJacobiCyclicHead candidate) :
    ComplexifiedOrbitResolvent.headReadout
        (completedJacobiOrbit jet 0) candidate =
      certificate.positiveJacobiHeightGlobalBoundaryReadout z hz := by
  rw [certificate.positiveJacobiHeightGlobalResolventVector_unique
    z hz candidate hcandidate]
  rfl

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
