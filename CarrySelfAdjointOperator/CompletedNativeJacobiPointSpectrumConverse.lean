import CarrySelfAdjointOperator.CompletedNativeJacobiCyclicAtomicExtraction

/-!
# Positive Jacobi point spectrum and native zeros

Cyclicity rules out eigenvectors invisible to the initial vector. At a nonzero
real height where the native characteristic is nonvanishing, the scaled cyclic
resolvent tends to zero. The eigenvector-resolvent identity then excludes a
point eigenvalue at the reciprocal square of that height.

All operator conclusions retain `CompletedNativeRealHPCarrierCertificate`.
-/

open Filter Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace CyclicPointSpectrum

/-- A dense real operator orbit detects every eigenvector of its
complexification. No assumption about the rest of the spectrum is needed. -/
theorem eigenvector_visible_of_real_cyclicOrbit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E) (v : ℕ → E)
    (hdense : Dense (Submodule.span ℝ (Set.range v) : Set E))
    (horbit : ∀ n : ℕ, ∃ x : A.domain,
      (x : E) = v n ∧ A x = v (n + 1))
    (hformal : A.complexification.IsFormalAdjoint A.complexification)
    {mu : ℂ} (x : A.complexification.domain)
    (hx : (x : RealHilbertComplexification E) ≠ 0)
    (hAx : A.complexification x = mu • (x : RealHilbertComplexification E)) :
    inner ℂ (x : RealHilbertComplexification E)
      (ComplexifiedOrbitResolvent.ofReal (v 0)) ≠ 0 := by
  intro hhead
  have horth : ∀ n : ℕ, inner ℂ (x : RealHilbertComplexification E)
      (ComplexifiedOrbitResolvent.ofReal (v n)) = 0 := by
    intro n
    induction n with
    | zero => exact hhead
    | succ n ih =>
      have hgraph := ComplexifiedOrbitResolvent.ofReal_pair_mem_complexification_graph
        A horbit n
      rw [LinearPMap.mem_graph_iff] at hgraph
      obtain ⟨y, hy, hAy⟩ := hgraph
      have h := hformal x y
      rw [hAx, inner_smul_left, hy, hAy, ih, mul_zero] at h
      exact h.symm
  have hre : RealHilbertComplexification.re (x : RealHilbertComplexification E) = 0 := by
    apply hdense.eq_zero_of_inner_left ℝ
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      have h := congrArg Complex.re (horth n)
      simpa [RealHilbertComplexification.inner_apply,
        RealHilbertComplexification.complexInner,
        ComplexifiedOrbitResolvent.ofReal] using h
    | zero => simp
    | add z w hz hw hz0 hw0 => simp [inner_add_right, hz0, hw0]
    | smul c z hz hz0 => simp [real_inner_smul_right, hz0]
  have him : RealHilbertComplexification.im (x : RealHilbertComplexification E) = 0 := by
    apply hdense.eq_zero_of_inner_left ℝ
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      have h := congrArg Complex.im (horth n)
      simpa [RealHilbertComplexification.inner_apply,
        RealHilbertComplexification.complexInner,
        ComplexifiedOrbitResolvent.ofReal] using h
    | zero => simp
    | add z w hz hw hz0 hw0 => simp [inner_add_right, hz0, hw0]
    | smul c z hz hz0 => simp [real_inner_smul_right, hz0]
  apply hx
  exact RealHilbertComplexification.ext hre him

/-- Pairing a resolvent equation with an eigenvector isolates its cyclic
component exactly, before taking any limit. -/
theorem eigenvector_inner_scaledResolvent
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hformal : A.IsFormalAdjoint A)
    {mu lambda : ℂ} (hmu : (starRingEnd ℂ) mu = mu)
    (x r : A.domain) {head : H}
    (hx : A x = mu • (x : H))
    (hr : A r - lambda • (r : H) = head) :
    inner ℂ (x : H) ((lambda - mu) • (r : H)) =
      -inner ℂ (x : H) head := by
  have hsym := hformal x r
  rw [hx, inner_smul_left, hmu] at hsym
  have h := congrArg (fun y : H => inner ℂ (x : H) y) hr
  rw [inner_sub_right, inner_smul_right, ← hsym] at h
  rw [inner_smul_right]
  linear_combination -h

end CyclicPointSpectrum

/-- Away from its zeros, the native Weyl continuation is analytic, including
its already removable value at the center. -/
theorem completedNativeJacobiWeylHeightContinuation_analyticAt_of_ne_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    AnalyticAt ℂ completedNativeJacobiWeylHeightContinuation z := by
  by_cases hz0 : z = 0
  · subst z
    exact completedNativeJacobiWeylHeightContinuation_analyticAt_zero
  have hanalytic := completedNativeOperatorCharacteristic_analyticAt hz
  have hlog : AnalyticAt ℂ completedNativeOperatorLogDerivative z :=
    hanalytic.deriv.neg.div hanalytic hF
  have hden : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by fun_prop
  have hquot := hlog.div hden (mul_ne_zero (by norm_num) hz0)
  apply hquot.congr
  filter_upwards [continuousAt_id.eventually_ne hz0] with w hw
  change w ≠ 0 at hw
  simp [completedNativeJacobiWeylHeightContinuation, hw]

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance : CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed (completedJet jet)).completeSpace_coe
local instance : SMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal.toNormedSpace.toModule.toDistribMulAction.toSMul
local instance : IsBoundedSMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  NormedSpace.toIsBoundedSMul
local instance : ContinuousSMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  IsBoundedSMul.continuousSMul

/-- A nonvanishing native characteristic has zero scaled cyclic readout
along the vertical spectral approach. -/
theorem positiveJacobiAtomicCyclicScaledReadout_tendsto_zero_of_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (hF : completedNativeOperatorCharacteristic z₀ ≠ 0) :
    Tendsto (certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real)
      atTop (nhds 0) := by
  have hpath := positiveJacobiAtomicHeightApproach_tendsto hz₀
  have hweyl :=
    (completedNativeJacobiWeylHeightContinuation_analyticAt_of_ne_zero
      hzDomain hF).continuousAt.tendsto.comp hpath
  have hproduct := ((hpath.add_const z₀).div_const (z₀ ^ 2)).mul
    ((hpath.sub_const z₀).mul hweyl)
  simp only [sub_self, zero_mul, mul_zero] at hproduct
  apply hproduct.congr'
  have hdomain := hpath.eventually
    (isOpen_completedNativeHeightDomain.mem_nhds hzDomain)
  have hnonzero := hpath.eventually
    ((completedNativeOperatorCharacteristic_analyticAt hzDomain).continuousAt.eventually_ne hF)
  filter_upwards [hdomain, hnonzero] with n hn hFn
  exact (certificate.positiveJacobiAtomicCyclicScaledReadout_eq_weyl
    hz₀ hz₀Real n hn hFn).symm

/-- The polarized resolvent Gram identity turns a zero scalar residue into
strong convergence of the scaled cyclic vector to zero. -/
theorem positiveJacobiAtomicCyclicScaledVector_tendsto_zero_of_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (hF : completedNativeOperatorCharacteristic z₀ ≠ 0) :
    Tendsto (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real)
      atTop (nhds 0) := by
  let g := certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real
  let u := certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real
  let eta : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hg : Tendsto g atTop (nhds 0) :=
    certificate.positiveJacobiAtomicCyclicScaledReadout_tendsto_zero_of_ne_zero
      hzDomain hz₀ hz₀Real hF
  have hconj : Tendsto (fun n => (starRingEnd ℂ) (g n)) atTop (nhds 0) := by
    simpa only [map_zero, Function.comp_def] using
      Complex.continuous_conj.continuousAt.tendsto.comp hg
  have hweighted := CyclicAtomicExtraction.weightedPairTendsto
    g (fun n => (starRingEnd ℂ) (g n)) 0 eta hg hconj (fun n => by
      dsimp [eta]
      positivity)
  have hinner : Tendsto (fun p : ℕ × ℕ => inner ℂ (u p.1) (u p.2))
      atTop (nhds 0) := by
    simp only [neg_zero] at hweighted
    apply hweighted.congr'
    exact Filter.Eventually.of_forall fun p =>
      (certificate.inner_positiveJacobiAtomicCyclicScaledVector hz₀Real p.1 p.2).symm
  have hdiag := hinner.comp tendsto_atTop_diagonal
  have hnormSq : Tendsto (fun n : ℕ => ‖u n‖ ^ 2) atTop (nhds 0) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hdiag
    convert hre using 1
    · ext n
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u n)).symm
    · simp
  have hnorm : Tendsto (fun n : ℕ => ‖u n‖) atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Every point eigenvector in the completed even sector is detected by the
canonical cyclic head. This excludes hidden point-spectrum directions. -/
theorem completedJacobiEigenvector_cyclicHead_ne_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {mu : ℂ}
    (x : certificate.completedJacobiEnergySelfAdjointData.complexification.domain)
    (hx : (x : RealHilbertComplexification (EvenCarrier jet)) ≠ 0)
    (hAx : certificate.completedJacobiEnergySelfAdjointData.complexification x =
      mu • (x : RealHilbertComplexification (EvenCarrier jet))) :
    inner ℂ (x : RealHilbertComplexification (EvenCarrier jet))
      certificate.positiveJacobiCyclicHead ≠ 0 := by
  have hself := certificate.completedJacobiEnergySelfAdjointData.complexification_isSelfAdjoint
  have hformal :=
    certificate.completedJacobiEnergySelfAdjointData.complexification.adjoint_isFormalAdjoint
      hself.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hself] at hformal
  exact CyclicPointSpectrum.eigenvector_visible_of_real_cyclicOrbit
    certificate.completedJacobiEnergySelfAdjointData.operator (completedJacobiOrbit jet)
    (completedJacobiOrbit_span_dense jet)
    certificate.completedJacobiOrbit_isOperatorOrbit hformal x hx hAx

/-- Point-spectrum converse at a nonzero real height: a Jacobi eigenvalue at
its reciprocal square forces a zero of the native characteristic. -/
theorem completedNativeOperator_eq_zero_of_hasEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (heigen : LinearPMap.HasEigenvalue
      certificate.completedJacobiEnergySelfAdjointData.complexification (z₀ ^ 2)⁻¹) :
    completedNativeOperatorCharacteristic z₀ = 0 := by
  by_contra hF
  obtain ⟨x, hx, hAx⟩ := heigen
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let H := RealHilbertComplexification (EvenCarrier jet)
  have hself := certificate.completedJacobiEnergySelfAdjointData.complexification_isSelfAdjoint
  have hformal : A.IsFormalAdjoint A := by
    have h := A.adjoint_isFormalAdjoint hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at h
    exact h
  have hvisible := certificate.completedJacobiEigenvector_cyclicHead_ne_zero x hx hAx
  have hu := certificate.positiveJacobiAtomicCyclicScaledVector_tendsto_zero_of_ne_zero
    hzDomain hz₀ hz₀Real hF
  have hpair : ∀ n : ℕ,
      inner ℂ (x : H) (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real n) =
        -inner ℂ (x : H) certificate.positiveJacobiCyclicHead := by
    intro n
    have hreal := inv_sq_im_eq_zero_of_im_eq_zero hz₀Real
    have hconj : (starRingEnd ℂ) ((z₀ ^ 2)⁻¹) = (z₀ ^ 2)⁻¹ := by
      apply Complex.ext
      · exact Complex.conj_re _
      · simp only [Complex.conj_im, hreal, neg_zero]
    exact CyclicPointSpectrum.eigenvector_inner_scaledResolvent A hformal hconj x
      (certificate.positiveJacobiCyclicResolventVector
        (positiveJacobiAtomicSpectralApproach (z₀ ^ 2)⁻¹ n)
        (Or.inl (ne_of_gt (positiveJacobiAtomicSpectralApproach_im_pos hreal n))))
      hAx (certificate.positiveJacobiCyclicResolventVector_equation _ _)
  have hzero : Tendsto
      (fun n : ℕ => inner ℂ (x : H)
        (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real n))
      atTop (nhds 0) := by
    simpa only [inner_zero_right] using
      (tendsto_const_nhds.inner hu : Tendsto _ atTop (nhds (inner ℂ (x : H) 0)))
  have hconstant : Tendsto
      (fun n : ℕ => inner ℂ (x : H)
        (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real n))
      atTop (nhds (-inner ℂ (x : H) certificate.positiveJacobiCyclicHead)) := by
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hpair n).symm)
  exact hvisible (neg_eq_zero.mp (tendsto_nhds_unique hconstant hzero))

/-- Exact point-spectrum/zero correspondence at every nonzero real height. -/
theorem completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {t : ℝ} (ht : t ≠ 0) :
    LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification
        ((t : ℂ) ^ 2)⁻¹ ↔
      completedNativeOperatorCharacteristic (t : ℂ) = 0 := by
  constructor
  · exact certificate.completedNativeOperator_eq_zero_of_hasEigenvalue_inv_sq
      (ofReal_mem_completedNativeHeightDomain t) (Complex.ofReal_ne_zero.mpr ht)
      (Complex.ofReal_im t)
  · exact certificate.completedNativeOperator_zero_hasEigenvalue_inv_sq
      (ofReal_mem_completedNativeHeightDomain t)

/-- Positive Jacobi point spectrum is exactly the reciprocal square of the
positive real native zero heights. No assertion about continuous spectrum
or analytic multiplicities is included. -/
theorem completedJacobiEnergyComplexification_hasEigenvalue_iff_nativeZero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    LinearPMap.HasEigenvalue
        certificate.completedJacobiEnergySelfAdjointData.complexification (lambda : ℂ) ↔
      completedNativeOperatorCharacteristic ((Real.sqrt lambda)⁻¹ : ℂ) = 0 := by
  have ht : (Real.sqrt lambda)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hlambda))
  have hsq : ((((Real.sqrt lambda)⁻¹ : ℝ) : ℂ) ^ 2)⁻¹ = (lambda : ℂ) := by
    norm_cast
    simp [inv_pow, Real.sq_sqrt hlambda.le]
  rw [← hsq]
  simpa only [Complex.ofReal_inv] using
    certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_iff_nativeZero ht

end CompletedNativeRealHPCarrierCertificate

end
end CarrySelfAdjointOperator
