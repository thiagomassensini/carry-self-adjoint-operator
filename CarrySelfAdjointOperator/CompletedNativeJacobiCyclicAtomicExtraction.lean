import CarrySelfAdjointOperator.CompletedNativeJacobiCyclicStieltjesReadout
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Tactic

/-!
# Atomic extraction from the cyclic completed Jacobi readout

This file promotes a simple pole of the concrete cyclic Jacobi readout to a
nonzero eigenvector.  The construction is vectorial: scaled off-axis
resolvent vectors form a Cauchy sequence by the polarized resolvent identity,
and closedness of the operator graph identifies their limit as an eigenvector.
No abstract spectral measure or pure-point hypothesis is introduced.
-/

open Filter Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

namespace CyclicAtomicExtraction

/-- If all pairwise inner products of a sequence converge to one positive
real mass, completeness produces a nonzero norm limit. -/
theorem exists_ne_zero_tendsto_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (u : ℕ → H) {mass : ℝ} (hmass : 0 < mass)
    (hinner : Tendsto
      (fun p : ℕ × ℕ ↦ inner ℂ (u p.1) (u p.2))
      atTop (nhds (mass : ℂ))) :
    ∃ v : H, v ≠ 0 ∧ Tendsto u atTop (nhds v) := by
  have hdiag : Tendsto (fun n : ℕ ↦ inner ℂ (u n) (u n))
      atTop (nhds (mass : ℂ)) :=
    hinner.comp tendsto_atTop_diagonal
  have hnormSq : Tendsto (fun n : ℕ ↦ ‖u n‖ ^ 2)
      atTop (nhds mass) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hdiag
    convert hre using 1
    · ext n
      simp [pow_two, Complex.mul_re]
    · simp
  have htendstoFst : Tendsto (Prod.fst : ℕ × ℕ → ℕ)
      atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have htendstoSnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ)
      atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hfirst : Tendsto (fun p : ℕ × ℕ ↦ ‖u p.1‖ ^ 2)
      atTop (nhds mass) :=
    hnormSq.comp htendstoFst
  have hsecond : Tendsto (fun p : ℕ × ℕ ↦ ‖u p.2‖ ^ 2)
      atTop (nhds mass) :=
    hnormSq.comp htendstoSnd
  have hinnerRe : Tendsto
      (fun p : ℕ × ℕ ↦ (inner ℂ (u p.1) (u p.2)).re)
      atTop (nhds mass) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp hinner
  have hdistSq : Tendsto
      (fun p : ℕ × ℕ ↦ dist (u p.1) (u p.2) ^ 2)
      atTop (nhds 0) := by
    have h := (hfirst.sub (hinnerRe.const_mul 2)).add hsecond
    convert h using 1
    · ext p
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ)]
      simp only [RCLike.re_to_complex]
    · ring
  have hdist : Tendsto
      (fun p : ℕ × ℕ ↦ dist (u p.1) (u p.2))
      atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hdistSq
    convert hsqrt using 1
    · ext p
      exact (Real.sqrt_sq dist_nonneg).symm
    · simp
  have hcauchy : CauchySeq u :=
    cauchySeq_iff_tendsto_dist_atTop_0.mpr hdist
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨v, ?_, hv⟩
  have hnormLimit : Tendsto (fun n : ℕ ↦ ‖u n‖ ^ 2)
      atTop (nhds (‖v‖ ^ 2)) := hv.norm.pow 2
  have hmassEq : mass = ‖v‖ ^ 2 :=
    tendsto_nhds_unique hnormSq hnormLimit
  intro hvzero
  rw [hvzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hmassEq
  linarith

/-- Algebraic core of the vertical polarized resolvent identity.  The two
weights add to one and no positivity or limiting argument enters here. -/
theorem verticalPolarizedScaledInner
    (a b : ℝ) (hsum : a + b ≠ 0) (m n x : ℂ)
    (hpolarized :
      m - (starRingEnd ℂ) n = Complex.I * (((a + b : ℝ) : ℂ)) * x) :
    (Complex.I * (a : ℂ)) *
        ((starRingEnd ℂ) (Complex.I * (b : ℂ)) * x) =
      -(((b / (a + b) : ℝ) : ℂ)) * (Complex.I * (a : ℂ) * m) -
        (((a / (a + b) : ℝ) : ℂ)) *
          (starRingEnd ℂ) (Complex.I * (b : ℂ) * n) := by
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  push_cast at hpolarized
  have hsumC : (((a + b : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsum
  have hsumC' : (a : ℂ) + (b : ℂ) ≠ 0 := by
    exact_mod_cast hsum
  field_simp [hsumC, hsumC']
  linear_combination ((a : ℂ) * (b : ℂ)) * hpolarized

/-- A convex combination with arbitrary positive, varying weights has the
same pair-filter limit when both channels converge to the same value. -/
theorem weightedPairTendsto
    (g h : ℕ → ℂ) (a : ℂ) (eta : ℕ → ℝ)
    (hg : Tendsto g atTop (nhds a))
    (hh : Tendsto h atTop (nhds a))
    (heta : ∀ n, 0 < eta n) :
    Tendsto
      (fun p : ℕ × ℕ ↦
        -(((eta p.1 / (eta p.2 + eta p.1) : ℝ) : ℂ)) * g p.2 -
          (((eta p.2 / (eta p.2 + eta p.1) : ℝ) : ℂ)) * h p.1)
      atTop (nhds (-a)) := by
  have htendstoFst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have htendstoSnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hgSnd : Tendsto (fun p : ℕ × ℕ ↦ g p.2 - a)
      atTop (nhds 0) := by
    convert (hg.comp htendstoSnd).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ ↦ a) atTop (nhds a)) using 1 <;>
      simp
  have hhFst : Tendsto (fun p : ℕ × ℕ ↦ h p.1 - a)
      atTop (nhds 0) := by
    convert (hh.comp htendstoFst).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ × ℕ ↦ a) atTop (nhds a)) using 1 <;>
      simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herrors : Tendsto
      (fun p : ℕ × ℕ ↦ ‖g p.2 - a‖ + ‖h p.1 - a‖)
      atTop (nhds 0) := by
    simpa using hgSnd.norm.add hhFst.norm
  refine squeeze_zero (fun p ↦ norm_nonneg _) ?_ herrors
  intro p
  let d : ℝ := eta p.2 + eta p.1
  let wk : ℝ := eta p.1 / d
  let wn : ℝ := eta p.2 / d
  have hd : 0 < d := add_pos (heta p.2) (heta p.1)
  have hwk0 : 0 ≤ wk := div_nonneg (heta p.1).le hd.le
  have hwn0 : 0 ≤ wn := div_nonneg (heta p.2).le hd.le
  have hwk1 : wk ≤ 1 :=
    (div_le_one hd).2 (le_add_of_nonneg_left (heta p.2).le)
  have hwn1 : wn ≤ 1 :=
    (div_le_one hd).2 (le_add_of_nonneg_right (heta p.1).le)
  have hsum : wk + wn = 1 := by
    dsimp [wk, wn]
    rw [← add_div]
    have hnum : eta p.1 + eta p.2 = d := by
      dsimp [d]
      ring
    rw [hnum, div_self (ne_of_gt hd)]
  have halgebra :
      -((wk : ℂ)) * g p.2 - (wn : ℂ) * h p.1 - -a =
        -((wk : ℂ)) * (g p.2 - a) -
          (wn : ℂ) * (h p.1 - a) := by
    have hsumC : (wk : ℂ) + (wn : ℂ) = 1 := by
      exact_mod_cast hsum
    calc
      -((wk : ℂ)) * g p.2 - (wn : ℂ) * h p.1 - -a =
          -((wk : ℂ)) * g p.2 - (wn : ℂ) * h p.1 +
            ((wk : ℂ) + (wn : ℂ)) * a := by rw [hsumC]; ring
      _ = -((wk : ℂ)) * (g p.2 - a) -
          (wn : ℂ) * (h p.1 - a) := by ring
  change ‖-((wk : ℂ)) * g p.2 - (wn : ℂ) * h p.1 - -a‖ ≤ _
  rw [halgebra]
  calc
    ‖-((wk : ℂ)) * (g p.2 - a) - (wn : ℂ) * (h p.1 - a)‖
        ≤ ‖-((wk : ℂ)) * (g p.2 - a)‖ +
            ‖(wn : ℂ) * (h p.1 - a)‖ := norm_sub_le _ _
    _ = wk * ‖g p.2 - a‖ + wn * ‖h p.1 - a‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hwk0, abs_of_nonneg hwn0]
    _ ≤ ‖g p.2 - a‖ + ‖h p.1 - a‖ := by
      gcongr
      · exact mul_le_of_le_one_left (norm_nonneg _) hwk1
      · exact mul_le_of_le_one_left (norm_nonneg _) hwn1

end CyclicAtomicExtraction

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance cyclicAtomicEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

local instance cyclicAtomicComplexificationSMul :
    SMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  RealHilbertComplexification.instInnerProductSpaceComplexOfReal.toNormedSpace.toModule.toDistribMulAction.toSMul

local instance cyclicAtomicComplexificationIsBoundedSMul :
    IsBoundedSMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  NormedSpace.toIsBoundedSMul

local instance cyclicAtomicComplexificationContinuousSMul :
    ContinuousSMul ℂ (RealHilbertComplexification (EvenCarrier jet)) :=
  IsBoundedSMul.continuousSMul

/-- Vertical approach to a real spectral parameter. -/
def positiveJacobiAtomicSpectralApproach (lambda₀ : ℂ) (n : ℕ) : ℂ :=
  lambda₀ + Complex.I * ((n : ℂ) + 1)⁻¹

/-- The corresponding local inverse of the reciprocal-square height map.
It is normalized to take the value `z₀` at `λ₀ = (z₀²)⁻¹`, independently
of the sign of the real height. -/
def positiveJacobiReciprocalSquareHeightBranch (z₀ lambda : ℂ) : ℂ :=
  z₀ * Complex.sqrt (((z₀ ^ 2)⁻¹) / lambda)

/-- The vertical spectral approach converges to its base parameter. -/
theorem positiveJacobiAtomicSpectralApproach_tendsto (lambda₀ : ℂ) :
    Tendsto (positiveJacobiAtomicSpectralApproach lambda₀) atTop (nhds lambda₀) := by
  have heta : Tendsto (fun n : ℕ ↦ ((n : ℂ) + 1)⁻¹)
      atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  change Tendsto
    (fun n : ℕ ↦ lambda₀ + Complex.I * ((n : ℂ) + 1)⁻¹)
    atTop (nhds lambda₀)
  simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul heta)

@[simp] theorem positiveJacobiAtomicSpectralApproach_im
    {lambda₀ : ℂ} (hlambda₀ : lambda₀.im = 0) (n : ℕ) :
    (positiveJacobiAtomicSpectralApproach lambda₀ n).im =
      ((n : ℝ) + 1)⁻¹ := by
  unfold positiveJacobiAtomicSpectralApproach
  rw [Complex.add_im, Complex.mul_im]
  simp only [hlambda₀, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add]
  rw [Complex.inv_re]
  norm_num [Complex.normSq]

/-- Every point of the vertical approach lies off the real axis. -/
theorem positiveJacobiAtomicSpectralApproach_im_pos
    {lambda₀ : ℂ} (hlambda₀ : lambda₀.im = 0) (n : ℕ) :
    0 < (positiveJacobiAtomicSpectralApproach lambda₀ n).im := by
  rw [positiveJacobiAtomicSpectralApproach_im hlambda₀]
  positivity

/-- The normalized square-root branch inverts the reciprocal-square
coordinate exactly, not merely asymptotically. -/
theorem positiveJacobiReciprocalSquareHeightBranch_sq_inv
    {z₀ lambda : ℂ} (hz₀ : z₀ ≠ 0) (hlambda : lambda ≠ 0) :
    (positiveJacobiReciprocalSquareHeightBranch z₀ lambda ^ 2)⁻¹ = lambda := by
  unfold positiveJacobiReciprocalSquareHeightBranch Complex.sqrt
  rw [mul_pow]
  have hsqrt :
      ((((z₀ ^ 2)⁻¹ / lambda) ^ (2⁻¹ : ℂ)) ^ (2 : ℕ)) =
        (z₀ ^ 2)⁻¹ / lambda := by
    exact Complex.cpow_nat_inv_pow (((z₀ ^ 2)⁻¹) / lambda)
      (by decide : (2 : ℕ) ≠ 0)
  rw [hsqrt]
  field_simp [pow_ne_zero 2 hz₀, hlambda]

/-- The normalized branch converges to the selected signed height. -/
theorem positiveJacobiReciprocalSquareHeightBranch_tendsto
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    Tendsto (positiveJacobiReciprocalSquareHeightBranch z₀)
      (nhds ((z₀ ^ 2)⁻¹)) (nhds z₀) := by
  have hlambda₀ : (z₀ ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hz₀)
  have hratio : Tendsto (fun lambda : ℂ ↦ (z₀ ^ 2)⁻¹ / lambda)
      (nhds ((z₀ ^ 2)⁻¹)) (nhds 1) := by
    have hconst : Tendsto (fun _ : ℂ ↦ (z₀ ^ 2)⁻¹)
        (nhds ((z₀ ^ 2)⁻¹)) (nhds ((z₀ ^ 2)⁻¹)) :=
      tendsto_const_nhds
    change Tendsto
      ((fun _ : ℂ ↦ (z₀ ^ 2)⁻¹) / id)
      (nhds ((z₀ ^ 2)⁻¹)) (nhds 1)
    simpa [hlambda₀] using (hconst.div tendsto_id hlambda₀)
  have hsqrt : Tendsto
      (fun lambda : ℂ ↦ Complex.sqrt ((z₀ ^ 2)⁻¹ / lambda))
      (nhds ((z₀ ^ 2)⁻¹)) (nhds 1) := by
    change Tendsto
      (Complex.sqrt ∘ fun lambda : ℂ ↦ (z₀ ^ 2)⁻¹ / lambda)
      (nhds ((z₀ ^ 2)⁻¹)) (nhds 1)
    simpa only [Complex.sqrt_one] using
      ((Complex.continuousAt_sqrt (z := (1 : ℂ)) (Or.inl (by norm_num)))
        |>.tendsto.comp hratio)
  change Tendsto
    (fun lambda : ℂ ↦ z₀ * Complex.sqrt ((z₀ ^ 2)⁻¹ / lambda))
    (nhds ((z₀ ^ 2)⁻¹)) (nhds z₀)
  simpa using tendsto_const_nhds.mul hsqrt

/-- The height readout is the canonical native Weyl continuation at every
off-axis point where the characteristic is nonzero. -/
theorem positiveJacobiHeightGlobalBoundaryReadout_eq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (hzIm : z.im ≠ 0)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    certificate.positiveJacobiHeightGlobalBoundaryReadout z hzIm =
      completedNativeJacobiWeylHeightContinuation z := by
  have hz : z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    exact hzIm (by simpa using him)
  have hlog :=
    certificate.completedNativeOperatorLogDerivative_eq_cyclicStieltjesReadout
      hzDomain hzIm hF
  rw [completedNativeJacobiWeylHeightContinuation, if_neg hz,
    hlog,
    certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_cyclic z hzIm]
  field_simp [hz]

/-- Schwarz symmetry of the concrete cyclic resolvent readout follows from
the polarized resolvent identity and uniqueness; no spectral theorem is
needed. -/
theorem positiveJacobiCyclicResolventReadout_conj
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    certificate.positiveJacobiCyclicResolventReadout
        (starRingEnd ℂ lambda) (Or.inl (by simpa using hlambda)) =
      (starRingEnd ℂ)
        (certificate.positiveJacobiCyclicResolventReadout
          lambda (Or.inl hlambda)) := by
  let hout : OutsideNonnegativeRealAxis lambda := Or.inl hlambda
  let hconj : OutsideNonnegativeRealAxis (starRingEnd ℂ lambda) :=
    Or.inl (by simpa using hlambda)
  have hpolarized :=
    certificate.positiveJacobiCyclicResolventReadout_sub_conj_eq
      lambda (starRingEnd ℂ lambda) hout hconj
  have hzero :
      lambda - (starRingEnd ℂ) ((starRingEnd ℂ) lambda) = 0 := by
    simp
  rw [hzero, zero_mul, sub_eq_zero] at hpolarized
  simpa using
    (congrArg (starRingEnd ℂ) hpolarized).symm

/-- The reciprocal square of a real nonzero height is real. -/
theorem inv_sq_im_eq_zero_of_im_eq_zero
    {z₀ : ℂ} (hz₀Real : z₀.im = 0) :
    ((z₀ ^ 2)⁻¹).im = 0 := by
  rw [Complex.inv_im]
  simp [pow_two, Complex.mul_im, hz₀Real]

/-- Height path obtained by applying the exact reciprocal-square branch to
the vertical spectral approach. -/
def positiveJacobiAtomicHeightApproach (z₀ : ℂ) (n : ℕ) : ℂ :=
  positiveJacobiReciprocalSquareHeightBranch z₀
    (positiveJacobiAtomicSpectralApproach ((z₀ ^ 2)⁻¹) n)

/-- The atomic height path converges to the selected height. -/
theorem positiveJacobiAtomicHeightApproach_tendsto
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    Tendsto (positiveJacobiAtomicHeightApproach z₀) atTop (nhds z₀) := by
  exact (positiveJacobiReciprocalSquareHeightBranch_tendsto hz₀).comp
    (positiveJacobiAtomicSpectralApproach_tendsto ((z₀ ^ 2)⁻¹))

/-- The branch and spectral paths commute exactly with reciprocal square. -/
theorem positiveJacobiAtomicHeightApproach_sq_inv
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (n : ℕ) :
    (positiveJacobiAtomicHeightApproach z₀ n ^ 2)⁻¹ =
      positiveJacobiAtomicSpectralApproach ((z₀ ^ 2)⁻¹) n := by
  apply positiveJacobiReciprocalSquareHeightBranch_sq_inv hz₀
  intro hzero
  have hbase := inv_sq_im_eq_zero_of_im_eq_zero hz₀Real
  have hpos := positiveJacobiAtomicSpectralApproach_im_pos hbase n
  rw [hzero] at hpos
  norm_num at hpos

/-- Every atomic height approximation is genuinely off-axis. -/
theorem positiveJacobiAtomicHeightApproach_im_ne_zero
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (n : ℕ) :
    (positiveJacobiAtomicHeightApproach z₀ n).im ≠ 0 := by
  intro him
  have hinvReal := inv_sq_im_eq_zero_of_im_eq_zero him
  rw [positiveJacobiAtomicHeightApproach_sq_inv hz₀ hz₀Real n,
    positiveJacobiAtomicSpectralApproach_im
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real)] at hinvReal
  have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

/-- The atomic height path approaches through the punctured plane. -/
theorem positiveJacobiAtomicHeightApproach_tendsto_punctured
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0) :
    Tendsto (positiveJacobiAtomicHeightApproach z₀) atTop
      (nhdsWithin z₀ {z₀}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨positiveJacobiAtomicHeightApproach_tendsto hz₀, ?_⟩
  exact Filter.Eventually.of_forall fun n ↦ by
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    have him := congrArg Complex.im heq
    exact positiveJacobiAtomicHeightApproach_im_ne_zero hz₀ hz₀Real n
      (by simpa [hz₀Real] using him)

/-- Spectral residue read from the concrete off-axis cyclic resolvent along
the canonical vertical approach. -/
def positiveJacobiAtomicCyclicScaledReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) : ℂ :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let lambda := positiveJacobiAtomicSpectralApproach lambda₀ n
  (lambda - lambda₀) *
    certificate.positiveJacobiCyclicResolventReadout lambda
      (Or.inl (ne_of_gt
        (positiveJacobiAtomicSpectralApproach_im_pos
          (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n)))

/-- The scalar coefficient forced by the simple native Weyl pole after the
reciprocal-square change of variables. -/
def positiveJacobiAtomicCyclicResidue (z₀ : ℂ) : ℂ :=
  ((2 : ℂ) / z₀) *
    meromorphicTrailingCoeffAt
      completedNativeJacobiWeylHeightContinuation z₀

/-- Exact pointwise conversion from the scaled cyclic resolvent readout to
the scaled native Weyl continuation on the reciprocal-square branch. -/
theorem positiveJacobiAtomicCyclicScaledReadout_eq_weyl
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (n : ℕ)
    (hzDomain : positiveJacobiAtomicHeightApproach z₀ n ∈
      completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic
      (positiveJacobiAtomicHeightApproach z₀ n) ≠ 0) :
    certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real n =
      ((positiveJacobiAtomicHeightApproach z₀ n + z₀) / z₀ ^ 2) *
        ((positiveJacobiAtomicHeightApproach z₀ n - z₀) *
          completedNativeJacobiWeylHeightContinuation
            (positiveJacobiAtomicHeightApproach z₀ n)) := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  let lambda : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ n
  let z : ℂ := positiveJacobiAtomicHeightApproach z₀ n
  have hlambdaIm : lambda.im ≠ 0 := ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n)
  have hzIm : z.im ≠ 0 :=
    positiveJacobiAtomicHeightApproach_im_ne_zero hz₀ hz₀Real n
  have hz : z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    exact hzIm (by simpa using him)
  have hsquare : (z ^ 2)⁻¹ = lambda :=
    positiveJacobiAtomicHeightApproach_sq_inv hz₀ hz₀Real n
  have hweyl := certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_weyl
    hzDomain hzIm hF
  have hcyclic := certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_cyclic
    z hzIm
  change certificate.positiveJacobiHeightGlobalBoundaryReadout z hzIm =
    completedNativeJacobiWeylHeightContinuation z at hweyl
  have hcyclic' :
      certificate.positiveJacobiHeightGlobalBoundaryReadout z hzIm =
        -lambda * certificate.positiveJacobiCyclicResolventReadout
          lambda (Or.inl hlambdaIm) := by
    simpa only [hsquare] using hcyclic
  have hrelation :
      completedNativeJacobiWeylHeightContinuation z =
        -lambda * certificate.positiveJacobiCyclicResolventReadout
          lambda (Or.inl hlambdaIm) := by
    rw [← hweyl, hcyclic']
  let m : ℂ := certificate.positiveJacobiCyclicResolventReadout
    lambda (Or.inl hlambdaIm)
  change (lambda - lambda₀) * m =
    ((z + z₀) / z₀ ^ 2) *
      ((z - z₀) * completedNativeJacobiWeylHeightContinuation z)
  change completedNativeJacobiWeylHeightContinuation z = -lambda * m
    at hrelation
  dsimp [lambda₀]
  rw [show lambda = (z ^ 2)⁻¹ from hsquare.symm] at hrelation ⊢
  field_simp [pow_ne_zero 2 hz₀, pow_ne_zero 2 hz] at hrelation ⊢
  linear_combination (z₀ ^ 2 - z ^ 2) * hrelation

/-- At a real native zero, the scaled scalar cyclic resolvent converges to
the nonzero meromorphic residue transported through `lambda = z⁻²`. -/
theorem positiveJacobiAtomicCyclicScaledReadout_tendsto
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    Tendsto
      (certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real)
      atTop (nhds (positiveJacobiAtomicCyclicResidue z₀)) := by
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  let path : ℕ → ℂ := positiveJacobiAtomicHeightApproach z₀
  have hpath : Tendsto path atTop (nhds z₀) :=
    positiveJacobiAtomicHeightApproach_tendsto hz₀
  have hpathPunctured : Tendsto path atTop (nhdsWithin z₀ {z₀}ᶜ) :=
    positiveJacobiAtomicHeightApproach_tendsto_punctured hz₀ hz₀Real
  have hmeromorphic :=
    completedNativeJacobiWeylHeightContinuation_meromorphicAt hzDomain
  have horder :=
    (completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
      hzDomain).2 hzero
  have htrail : Tendsto
      (fun z : ℂ ↦ (z - z₀) * completedNativeJacobiWeylHeightContinuation z)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (meromorphicTrailingCoeffAt
        completedNativeJacobiWeylHeightContinuation z₀)) := by
    have h := hmeromorphic.tendsto_nhds_meromorphicTrailingCoeffAt
    rw [horder] at h
    have hpower :
        -((((-1 : ℤ) : WithTop ℤ).untop₀)) = (1 : ℤ) := by
      norm_num
    rw [hpower] at h
    simp only [zpow_one, smul_eq_mul] at h
    change Tendsto
      (fun z : ℂ ↦ (z - z₀) * completedNativeJacobiWeylHeightContinuation z)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (meromorphicTrailingCoeffAt
        completedNativeJacobiWeylHeightContinuation z₀)) at h
    exact h
  have htrailPath : Tendsto
      (fun n : ℕ ↦ (path n - z₀) *
        completedNativeJacobiWeylHeightContinuation (path n))
      atTop
      (nhds (meromorphicTrailingCoeffAt
        completedNativeJacobiWeylHeightContinuation z₀)) :=
    htrail.comp hpathPunctured
  have hfactor : Tendsto
      (fun n : ℕ ↦ (path n + z₀) / z₀ ^ 2)
      atTop (nhds ((2 : ℂ) / z₀)) := by
    have h := (hpath.add_const z₀).div_const (z₀ ^ 2)
    convert h using 1
    field_simp [hz₀]
    ring
  have hrhs : Tendsto
      (fun n : ℕ ↦ ((path n + z₀) / z₀ ^ 2) *
        ((path n - z₀) *
          completedNativeJacobiWeylHeightContinuation (path n)))
      atTop (nhds (positiveJacobiAtomicCyclicResidue z₀)) := by
    simpa [positiveJacobiAtomicCyclicResidue] using hfactor.mul htrailPath
  have hDomain : ∀ᶠ n : ℕ in atTop,
      path n ∈ completedNativeHeightDomain :=
    hpath.eventually (isOpen_completedNativeHeightDomain.mem_nhds hzDomain)
  have hFne : ∀ᶠ z : ℂ in nhdsWithin z₀ {z₀}ᶜ,
      completedNativeOperatorCharacteristic z ≠ 0 :=
    (completedNativeOperatorCharacteristic_analyticAt hzDomain)
      |>.eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left
        (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
  have hFpath : ∀ᶠ n : ℕ in atTop,
      completedNativeOperatorCharacteristic (path n) ≠ 0 :=
    hpathPunctured.eventually hFne
  apply hrhs.congr'
  filter_upwards [hDomain, hFpath] with n hnDomain hnF
  simpa [path] using
    (certificate.positiveJacobiAtomicCyclicScaledReadout_eq_weyl
      hz₀ hz₀Real n hnDomain hnF).symm

/-! ## Lower approach and reality of the atom -/

/-- Lower vertical approach, defined as the conjugate of the upper one. -/
def positiveJacobiAtomicLowerSpectralApproach (lambda₀ : ℂ) (n : ℕ) : ℂ :=
  (starRingEnd ℂ) (positiveJacobiAtomicSpectralApproach lambda₀ n)

theorem positiveJacobiAtomicLowerSpectralApproach_tendsto
    {lambda₀ : ℂ} (hlambda₀Real : lambda₀.im = 0) :
    Tendsto (positiveJacobiAtomicLowerSpectralApproach lambda₀)
      atTop (nhds lambda₀) := by
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    (positiveJacobiAtomicSpectralApproach_tendsto lambda₀)
  have hconj : (starRingEnd ℂ) lambda₀ = lambda₀ := by
    apply Complex.ext
    · simp
    · simp [hlambda₀Real]
  rw [hconj] at h
  exact h

@[simp] theorem positiveJacobiAtomicLowerSpectralApproach_im
    {lambda₀ : ℂ} (hlambda₀Real : lambda₀.im = 0) (n : ℕ) :
    (positiveJacobiAtomicLowerSpectralApproach lambda₀ n).im =
      -((n : ℝ) + 1)⁻¹ := by
  simp [positiveJacobiAtomicLowerSpectralApproach,
    positiveJacobiAtomicSpectralApproach_im hlambda₀Real]

theorem positiveJacobiAtomicLowerSpectralApproach_im_ne_zero
    {lambda₀ : ℂ} (hlambda₀Real : lambda₀.im = 0) (n : ℕ) :
    (positiveJacobiAtomicLowerSpectralApproach lambda₀ n).im ≠ 0 := by
  rw [positiveJacobiAtomicLowerSpectralApproach_im hlambda₀Real]
  exact neg_ne_zero.mpr (inv_ne_zero (by positivity))

/-- Lower reciprocal-square height branch. -/
def positiveJacobiAtomicLowerHeightApproach (z₀ : ℂ) (n : ℕ) : ℂ :=
  positiveJacobiReciprocalSquareHeightBranch z₀
    (positiveJacobiAtomicLowerSpectralApproach ((z₀ ^ 2)⁻¹) n)

theorem positiveJacobiAtomicLowerHeightApproach_tendsto
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0) :
    Tendsto (positiveJacobiAtomicLowerHeightApproach z₀)
      atTop (nhds z₀) := by
  exact (positiveJacobiReciprocalSquareHeightBranch_tendsto hz₀).comp
    (positiveJacobiAtomicLowerSpectralApproach_tendsto
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real))

theorem positiveJacobiAtomicLowerHeightApproach_sq_inv
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (n : ℕ) :
    (positiveJacobiAtomicLowerHeightApproach z₀ n ^ 2)⁻¹ =
      positiveJacobiAtomicLowerSpectralApproach ((z₀ ^ 2)⁻¹) n := by
  apply positiveJacobiReciprocalSquareHeightBranch_sq_inv hz₀
  intro hzero
  have him := congrArg Complex.im hzero
  rw [positiveJacobiAtomicLowerSpectralApproach_im
    (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real)] at him
  have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  simp at him
  linarith

theorem positiveJacobiAtomicLowerHeightApproach_im_ne_zero
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0)
    (n : ℕ) :
    (positiveJacobiAtomicLowerHeightApproach z₀ n).im ≠ 0 := by
  intro him
  have hinvReal := inv_sq_im_eq_zero_of_im_eq_zero him
  rw [positiveJacobiAtomicLowerHeightApproach_sq_inv hz₀ hz₀Real n,
    positiveJacobiAtomicLowerSpectralApproach_im
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real)] at hinvReal
  have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

theorem positiveJacobiAtomicLowerHeightApproach_tendsto_punctured
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (hz₀Real : z₀.im = 0) :
    Tendsto (positiveJacobiAtomicLowerHeightApproach z₀) atTop
      (nhdsWithin z₀ {z₀}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨positiveJacobiAtomicLowerHeightApproach_tendsto hz₀ hz₀Real, ?_⟩
  exact Filter.Eventually.of_forall fun n ↦ by
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    have him := congrArg Complex.im heq
    exact positiveJacobiAtomicLowerHeightApproach_im_ne_zero hz₀ hz₀Real n
      (by simpa [hz₀Real] using him)

/-- Scaled lower cyclic readout. -/
def positiveJacobiAtomicLowerCyclicScaledReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) : ℂ :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let lambda := positiveJacobiAtomicLowerSpectralApproach lambda₀ n
  (lambda - lambda₀) *
    certificate.positiveJacobiCyclicResolventReadout lambda
      (Or.inl (positiveJacobiAtomicLowerSpectralApproach_im_ne_zero
        (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n))

/-- Generic pointwise branch conversion used by the lower approach. -/
theorem positiveJacobiCyclicScaledReadout_eq_weyl_of_sq_inv
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ lambda z : ℂ} (hz₀ : z₀ ≠ 0)
    (hlambdaIm : lambda.im ≠ 0) (hzIm : z.im ≠ 0)
    (hsquare : (z ^ 2)⁻¹ = lambda)
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    (lambda - (z₀ ^ 2)⁻¹) *
        certificate.positiveJacobiCyclicResolventReadout
          lambda (Or.inl hlambdaIm) =
      ((z + z₀) / z₀ ^ 2) *
        ((z - z₀) * completedNativeJacobiWeylHeightContinuation z) := by
  have hz : z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    exact hzIm (by simpa using him)
  have hweyl := certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_weyl
    hzDomain hzIm hF
  have hcyclic := certificate.positiveJacobiHeightGlobalBoundaryReadout_eq_cyclic
    z hzIm
  have hcyclic' :
      certificate.positiveJacobiHeightGlobalBoundaryReadout z hzIm =
        -lambda * certificate.positiveJacobiCyclicResolventReadout
          lambda (Or.inl hlambdaIm) := by
    simpa only [hsquare] using hcyclic
  have hrelation : completedNativeJacobiWeylHeightContinuation z =
      -lambda * certificate.positiveJacobiCyclicResolventReadout
        lambda (Or.inl hlambdaIm) := by
    rw [← hweyl, hcyclic']
  let m : ℂ := certificate.positiveJacobiCyclicResolventReadout
    lambda (Or.inl hlambdaIm)
  change (lambda - (z₀ ^ 2)⁻¹) * m =
    ((z + z₀) / z₀ ^ 2) *
      ((z - z₀) * completedNativeJacobiWeylHeightContinuation z)
  change completedNativeJacobiWeylHeightContinuation z = -lambda * m
    at hrelation
  rw [show lambda = (z ^ 2)⁻¹ from hsquare.symm] at hrelation ⊢
  field_simp [pow_ne_zero 2 hz₀, pow_ne_zero 2 hz] at hrelation ⊢
  linear_combination (z₀ ^ 2 - z ^ 2) * hrelation

/-- The lower scaled readout has the same meromorphic residue. -/
theorem positiveJacobiAtomicLowerCyclicScaledReadout_tendsto
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    Tendsto
      (certificate.positiveJacobiAtomicLowerCyclicScaledReadout z₀ hz₀Real)
      atTop (nhds (positiveJacobiAtomicCyclicResidue z₀)) := by
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  let path : ℕ → ℂ := positiveJacobiAtomicLowerHeightApproach z₀
  have hpath : Tendsto path atTop (nhds z₀) :=
    positiveJacobiAtomicLowerHeightApproach_tendsto hz₀ hz₀Real
  have hpathPunctured : Tendsto path atTop (nhdsWithin z₀ {z₀}ᶜ) :=
    positiveJacobiAtomicLowerHeightApproach_tendsto_punctured hz₀ hz₀Real
  have hmeromorphic :=
    completedNativeJacobiWeylHeightContinuation_meromorphicAt hzDomain
  have horder :=
    (completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
      hzDomain).2 hzero
  have htrail : Tendsto
      (fun z : ℂ ↦ (z - z₀) * completedNativeJacobiWeylHeightContinuation z)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (meromorphicTrailingCoeffAt
        completedNativeJacobiWeylHeightContinuation z₀)) := by
    have h := hmeromorphic.tendsto_nhds_meromorphicTrailingCoeffAt
    rw [horder] at h
    have hpower :
        -((((-1 : ℤ) : WithTop ℤ).untop₀)) = (1 : ℤ) := by
      norm_num
    rw [hpower] at h
    simp only [zpow_one, smul_eq_mul] at h
    change Tendsto
      (fun z : ℂ ↦ (z - z₀) * completedNativeJacobiWeylHeightContinuation z)
      (nhdsWithin z₀ {z₀}ᶜ)
      (nhds (meromorphicTrailingCoeffAt
        completedNativeJacobiWeylHeightContinuation z₀)) at h
    exact h
  have htrailPath := htrail.comp hpathPunctured
  have hfactor : Tendsto
      (fun n : ℕ ↦ (path n + z₀) / z₀ ^ 2)
      atTop (nhds ((2 : ℂ) / z₀)) := by
    have h := (hpath.add_const z₀).div_const (z₀ ^ 2)
    convert h using 1
    field_simp [hz₀]
    ring
  have hrhs : Tendsto
      (fun n : ℕ ↦ ((path n + z₀) / z₀ ^ 2) *
        ((path n - z₀) *
          completedNativeJacobiWeylHeightContinuation (path n)))
      atTop (nhds (positiveJacobiAtomicCyclicResidue z₀)) := by
    simpa [positiveJacobiAtomicCyclicResidue] using hfactor.mul htrailPath
  have hDomain : ∀ᶠ n : ℕ in atTop,
      path n ∈ completedNativeHeightDomain :=
    hpath.eventually (isOpen_completedNativeHeightDomain.mem_nhds hzDomain)
  have hFne : ∀ᶠ z : ℂ in nhdsWithin z₀ {z₀}ᶜ,
      completedNativeOperatorCharacteristic z ≠ 0 :=
    (completedNativeOperatorCharacteristic_analyticAt hzDomain)
      |>.eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left
        (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
  have hFpath : ∀ᶠ n : ℕ in atTop,
      completedNativeOperatorCharacteristic (path n) ≠ 0 :=
    hpathPunctured.eventually hFne
  apply hrhs.congr'
  filter_upwards [hDomain, hFpath] with n hnDomain hnF
  let lambda := positiveJacobiAtomicLowerSpectralApproach ((z₀ ^ 2)⁻¹) n
  let z := positiveJacobiAtomicLowerHeightApproach z₀ n
  have hlambdaIm : lambda.im ≠ 0 :=
    positiveJacobiAtomicLowerSpectralApproach_im_ne_zero
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n
  have hzIm : z.im ≠ 0 :=
    positiveJacobiAtomicLowerHeightApproach_im_ne_zero hz₀ hz₀Real n
  have hsquare : (z ^ 2)⁻¹ = lambda :=
    positiveJacobiAtomicLowerHeightApproach_sq_inv hz₀ hz₀Real n
  have hpoint := certificate.positiveJacobiCyclicScaledReadout_eq_weyl_of_sq_inv
    hz₀ hlambdaIm hzIm hsquare hnDomain hnF
  simpa [positiveJacobiAtomicLowerCyclicScaledReadout, path, lambda, z] using
    hpoint.symm

/-- Lower and upper scaled readouts are exact complex conjugates. -/
theorem positiveJacobiAtomicLowerCyclicScaledReadout_eq_conj
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hz₀Real : z₀.im = 0) (n : ℕ) :
    certificate.positiveJacobiAtomicLowerCyclicScaledReadout z₀ hz₀Real n =
      (starRingEnd ℂ)
        (certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real n) := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  let lambda : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ n
  have hlambda₀Real : lambda₀.im = 0 :=
    inv_sq_im_eq_zero_of_im_eq_zero hz₀Real
  have hlambdaIm : lambda.im ≠ 0 := ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos hlambda₀Real n)
  have hreadout := certificate.positiveJacobiCyclicResolventReadout_conj hlambdaIm
  have hlambda₀Conj : (starRingEnd ℂ) lambda₀ = lambda₀ := by
    apply Complex.ext
    · simp
    · simp [hlambda₀Real]
  change ((starRingEnd ℂ) lambda - lambda₀) *
      certificate.positiveJacobiCyclicResolventReadout
        ((starRingEnd ℂ) lambda) _ =
    (starRingEnd ℂ)
      ((lambda - lambda₀) *
        certificate.positiveJacobiCyclicResolventReadout lambda _)
  rw [map_mul, map_sub, hlambda₀Conj, hreadout]

/-- The transported cyclic residue is fixed by complex conjugation. -/
theorem positiveJacobiAtomicCyclicResidue_conj
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    (starRingEnd ℂ) (positiveJacobiAtomicCyclicResidue z₀) =
      positiveJacobiAtomicCyclicResidue z₀ := by
  have hupper := certificate.positiveJacobiAtomicCyclicScaledReadout_tendsto
    hzDomain hzero hz₀Real
  have hlower := certificate.positiveJacobiAtomicLowerCyclicScaledReadout_tendsto
    hzDomain hzero hz₀Real
  have hconjUpper : Tendsto
      (fun n : ℕ ↦ (starRingEnd ℂ)
        (certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real n))
      atTop
      (nhds ((starRingEnd ℂ) (positiveJacobiAtomicCyclicResidue z₀))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp hupper
  have hlowerConj : Tendsto
      (certificate.positiveJacobiAtomicLowerCyclicScaledReadout z₀ hz₀Real)
      atTop
      (nhds ((starRingEnd ℂ) (positiveJacobiAtomicCyclicResidue z₀))) := by
    apply hconjUpper.congr'
    exact Filter.Eventually.of_forall fun n ↦
      (certificate.positiveJacobiAtomicLowerCyclicScaledReadout_eq_conj
        hz₀Real n).symm
  exact tendsto_nhds_unique hlowerConj hlower

/-- The transported cyclic residue is nonzero at every native zero. -/
theorem positiveJacobiAtomicCyclicResidue_ne_zero
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    positiveJacobiAtomicCyclicResidue z₀ ≠ 0 := by
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have hmeromorphic :=
    completedNativeJacobiWeylHeightContinuation_meromorphicAt hzDomain
  have horder :=
    (completedNativeJacobiWeylHeightContinuation_meromorphicOrderAt_eq_neg_one_iff_zero
      hzDomain).2 hzero
  have hfinite :
      meromorphicOrderAt completedNativeJacobiWeylHeightContinuation z₀ ≠ ⊤ := by
    rw [horder]
    simp
  exact mul_ne_zero (div_ne_zero (by norm_num) hz₀)
    (hmeromorphic.meromorphicTrailingCoeffAt_ne_zero hfinite)

/-- Real form of the transported cyclic residue. -/
theorem positiveJacobiAtomicCyclicResidue_im_eq_zero
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    (positiveJacobiAtomicCyclicResidue z₀).im = 0 := by
  have hconj := certificate.positiveJacobiAtomicCyclicResidue_conj
    hzDomain hzero hz₀Real
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith

/-- Positive atomic mass carried by the cyclic head. -/
def positiveJacobiAtomicCyclicMass (z₀ : ℂ) : ℝ :=
  -(positiveJacobiAtomicCyclicResidue z₀).re

/-- Every upper scaled cyclic readout has nonpositive real part. -/
theorem positiveJacobiAtomicCyclicScaledReadout_re_nonpos
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hz₀Real : z₀.im = 0) (n : ℕ) :
    (certificate.positiveJacobiAtomicCyclicScaledReadout
      z₀ hz₀Real n).re ≤ 0 := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  let lambda : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ n
  let hlambdaIm : lambda.im ≠ 0 := ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n)
  let hout : OutsideNonnegativeRealAxis lambda := Or.inl hlambdaIm
  let m : ℂ := certificate.positiveJacobiCyclicResolventReadout lambda hout
  have hmPos : 0 < m.im :=
    certificate.positiveJacobiCyclicResolventReadout_im_pos
      lambda hout (positiveJacobiAtomicSpectralApproach_im_pos
        (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n)
  change ((lambda - lambda₀) * m).re ≤ 0
  rw [Complex.mul_re]
  have hdeltaRe : (lambda - lambda₀).re = 0 := by
    simp [lambda, lambda₀, positiveJacobiAtomicSpectralApproach]
  have hdeltaIm : (lambda - lambda₀).im = ((n : ℝ) + 1)⁻¹ := by
    have hlambda₀Real : lambda₀.im = 0 :=
      inv_sq_im_eq_zero_of_im_eq_zero hz₀Real
    rw [Complex.sub_im,
      positiveJacobiAtomicSpectralApproach_im hlambda₀Real,
      hlambda₀Real, sub_zero]
  rw [hdeltaRe, hdeltaIm, zero_mul, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (by positivity) hmPos.le)

/-- The atom extracted from a native zero has strictly positive mass. -/
theorem positiveJacobiAtomicCyclicMass_pos
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    0 < positiveJacobiAtomicCyclicMass z₀ := by
  have htendsto := certificate.positiveJacobiAtomicCyclicScaledReadout_tendsto
    hzDomain hzero hz₀Real
  have hre : Tendsto
      (fun n : ℕ ↦
        (certificate.positiveJacobiAtomicCyclicScaledReadout
          z₀ hz₀Real n).re)
      atTop (nhds (positiveJacobiAtomicCyclicResidue z₀).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp htendsto
  have hnonpos : (positiveJacobiAtomicCyclicResidue z₀).re ≤ 0 :=
    le_of_tendsto' hre fun n ↦
      certificate.positiveJacobiAtomicCyclicScaledReadout_re_nonpos
        hz₀Real n
  have hreal := certificate.positiveJacobiAtomicCyclicResidue_im_eq_zero
    hzDomain hzero hz₀Real
  have hne := positiveJacobiAtomicCyclicResidue_ne_zero hzDomain hzero
  have hreNe : (positiveJacobiAtomicCyclicResidue z₀).re ≠ 0 := by
    intro hreZero
    apply hne
    apply Complex.ext <;> simp [hreZero, hreal]
  unfold positiveJacobiAtomicCyclicMass
  exact neg_pos.mpr (lt_of_le_of_ne hnonpos hreNe)

/-! ## Vector extraction -/

/-- Scaled off-axis cyclic resolvent vector whose limit is the atom. -/
def positiveJacobiAtomicCyclicScaledVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) :
    RealHilbertComplexification (EvenCarrier jet) :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let lambda := positiveJacobiAtomicSpectralApproach lambda₀ n
  let hlambda : OutsideNonnegativeRealAxis lambda :=
    Or.inl (ne_of_gt (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n))
  (lambda - lambda₀) •
    ((certificate.positiveJacobiCyclicResolventVector lambda hlambda :
      certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet))

/-- Domain-valued spelling of the same scaled resolvent vector. -/
def positiveJacobiAtomicCyclicScaledDomainVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) :
    certificate.completedJacobiEnergySelfAdjointData.complexification.domain :=
  let lambda₀ := (z₀ ^ 2)⁻¹
  let lambda := positiveJacobiAtomicSpectralApproach lambda₀ n
  let hlambda : OutsideNonnegativeRealAxis lambda :=
    Or.inl (ne_of_gt (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n))
  (lambda - lambda₀) •
    certificate.positiveJacobiCyclicResolventVector lambda hlambda

@[simp] theorem positiveJacobiAtomicCyclicScaledDomainVector_coe
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) :
    ((certificate.positiveJacobiAtomicCyclicScaledDomainVector
      z₀ hz₀Real n :
        certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
      RealHilbertComplexification (EvenCarrier jet)) =
      certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real n :=
  rfl

/-- Exact graph equation for a scaled vertical resolvent vector. -/
theorem positiveJacobiAtomicCyclicScaledDomainVector_equation
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z₀ : ℂ) (hz₀Real : z₀.im = 0) (n : ℕ) :
    certificate.completedJacobiEnergySelfAdjointData.complexification
        (certificate.positiveJacobiAtomicCyclicScaledDomainVector
          z₀ hz₀Real n) =
      (positiveJacobiAtomicSpectralApproach (z₀ ^ 2)⁻¹ n - (z₀ ^ 2)⁻¹) •
          certificate.positiveJacobiCyclicHead +
        positiveJacobiAtomicSpectralApproach (z₀ ^ 2)⁻¹ n •
          certificate.positiveJacobiAtomicCyclicScaledVector
            z₀ hz₀Real n := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  let lambda : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ n
  let hlambda : OutsideNonnegativeRealAxis lambda := Or.inl (ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n))
  let x := certificate.positiveJacobiCyclicResolventVector lambda hlambda
  have hx := certificate.positiveJacobiCyclicResolventVector_equation
    lambda hlambda
  unfold PositiveJacobiResolventEquation at hx
  change certificate.completedJacobiEnergySelfAdjointData.complexification
      ((lambda - lambda₀) • x) = _
  rw [LinearPMap.map_smul]
  have hAx :
      certificate.completedJacobiEnergySelfAdjointData.complexification x =
        certificate.positiveJacobiCyclicHead +
          lambda •
            (x : RealHilbertComplexification (EvenCarrier jet)) :=
    sub_eq_iff_eq_add.mp hx
  rw [hAx, smul_add]
  change
    (lambda - lambda₀) • certificate.positiveJacobiCyclicHead +
        (lambda - lambda₀) •
          (lambda •
            (x : RealHilbertComplexification (EvenCarrier jet))) =
      (lambda - lambda₀) • certificate.positiveJacobiCyclicHead +
        lambda •
          ((lambda - lambda₀) •
            (x : RealHilbertComplexification (EvenCarrier jet)))
  module

/-- Exact weighted formula for the Gram matrix of two scaled vertical
resolvent vectors. -/
theorem inner_positiveJacobiAtomicCyclicScaledVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hz₀Real : z₀.im = 0) (k n : ℕ) :
    inner ℂ
        (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real k)
        (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real n) =
      -((((k : ℝ) + 1)⁻¹ / (((n : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹) : ℝ) : ℂ) *
          certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real n -
        ((((n : ℝ) + 1)⁻¹ / (((n : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹) : ℝ) : ℂ) *
          (starRingEnd ℂ)
            (certificate.positiveJacobiAtomicCyclicScaledReadout
              z₀ hz₀Real k) := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  let lambdaN : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ n
  let lambdaK : ℂ := positiveJacobiAtomicSpectralApproach lambda₀ k
  let hN : OutsideNonnegativeRealAxis lambdaN := Or.inl (ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) n))
  let hK : OutsideNonnegativeRealAxis lambdaK := Or.inl (ne_of_gt
    (positiveJacobiAtomicSpectralApproach_im_pos
      (inv_sq_im_eq_zero_of_im_eq_zero hz₀Real) k))
  let xN := certificate.positiveJacobiCyclicResolventVector lambdaN hN
  let xK := certificate.positiveJacobiCyclicResolventVector lambdaK hK
  let mN := certificate.positiveJacobiCyclicResolventReadout lambdaN hN
  let mK := certificate.positiveJacobiCyclicResolventReadout lambdaK hK
  have hpolarized :=
    certificate.positiveJacobiCyclicResolventReadout_sub_conj_eq
      lambdaN lambdaK hN hK
  change mN - (starRingEnd ℂ) mK =
      (lambdaN - (starRingEnd ℂ) lambdaK) *
        inner ℂ
          ((xK : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
            RealHilbertComplexification (EvenCarrier jet))
          ((xN : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
            RealHilbertComplexification (EvenCarrier jet)) at hpolarized
  change inner ℂ
      ((lambdaK - lambda₀) •
        ((xK : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
          RealHilbertComplexification (EvenCarrier jet)))
      ((lambdaN - lambda₀) •
        ((xN : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
          RealHilbertComplexification (EvenCarrier jet))) = _
  rw [inner_smul_right
    ((lambdaK - lambda₀) •
      ((xK : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet)))
    (((xN : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
      RealHilbertComplexification (EvenCarrier jet)))
    (lambdaN - lambda₀)]
  rw [inner_smul_left
    (((xK : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
      RealHilbertComplexification (EvenCarrier jet)))
    (((xN : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
      RealHilbertComplexification (EvenCarrier jet)))
    (lambdaK - lambda₀)]
  have hz₀Conj : (starRingEnd ℂ) z₀ = z₀ := by
    apply Complex.ext
    · simp
    · simp [hz₀Real]
  have hlambda₀Conj : (starRingEnd ℂ) lambda₀ = lambda₀ := by
    dsimp [lambda₀]
    rw [map_inv₀, map_pow, hz₀Conj]
  have hetaN : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hetaK : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
  have hsum : ((n : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹ ≠ 0 :=
    ne_of_gt (add_pos hetaN hetaK)
  have hdeltaN : lambdaN - lambda₀ =
      Complex.I * ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    dsimp [lambdaN, positiveJacobiAtomicSpectralApproach]
    push_cast
    ring
  have hdeltaK : lambdaK - lambda₀ =
      Complex.I * ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    dsimp [lambdaK, positiveJacobiAtomicSpectralApproach]
    push_cast
    ring
  have hdenom : lambdaN - (starRingEnd ℂ) lambdaK =
      Complex.I *
        (((((n : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)) := by
    calc
      lambdaN - (starRingEnd ℂ) lambdaK =
          (lambdaN - lambda₀) - (starRingEnd ℂ) (lambdaK - lambda₀) := by
            rw [map_sub, hlambda₀Conj]
            ring
      _ = Complex.I *
          (((((n : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)) := by
            rw [hdeltaN, hdeltaK, map_mul]
            simp
            ring
  have hreadoutN :
      certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real n =
        (lambdaN - lambda₀) * mN := by rfl
  have hreadoutK :
      certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real k =
        (lambdaK - lambda₀) * mK := by rfl
  rw [hdeltaN] at hreadoutN
  rw [hdeltaK] at hreadoutK
  rw [hdenom] at hpolarized
  rw [hdeltaN, hdeltaK]
  rw [hreadoutN, hreadoutK]
  exact CyclicAtomicExtraction.verticalPolarizedScaledInner
    ((n : ℝ) + 1)⁻¹ ((k : ℝ) + 1)⁻¹ hsum mN mK
    (inner ℂ
      ((xK : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet))
      ((xN : certificate.completedJacobiEnergySelfAdjointData.complexification.domain) :
        RealHilbertComplexification (EvenCarrier jet))) hpolarized

/-- Pairwise Gram entries of the scaled resolvent vectors converge to the
strictly positive cyclic atomic mass. -/
theorem inner_positiveJacobiAtomicCyclicScaledVector_tendsto
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    Tendsto
      (fun p : ℕ × ℕ ↦ inner ℂ
        (certificate.positiveJacobiAtomicCyclicScaledVector
          z₀ hz₀Real p.1)
        (certificate.positiveJacobiAtomicCyclicScaledVector
          z₀ hz₀Real p.2))
      atTop (nhds (positiveJacobiAtomicCyclicMass z₀ : ℂ)) := by
  let g : ℕ → ℂ :=
    certificate.positiveJacobiAtomicCyclicScaledReadout z₀ hz₀Real
  let residue : ℂ := positiveJacobiAtomicCyclicResidue z₀
  let eta : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have hg : Tendsto g atTop (nhds residue) :=
    certificate.positiveJacobiAtomicCyclicScaledReadout_tendsto
      hzDomain hzero hz₀Real
  have hresidueConj : (starRingEnd ℂ) residue = residue :=
    certificate.positiveJacobiAtomicCyclicResidue_conj
      hzDomain hzero hz₀Real
  have hconj : Tendsto (fun n : ℕ ↦ (starRingEnd ℂ) (g n))
      atTop (nhds residue) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp hg
    rw [hresidueConj] at h
    exact h
  have heta : ∀ n, 0 < eta n := by
    intro n
    dsimp [eta]
    positivity
  have hweighted := CyclicAtomicExtraction.weightedPairTendsto
    g (fun n ↦ (starRingEnd ℂ) (g n)) residue eta hg hconj heta
  have hmass : (positiveJacobiAtomicCyclicMass z₀ : ℂ) = -residue := by
    have him := certificate.positiveJacobiAtomicCyclicResidue_im_eq_zero
      hzDomain hzero hz₀Real
    apply Complex.ext
    · simp [positiveJacobiAtomicCyclicMass, residue]
    · simp [residue, him]
  rw [hmass]
  apply hweighted.congr'
  exact Filter.Eventually.of_forall fun p ↦ by
    simpa [g, eta] using
      (certificate.inner_positiveJacobiAtomicCyclicScaledVector
        hz₀Real p.1 p.2).symm

/-- The positive Gram mass produces a nonzero ambient limit of the scaled
cyclic resolvent vectors. -/
theorem exists_positiveJacobiAtomicCyclicVector
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    ∃ v : RealHilbertComplexification (EvenCarrier jet),
      v ≠ 0 ∧ Tendsto
        (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real)
        atTop (nhds v) := by
  exact CyclicAtomicExtraction.exists_ne_zero_tendsto_of_inner_tendsto
    (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real)
    (certificate.positiveJacobiAtomicCyclicMass_pos
      hzDomain hzero hz₀Real)
    (certificate.inner_positiveJacobiAtomicCyclicScaledVector_tendsto
      hzDomain hzero hz₀Real)

/-- The graph images of scaled resolvent vectors converge to the eigenvalue
multiple of any ambient vector limit. -/
theorem positiveJacobiAtomicCyclicScaledDomainVector_image_tendsto
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hz₀Real : z₀.im = 0)
    {v : RealHilbertComplexification (EvenCarrier jet)}
    (hv : Tendsto
      (certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real)
      atTop (nhds v)) :
    Tendsto
      (fun n : ℕ ↦
        certificate.completedJacobiEnergySelfAdjointData.complexification
          (certificate.positiveJacobiAtomicCyclicScaledDomainVector
            z₀ hz₀Real n))
      atTop (nhds (((z₀ ^ 2)⁻¹ : ℂ) • v)) := by
  let lambda₀ : ℂ := (z₀ ^ 2)⁻¹
  have hlambda : Tendsto
      (positiveJacobiAtomicSpectralApproach lambda₀)
      atTop (nhds lambda₀) :=
    positiveJacobiAtomicSpectralApproach_tendsto lambda₀
  have hdelta : Tendsto
      (fun n : ℕ ↦ positiveJacobiAtomicSpectralApproach lambda₀ n - lambda₀)
      atTop (nhds 0) := by
    simpa using hlambda.sub_const lambda₀
  have hsource := hdelta.smul_const certificate.positiveJacobiCyclicHead
  have hvector := hlambda.smul hv
  have hsum := hsource.add hvector
  convert hsum using 1
  · funext n
    exact certificate.positiveJacobiAtomicCyclicScaledDomainVector_equation
      z₀ hz₀Real n
  · congr 1
    dsimp [lambda₀]
    module

/-- Atomic extraction at a real native zero: the reciprocal square is a point
eigenvalue of the already constructed positive Jacobi operator. -/
theorem completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_atomicExtraction
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0)
    (hz₀Real : z₀.im = 0) :
    LinearPMap.HasEigenvalue
      certificate.completedJacobiEnergySelfAdjointData.complexification
      (z₀ ^ 2)⁻¹ := by
  let A := certificate.completedJacobiEnergySelfAdjointData.complexification
  let u := certificate.positiveJacobiAtomicCyclicScaledVector z₀ hz₀Real
  let ud := certificate.positiveJacobiAtomicCyclicScaledDomainVector z₀ hz₀Real
  obtain ⟨v, hvne, hv⟩ :=
    certificate.exists_positiveJacobiAtomicCyclicVector
      hzDomain hzero hz₀Real
  have hAv :=
    certificate.positiveJacobiAtomicCyclicScaledDomainVector_image_tendsto
      hz₀Real hv
  have hpairs : Tendsto
      (fun n : ℕ ↦ (u n, A (ud n)))
      atTop (nhds (v, ((z₀ ^ 2)⁻¹ : ℂ) • v)) := by
    rw [nhds_prod_eq]
    simpa [u, ud, A] using hv.prodMk hAv
  have heventuallyGraph :
      ∀ᶠ n : ℕ in atTop, (u n, A (ud n)) ∈ A.graph :=
    Filter.Eventually.of_forall fun n ↦ by
      apply (LinearPMap.mem_graph_iff A).2
      refine ⟨ud n, ?_, rfl⟩
      exact certificate.positiveJacobiAtomicCyclicScaledDomainVector_coe
        z₀ hz₀Real n
  have hclosed :=
    certificate.completedJacobiEnergySelfAdjointData.complexification_isClosed
  change _root_.IsClosed (A.graph : Set
    (RealHilbertComplexification (EvenCarrier jet) ×
      RealHilbertComplexification (EvenCarrier jet))) at hclosed
  have hgraph : (v, ((z₀ ^ 2)⁻¹ : ℂ) • v) ∈ A.graph :=
    hclosed.mem_of_tendsto hpairs heventuallyGraph
  obtain ⟨x, hx, hAx⟩ := (LinearPMap.mem_graph_iff A).1 hgraph
  have hxv : (x : RealHilbertComplexification (EvenCarrier jet)) = v := by
    simpa using hx
  have hAxv : A x = ((z₀ ^ 2)⁻¹ : ℂ) • v := by
    simpa using hAx
  refine ⟨x, ?_, ?_⟩
  · intro hxzero
    apply hvne
    rw [← hxv, hxzero]
  · calc
      A x = ((z₀ ^ 2)⁻¹ : ℂ) • v := hAxv
      _ = ((z₀ ^ 2)⁻¹ : ℂ) •
          (x : RealHilbertComplexification (EvenCarrier jet)) := by rw [hxv]

/-- Every native zero in the natural height strip supplies a genuine atom of
the concrete cyclic Jacobi operator.  No pure-point or spectral-measure
hypothesis is assumed. -/
theorem completedNativeOperator_zero_hasEigenvalue_inv_sq
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    LinearPMap.HasEigenvalue
      certificate.completedJacobiEnergySelfAdjointData.complexification
      (z₀ ^ 2)⁻¹ := by
  have hz₀Real :=
    certificate.completedNativeOperator_zero_im_eq_zero_of_positiveJacobiResolvent
      hzDomain hzero
  exact
    certificate.completedJacobiEnergyComplexification_hasEigenvalue_inv_sq_of_atomicExtraction
      hzDomain hzero hz₀Real

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- The extracted Jacobi atom transports through the already constructed
reciprocal square root to the reduced signed-height operator. -/
theorem reducedSignedHeightComplexification_hasEigenvalue_of_atomicExtraction
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z₀ : ℂ} (hzDomain : z₀ ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z₀ = 0) :
    LinearPMap.HasEigenvalue
      certificate.toReducedMaximalSelfAdjointHeightData.selfAdjointData.complexification
      z₀ := by
  let data := certificate.completedJacobiEnergySelfAdjointData
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact completedNativeOperatorCharacteristic_zero_ne_zero hzero
  have heigen :
      LinearPMap.HasEigenvalue data.complexification (z₀ ^ 2)⁻¹ :=
    certificate.completedNativeOperator_zero_hasEigenvalue_inv_sq
      hzDomain hzero
  have hlambdaIm : ((z₀ ^ 2)⁻¹).im = 0 :=
    LinearPMap.eigenvalue_im_eq_zero_of_isSelfAdjoint
      data.complexification_isSelfAdjoint heigen
  let lambda : ℝ := ((z₀ ^ 2)⁻¹).re
  have hlambdaComplex : (lambda : ℂ) = (z₀ ^ 2)⁻¹ := by
    apply Complex.ext
    · rfl
    · exact hlambdaIm.symm
  have heigenRealComplex :
      LinearPMap.HasEigenvalue data.complexification (lambda : ℂ) := by
    rw [hlambdaComplex]
    exact heigen
  obtain ⟨x, hx, hAx⟩ :=
    LinearPMap.hasRealEigenvalue_of_complexification_hasEigenvalue
      heigenRealComplex
  have hlambda : lambda ≠ 0 := by
    intro hlambdaZero
    have : ((z₀ ^ 2)⁻¹ : ℂ) = 0 := by
      rw [← hlambdaComplex, hlambdaZero]
      norm_num
    exact inv_ne_zero (pow_ne_zero 2 hz₀) this
  have hroot : z₀ ^ 2 * (lambda : ℂ) = 1 := by
    rw [hlambdaComplex]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hz₀)
  let hrep := completedGreenJet_gramRepresentation certificate.momentKernel
  let heven := completedGreenJet_even_linearIndependent certificate.evenIndependent
  let hodd := completedGreenJet_odd_linearIndependent certificate.oddIndependent
  let square := closedGreenJetEnergyAdjointSquare hrep heven hodd
  have hAeq : data.operator = square := by
    rfl
  have heigenSquare : ∃ xs : square.domain,
      (xs : EvenCarrier jet) ≠ 0 ∧
        square xs = lambda • (xs : EvenCarrier jet) := by
    rw [← hAeq]
    exact ⟨x, hx, hAx⟩
  obtain ⟨xs, hxs, hSquareXs⟩ := heigenSquare
  have hsigned :=
    closedGreenJetReducedReciprocalSignedHeight_hasEigenvalue_of_adjointSquare_complex
      hrep heven hodd hlambda hroot xs hxs hSquareXs
  change LinearPMap.HasEigenvalue
    (closedGreenJetReducedReciprocalSignedHeightData
      hrep heven hodd).selfAdjointData.complexification z₀
  exact hsigned

end CompletedNativeRealHPCarrierCertificate

end

end CarrySelfAdjointOperator
