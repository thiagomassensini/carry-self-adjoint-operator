import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz
import CarrySelfAdjointOperator.CompletedNativeSignedGeneratorResolvent
import CarrySelfAdjointOperator.CompletedC3CoisometricAmbientMomentGate
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Signed-generator Gram realization of the completed-native Herglotz kernel

For a formally self-adjoint operator `K`, height-resolvent vectors satisfying

`x_z - z K x_z = e₀`

obey the polarized identity

`w ⟪e₀, x_w⟫ - conj (z ⟪e₀, x_z⟫)
    = (w - conj z) ⟪x_z, x_w⟫`.

The completed-native signed generator already realizes the logarithmic
derivative by `a(z) = 2 z ⟪e₀, x_z⟫` on the upper height cone.  Consequently
its Herglotz kernel is exactly the positive Gram kernel

`K_a(z,w) = 2 ⟪x_z, x_w⟫`.

This is a conditional realization from a completed-native real HP carrier
certificate.  It does not construct that certificate independently of the
all-order moment gate.
-/

open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Polarized identity for the height form `x - z A x = source` of a
formally self-adjoint resolvent equation. -/
theorem heightResolventWeightedReadout_sub_conj_eq
    {A : H →ₗ.[ℂ] H} (hformal : A.IsFormalAdjoint A)
    {z w : ℂ} {source : H} (x y : A.domain)
    (hx : (x : H) - z • A x = source)
    (hy : (y : H) - w • A y = source) :
    w * inner ℂ source (y : H) -
        conj (z * inner ℂ source (x : H)) =
      (w - conj z) * inner ℂ (x : H) (y : H) := by
  calc
    w * inner ℂ source (y : H) -
        conj (z * inner ℂ source (x : H)) =
      w * inner ℂ ((x : H) - z • A x) (y : H) -
        conj z * inner ℂ (x : H) ((y : H) - w • A y) := by
          rw [hx, hy, map_mul, inner_conj_symm]
    _ = (w - conj z) * inner ℂ (x : H) (y : H) := by
      rw [inner_sub_left, inner_smul_left, inner_sub_right,
        inner_smul_right, hformal x y]
      ring

end LinearPMap

namespace CompletedNativeRealHPCarrierCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {jet : (ℕ ⊕ ℕ) → E}

local instance signedGeneratorHerglotzEvenCarrierCompleteSpace :
    CompleteSpace (EvenCarrier jet) :=
  (greenJetEvenHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

local instance signedGeneratorHerglotzOddCarrierCompleteSpace :
    CompleteSpace (OddCarrier jet) :=
  (greenJetOddHilbertSubspace_isClosed
    (completedJet jet)).completeSpace_coe

/-- Off the real axis, the proof-independent boundary readout is literally
the cyclic inner product against the selected height-resolvent vector. -/
theorem signedGeneratorHeightGlobalBoundaryReadout_eq_inner
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    (z : ℂ) (hz : z.im ≠ 0) :
    certificate.signedGeneratorHeightGlobalBoundaryReadout z =
      inner ℂ certificate.completedSignedGeneratorCyclicHead
        (certificate.signedGeneratorHeightGlobalResolventVector z hz :
          RealHilbertComplexification (SignedGeneratorCarrier jet)) := by
  rw [signedGeneratorHeightGlobalBoundaryReadout,
    signedGeneratorHeightGlobalResolventState, dif_pos hz]
  rfl

/-- The division-free native ODE identifies the Herglotz coordinate with
twice the height-weighted cyclic readout throughout the regular upper cone. -/
theorem completedNativeLogDerivativeHerglotzCoordinate_eq_signedGeneratorReadout
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z : ℂ} (hzUpper : z ∈ completedNativeUpperHeightCone)
    (hzIm : z.im ≠ 0)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeLogDerivativeHerglotzCoordinate z =
      ((2 : ℂ) * z) *
        certificate.signedGeneratorHeightGlobalBoundaryReadout z := by
  have hdefect : certificate.signedGeneratorWeylODEDefect z = 0 :=
    certificate.signedGeneratorWeylODEDefect_eq_zero_on_upper hzUpper
  unfold completedNativeLogDerivativeHerglotzCoordinate
  apply (div_eq_iff hF).2
  change -deriv completedNativeOperatorCharacteristic z =
    ((2 : ℂ) * z) *
      certificate.signedGeneratorHeightGlobalBoundaryReadout z *
        completedNativeOperatorCharacteristic z
  unfold signedGeneratorWeylODEDefect at hdefect
  rw [signedGeneratorHeightGluedBoundaryReadout, if_neg hzIm] at hdefect
  linear_combination -hdefect

/-- Polarized numerator identity for the native logarithmic derivative.
The right side is a positive Gram numerator of signed-generator height
resolvent vectors. -/
theorem completedNativeLogDerivativeHerglotzNumerator_eq_signedGeneratorGram
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z w : ℂ}
    (hzUpper : z ∈ completedNativeUpperHeightCone)
    (hwUpper : w ∈ completedNativeUpperHeightCone)
    (hzIm : z.im ≠ 0) (hwIm : w.im ≠ 0)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    completedNativeLogDerivativeHerglotzCoordinate w -
        conj (completedNativeLogDerivativeHerglotzCoordinate z) =
      (w - conj z) *
        (2 * inner ℂ
          (certificate.signedGeneratorHeightGlobalResolventVector z hzIm :
            RealHilbertComplexification (SignedGeneratorCarrier jet))
          (certificate.signedGeneratorHeightGlobalResolventVector w hwIm :
            RealHilbertComplexification (SignedGeneratorCarrier jet))) := by
  let A := certificate.completedSignedGeneratorData.complexification
  let x := certificate.signedGeneratorHeightGlobalResolventVector z hzIm
  let y := certificate.signedGeneratorHeightGlobalResolventVector w hwIm
  have hformal : A.IsFormalAdjoint A := by
    have hadjoint := A.adjoint_isFormalAdjoint
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp
      certificate.completedSignedGeneratorData.complexification_isSelfAdjoint]
      at hadjoint
    exact hadjoint
  have hheight := LinearPMap.heightResolventWeightedReadout_sub_conj_eq
    hformal x y
    (certificate.signedGeneratorHeightGlobalResolventVector_equation z hzIm)
    (certificate.signedGeneratorHeightGlobalResolventVector_equation w hwIm)
  simp only [map_mul] at hheight
  rw [certificate.completedNativeLogDerivativeHerglotzCoordinate_eq_signedGeneratorReadout
      hzUpper hzIm hzF,
    certificate.completedNativeLogDerivativeHerglotzCoordinate_eq_signedGeneratorReadout
      hwUpper hwIm hwF,
    certificate.signedGeneratorHeightGlobalBoundaryReadout_eq_inner z hzIm,
    certificate.signedGeneratorHeightGlobalBoundaryReadout_eq_inner w hwIm]
  simp only [map_mul, map_ofNat]
  change
    ((2 : ℂ) * w) * inner ℂ certificate.completedSignedGeneratorCyclicHead
        (y : RealHilbertComplexification (SignedGeneratorCarrier jet)) -
      2 * conj z * conj
        (inner ℂ certificate.completedSignedGeneratorCyclicHead
          (x : RealHilbertComplexification (SignedGeneratorCarrier jet))) =
    (w - conj z) *
      (2 * inner ℂ
        (x : RealHilbertComplexification (SignedGeneratorCarrier jet))
        (y : RealHilbertComplexification (SignedGeneratorCarrier jet)))
  linear_combination 2 * hheight

/-- On every regular pair in the upper height cone, the completed-native
Herglotz kernel is exactly twice a signed-generator resolvent Gram entry. -/
theorem completedNativeLogDerivativeHerglotzKernel_eq_signedGeneratorGram
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z w : ℂ}
    (hzUpper : z ∈ completedNativeUpperHeightCone)
    (hwUpper : w ∈ completedNativeUpperHeightCone)
    (hzIm : z.im ≠ 0) (hwIm : w.im ≠ 0)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    completedNativeLogDerivativeHerglotzKernel z w =
      2 * inner ℂ
        (certificate.signedGeneratorHeightGlobalResolventVector z hzIm :
          RealHilbertComplexification (SignedGeneratorCarrier jet))
        (certificate.signedGeneratorHeightGlobalResolventVector w hwIm :
          RealHilbertComplexification (SignedGeneratorCarrier jet)) := by
  unfold completedNativeLogDerivativeHerglotzKernel
  rw [certificate.completedNativeLogDerivativeHerglotzNumerator_eq_signedGeneratorGram
    hzUpper hwUpper hzIm hwIm hzF hwF]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsep)

/-- Certificate-only form of the Gram identity.  The certificate's global
Jacobi continuation already excludes characteristic zeros in the upper cone,
so no separate regularity premise remains. -/
theorem completedNativeLogDerivativeHerglotzKernel_eq_signedGeneratorStateGram_on_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {z w : ℂ}
    (hzUpper : z ∈ completedNativeUpperHeightCone)
    (hwUpper : w ∈ completedNativeUpperHeightCone)
    (hzIm : z.im ≠ 0) (hwIm : w.im ≠ 0)
    (hsep : w ≠ conj z) :
    completedNativeLogDerivativeHerglotzKernel z w =
      2 * inner ℂ
        (certificate.signedGeneratorHeightGlobalResolventState z)
        (certificate.signedGeneratorHeightGlobalResolventState w) := by
  rw [certificate.completedNativeLogDerivativeHerglotzKernel_eq_signedGeneratorGram
    hzUpper hwUpper hzIm hwIm
    (certificate.completedNativeOperatorCharacteristic_ne_zero_on_upper hzUpper)
    (certificate.completedNativeOperatorCharacteristic_ne_zero_on_upper hwUpper)
    hsep]
  simp [signedGeneratorHeightGlobalResolventState, hzIm, hwIm]

/-- Every finite restriction of the native logarithmic-derivative Herglotz
kernel to the open upper height cone is positive semidefinite once a real HP
carrier certificate is available. -/
theorem completedNativeLogDerivativeHerglotzKernel_posSemidef_on_upper
    (certificate : CompletedNativeRealHPCarrierCertificate jet)
    {ι : Type*} [Finite ι]
    (point : ι → ℂ)
    (hUpper : ∀ i, point i ∈ completedNativeUpperHeightCone)
    (hImPos : ∀ i, 0 < (point i).im) :
    (Matrix.of fun i j =>
      completedNativeLogDerivativeHerglotzKernel (point i) (point j)).PosSemidef := by
  let state : ι → RealHilbertComplexification (SignedGeneratorCarrier jet) :=
    fun i => certificate.signedGeneratorHeightGlobalResolventState (point i)
  have hmatrix :
      Matrix.of (fun i j =>
          completedNativeLogDerivativeHerglotzKernel (point i) (point j)) =
        (2 : ℝ) • Matrix.gram ℂ state := by
    ext i j
    have hsep : point j ≠ conj (point i) := by
      intro heq
      have him := congrArg Complex.im heq
      rw [Complex.conj_im] at him
      have hi := hImPos i
      have hj := hImPos j
      linarith
    change completedNativeLogDerivativeHerglotzKernel (point i) (point j) =
      (2 : ℝ) • inner ℂ (state i) (state j)
    rw [certificate.completedNativeLogDerivativeHerglotzKernel_eq_signedGeneratorStateGram_on_upper
      (hUpper i) (hUpper j) (ne_of_gt (hImPos i)) (ne_of_gt (hImPos j)) hsep]
    simp [state]
  rw [hmatrix]
  exact (Matrix.posSemidef_gram ℂ state).smul (by norm_num)

/-- A real HP carrier certificate closes the radial Herglotz gate.  The
qualification is essential: the certificate itself contains the exact
all-order moment Gram realization. -/
theorem canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_of_certificate
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite := by
  intro N
  have hUpper : ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
        completedNativeUpperHeightCone := by
    rw [eventually_all]
    intro i
    filter_upwards [canonicalCompletedC3RadialTiltPoint_eventually_admissible i]
      with k hk
    have hbounds := mem_completedNativeHeightDomain_iff_im_bounds.mp hk.1
    exact Or.inr
      ⟨canonicalCompletedC3RadialTiltPoint_im_pos k i, hbounds.2⟩
  filter_upwards [hUpper] with k hk
  exact certificate.completedNativeLogDerivativeHerglotzKernel_posSemidef_on_upper
    (fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i)
    hk
    (fun i => canonicalCompletedC3RadialTiltPoint_im_pos k i)

end CompletedNativeRealHPCarrierCertificate

/-! ## Exact relation with the all-order Stieltjes gate -/

/-- Strict Stieltjes positivity constructs a signed-generator realization and
hence proves every eventual radial Herglotz section positive semidefinite. -/
theorem canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_of_stieltjesPositivity
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_of_certificate

/-- Exact gate audit: radial Herglotz semidefiniteness is the closed part of
the strict Stieltjes condition; finite-section nondegeneracy is precisely the
remaining strictness input. -/
theorem canonicalCompletedNativeStieltjesPositivity_iff_radialHerglotz_and_nondegenerate :
    CanonicalCompletedNativeStieltjesPositivity ↔
      CanonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite ∧
        CanonicalCompletedNativeHankelPairNondegenerate := by
  constructor
  · intro hpos
    exact
      ⟨canonicalCompletedNativeRadialHerglotzEventuallyPosSemidefinite_of_stieltjesPositivity
          hpos,
        (canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate.mp
          hpos).2⟩
  · rintro ⟨hHerglotz, hnondegenerate⟩
    exact
      canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate.mpr
        ⟨canonicalCompletedNativeStieltjesPosSemidefinite_of_radialHerglotz
            hHerglotz,
          hnondegenerate⟩

/-! ## Unbundled first-order shadow -/

/-- The central curvature/ruler closes the one-point Herglotz section without
assuming an all-order HP certificate.  This is the precise low-order content
of `a'(0) = 2 h₀`; genuinely polarized higher sections are not consequences
of this scalar premise. -/
theorem canonicalCompletedNativeRadialHerglotzSampleMatrix_one_eventually_posSemidef_of_moment_zero_pos
    (hmoment : 0 < canonicalCompletedNativeLogDerivativeMoment 0) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 1).PosSemidef := by
  have hcontractive :=
    canonicalCompletedNativeRadialChiralMultiplierContractiveAt_one_eventually_of_moment_zero_pos
      hmoment
  have hpick : ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 1).PosSemidef := by
    filter_upwards [hcontractive] with k hk
    exact
      (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
        k 1).mp hk
  have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin 1,
      completedNativeOperatorCharacteristic
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
    rw [eventually_all]
    intro i
    filter_upwards [
      (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
        completedNativeChiralPickFactorization_eventually_regular] with k hk
    exact ⟨hk.2.1, hk.2.2⟩
  filter_upwards [hpick, hregular] with k hk hreg
  exact
    (canonicalCompletedNativeRadialChiralPickSampleMatrix_posSemidef_iff_herglotz
      k 1 hreg).mp hk

/-- Explicit gate transition from the previously isolated central
coisometric curvature identity to the first radial Herglotz section. -/
theorem canonicalCompletedNativeRadialHerglotzSampleMatrix_one_eventually_posSemidef_of_transverseCurvature
    (hcurvature :
      iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
        4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 1).PosSemidef :=
  canonicalCompletedNativeRadialHerglotzSampleMatrix_one_eventually_posSemidef_of_moment_zero_pos
    (canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_transverseCurvature
      hcurvature)

end

end CarrySelfAdjointOperator
