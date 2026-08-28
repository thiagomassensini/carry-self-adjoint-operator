import CarrySelfAdjointOperator.CompletedNativePositiveJacobiResolventAnalytic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Canonical moment realization of the completed-native Jacobi operator

This module isolates the operator-theoretic gate from any particular Green
carrier.  Strict positivity of the unshifted and shifted Hankel towers builds
the two canonical moment Hilbert spaces, their orthogonal parity jet, and the
existing completed-native HP certificate.
-/

namespace CarrySelfAdjointOperator

noncomputable section

open scoped InnerProductSpace

/-- The purely momental gate for the completed-native Stieltjes construction. -/
def CanonicalCompletedNativeStieltjesPositivity : Prop :=
  ∀ N : ℕ,
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef ∧
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosDef

/-- Every carrier-honest completed-native HP certificate supplies the purely
momental Stieltjes positivity gate. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_certificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (certificate : CompletedNativeRealHPCarrierCertificate jet) :
    CanonicalCompletedNativeStieltjesPositivity := by
  intro N
  exact certificate.hankelPair_posDef N

/-- Infinite Hankel matrix with a selectable moment offset. -/
def infiniteShiftedHankel (moments : ℕ → ℝ) (offset : ℕ) : Matrix ℕ ℕ ℝ :=
  fun i j => moments (i + j + offset)

/-- Positivity of every finite Hankel prefix promotes to positivity of the
infinite finitely-supported quadratic form. -/
theorem infiniteShiftedHankel_posDef_of_prefixes
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : ∀ N : ℕ,
      (Matrix.of fun i j : Fin N => moments ((i : ℕ) + (j : ℕ) + offset)).PosDef) :
    (infiniteShiftedHankel moments offset).PosDef := by
  constructor
  · ext i j
    simp [infiniteShiftedHankel, add_comm]
  · intro x hx
    obtain ⟨N, hsupport⟩ := x.support.exists_nat_subset_range
    let e : Fin N ↪ ℕ := ⟨fun i => (i : ℕ), Fin.val_injective⟩
    have hsupport' : (x.support : Set ℕ) ⊆ Set.range e := by
      intro n hn
      have hnN : n < N := Finset.mem_range.mp (hsupport hn)
      exact ⟨⟨n, hnN⟩, rfl⟩
    let y : Fin N →₀ ℝ := Finsupp.comapDomain e x e.injective.injOn
    have hembed : Finsupp.embDomain e y = x := by
      exact Finsupp.embDomain_comapDomain hsupport'
    have hy : y ≠ 0 := by
      intro hy0
      apply hx
      simp [← hembed, hy0]
    have hfinite := (hpos N).2 hy
    rw [← hembed]
    simpa [infiniteShiftedHankel, y, e, Finsupp.embDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index,
      add_mul, mul_add] using hfinite

/-- Algebraic moment space before Hilbert completion.  The positivity proof is
part of the type so its norm and inner product are canonical for that proof. -/
@[reducible] def MomentPreHilbertSpace (moments : ℕ → ℝ) (offset : ℕ)
    (_hpos : (infiniteShiftedHankel moments offset).PosDef) :=
  ℕ →₀ ℝ

instance momentPreHilbertSpaceAddCommGroup
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    AddCommGroup (MomentPreHilbertSpace moments offset hpos) :=
  inferInstanceAs (AddCommGroup (ℕ →₀ ℝ))

instance momentPreHilbertSpaceModule
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    Module ℝ (MomentPreHilbertSpace moments offset hpos) :=
  inferInstanceAs (Module ℝ (ℕ →₀ ℝ))

/-- Positive-definite inner-product core of the algebraic moment space. -/
@[reducible] def momentPreHilbertSpaceCore
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    InnerProductSpace.Core ℝ (MomentPreHilbertSpace moments offset hpos) where
  inner x y :=
    x.sum fun i xi => y.sum fun j yj =>
      xi * infiniteShiftedHankel moments offset i j * yj
  conj_inner_symm x y := by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← hpos.isHermitian.apply]
    rw [starRingEnd_apply, star_trivial]
    rw [star_trivial]
    ring
  re_inner_nonneg x := hpos.posSemidef.2 x
  add_left _ _ _ := by
    rw [Finsupp.sum_add_index'] <;>
      simp [← Finsupp.sum_add, add_mul]
  smul_left _ _ _ := by
    rw [Finsupp.sum_smul_index] <;>
      simp [Finsupp.mul_sum, ← mul_assoc]
  definite x hx := by
    by_contra hx0
    have hstrict := hpos.2 hx0
    have hstrict' :
        0 < x.sum fun i xi => x.sum fun j yj =>
          xi * infiniteShiftedHankel moments offset i j * yj := by
      simpa using hstrict
    rw [hx] at hstrict'
    exact (lt_irrefl 0) hstrict'

instance momentPreHilbertSpaceNormedAddCommGroup
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    NormedAddCommGroup (MomentPreHilbertSpace moments offset hpos) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ
    (MomentPreHilbertSpace moments offset hpos) _ _ _
    (momentPreHilbertSpaceCore moments offset hpos)

instance momentPreHilbertSpaceInnerProductSpace
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    InnerProductSpace ℝ (MomentPreHilbertSpace moments offset hpos) :=
  InnerProductSpace.ofCore
    { momentPreHilbertSpaceCore moments offset hpos with }

/-- Canonical algebraic basis vector in a moment pre-Hilbert space. -/
def momentPreHilbertBasisVector
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) (n : ℕ) :
    MomentPreHilbertSpace moments offset hpos :=
  Finsupp.single n 1

@[simp] theorem inner_momentPreHilbertBasisVector
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) (i j : ℕ) :
    inner ℝ
      (momentPreHilbertBasisVector moments offset hpos i)
      (momentPreHilbertBasisVector moments offset hpos j) =
        moments (i + j + offset) := by
  change (Finsupp.single i 1).sum (fun i xi =>
    (Finsupp.single j 1).sum fun j yj =>
      xi * infiniteShiftedHankel moments offset i j * yj) = _
  simp [infiniteShiftedHankel]

/-- Completed canonical Hilbert space associated to one shifted Hankel tower. -/
abbrev MomentHilbertSpace
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :=
  UniformSpace.Completion (MomentPreHilbertSpace moments offset hpos)

/-- Canonical basis vector after Hilbert completion. -/
def momentHilbertBasisVector
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) (n : ℕ) :
    MomentHilbertSpace moments offset hpos :=
  (momentPreHilbertBasisVector moments offset hpos n :
    MomentHilbertSpace moments offset hpos)

@[simp] theorem inner_momentHilbertBasisVector
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) (i j : ℕ) :
    inner ℝ
      (momentHilbertBasisVector moments offset hpos i)
      (momentHilbertBasisVector moments offset hpos j) =
        moments (i + j + offset) := by
  simp [momentHilbertBasisVector]

/-- The completed canonical basis remains globally linearly independent. -/
theorem momentHilbertBasisVector_linearIndependent
    (moments : ℕ → ℝ) (offset : ℕ)
    (hpos : (infiniteShiftedHankel moments offset).PosDef) :
    LinearIndependent ℝ (momentHilbertBasisVector moments offset hpos) := by
  have hsingle : LinearIndependent ℝ
      (fun n : ℕ =>
        momentPreHilbertBasisVector moments offset hpos n) := by
    simpa [momentPreHilbertBasisVector] using
      (Finsupp.linearIndependent_single_one ℝ ℕ)
  have hmapped := hsingle.map'
    (UniformSpace.Completion.toComplₗᵢ :
      MomentPreHilbertSpace moments offset hpos →ₗᵢ[ℝ]
        MomentHilbertSpace moments offset hpos).toLinearMap
    (LinearMap.ker_eq_bot.mpr
      (UniformSpace.Completion.toComplₗᵢ :
        MomentPreHilbertSpace moments offset hpos →ₗᵢ[ℝ]
          MomentHilbertSpace moments offset hpos).injective)
  change LinearIndependent ℝ (fun n : ℕ =>
    (momentPreHilbertBasisVector moments offset hpos n :
      MomentHilbertSpace moments offset hpos))
  exact hmapped

/-- Infinite positive-definite unshifted Hankel form selected by the moment
positivity gate. -/
theorem canonicalCompletedNativeEvenInfiniteHankelPosDef
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    (infiniteShiftedHankel
      canonicalCompletedNativeLogDerivativeMoment 0).PosDef :=
  infiniteShiftedHankel_posDef_of_prefixes
    canonicalCompletedNativeLogDerivativeMoment 0 fun N => by
      have hN := (hpos N).1
      change (Matrix.of fun i j : Fin N =>
        canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ) + 0)).PosDef
      change (Matrix.of fun i j : Fin N =>
        canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ) + 0)).PosDef at hN
      exact hN

/-- Infinite positive-definite shifted Hankel form selected by the moment
positivity gate. -/
theorem canonicalCompletedNativeOddInfiniteHankelPosDef
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    (infiniteShiftedHankel
      canonicalCompletedNativeLogDerivativeMoment 1).PosDef :=
  infiniteShiftedHankel_posDef_of_prefixes
    canonicalCompletedNativeLogDerivativeMoment 1 fun N => by
      have hN := (hpos N).2
      change (Matrix.of fun i j : Fin N =>
        canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ) + 1)).PosDef
      change (Matrix.of fun i j : Fin N =>
        canonicalCompletedNativeLogDerivativeMoment
          ((i : ℕ) + (j : ℕ) + 1)).PosDef at hN
      exact hN

/-- Canonical algebraic pre-Hilbert carrier for the unshifted moments. -/
abbrev CanonicalCompletedNativeEvenMomentPreHilbertSpace
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  MomentPreHilbertSpace canonicalCompletedNativeLogDerivativeMoment 0
    (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos)

/-- Canonical algebraic pre-Hilbert carrier for the shifted moments. -/
abbrev CanonicalCompletedNativeOddMomentPreHilbertSpace
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  MomentPreHilbertSpace canonicalCompletedNativeLogDerivativeMoment 1
    (canonicalCompletedNativeOddInfiniteHankelPosDef hpos)

/-- Completed canonical Hilbert carrier for the unshifted moments. -/
abbrev CanonicalCompletedNativeEvenMomentHilbertSpace
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  MomentHilbertSpace canonicalCompletedNativeLogDerivativeMoment 0
    (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos)

/-- Completed canonical Hilbert carrier for the shifted moments. -/
abbrev CanonicalCompletedNativeOddMomentHilbertSpace
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  MomentHilbertSpace canonicalCompletedNativeLogDerivativeMoment 1
    (canonicalCompletedNativeOddInfiniteHankelPosDef hpos)

/-- Orthogonal direct sum of the two canonical completed moment sectors. -/
abbrev CanonicalCompletedNativeStieltjesCarrier
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  WithLp 2
    (CanonicalCompletedNativeEvenMomentHilbertSpace hpos ×
      CanonicalCompletedNativeOddMomentHilbertSpace hpos)

/-- Canonical parity jet in the orthogonal sum of the two moment sectors. -/
def canonicalCompletedNativeStieltjesJet
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    (ℕ ⊕ ℕ) → CanonicalCompletedNativeStieltjesCarrier hpos
  | Sum.inl n => WithLp.toLp 2
      (momentHilbertBasisVector
        canonicalCompletedNativeLogDerivativeMoment 0
        (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos) n, 0)
  | Sum.inr n => WithLp.toLp 2
      (0, momentHilbertBasisVector
        canonicalCompletedNativeLogDerivativeMoment 1
        (canonicalCompletedNativeOddInfiniteHankelPosDef hpos) n)

/-- The canonical direct-sum jet realizes all four parity blocks of the
completed-native moment kernel. -/
theorem canonicalCompletedNativeStieltjesJet_momentKernel
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (canonicalCompletedNativeStieltjesJet hpos) := by
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [greenWronskianMomentKernel, Matrix.gram,
      canonicalCompletedNativeStieltjesJet, WithLp.prod_inner_apply]

/-- The even and odd canonical moment sectors are orthogonal in this
orientation. -/
@[simp] theorem canonicalCompletedNativeStieltjesJet_even_odd_inner_eq_zero
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (i j : ℕ) :
    inner ℝ
      (canonicalCompletedNativeStieltjesJet hpos (Sum.inl i))
      (canonicalCompletedNativeStieltjesJet hpos (Sum.inr j)) = 0 := by
  simp [canonicalCompletedNativeStieltjesJet, WithLp.prod_inner_apply]

/-- The odd and even canonical moment sectors are orthogonal in the reverse
orientation as well. -/
@[simp] theorem canonicalCompletedNativeStieltjesJet_odd_even_inner_eq_zero
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (i j : ℕ) :
    inner ℝ
      (canonicalCompletedNativeStieltjesJet hpos (Sum.inr i))
      (canonicalCompletedNativeStieltjesJet hpos (Sum.inl j)) = 0 := by
  simp [canonicalCompletedNativeStieltjesJet, WithLp.prod_inner_apply]

/-- The even canonical moment jets are globally linearly independent. -/
theorem canonicalCompletedNativeStieltjesJet_even_linearIndependent
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    LinearIndependent ℝ
      (fun n : ℕ => canonicalCompletedNativeStieltjesJet hpos (Sum.inl n)) := by
  apply LinearIndependent.of_comp
    (WithLp.fstL 2 ℝ
      (CanonicalCompletedNativeEvenMomentHilbertSpace hpos)
      (CanonicalCompletedNativeOddMomentHilbertSpace hpos)).toLinearMap
  simpa [Function.comp_def, canonicalCompletedNativeStieltjesJet] using
    (momentHilbertBasisVector_linearIndependent
      canonicalCompletedNativeLogDerivativeMoment 0
      (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos))

/-- The odd canonical moment jets are globally linearly independent. -/
theorem canonicalCompletedNativeStieltjesJet_odd_linearIndependent
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    LinearIndependent ℝ
      (fun n : ℕ => canonicalCompletedNativeStieltjesJet hpos (Sum.inr n)) := by
  apply LinearIndependent.of_comp
    (WithLp.sndL 2 ℝ
      (CanonicalCompletedNativeEvenMomentHilbertSpace hpos)
      (CanonicalCompletedNativeOddMomentHilbertSpace hpos)).toLinearMap
  simpa [Function.comp_def, canonicalCompletedNativeStieltjesJet] using
    (momentHilbertBasisVector_linearIndependent
      canonicalCompletedNativeLogDerivativeMoment 1
      (canonicalCompletedNativeOddInfiniteHankelPosDef hpos))

/-- Purely momental construction of the carrier-honest completed-native HP
certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet hpos) where
  momentKernel := canonicalCompletedNativeStieltjesJet_momentKernel hpos
  evenIndependent :=
    canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos
  oddIndependent :=
    canonicalCompletedNativeStieltjesJet_odd_linearIndependent hpos

/-! ## Exact logical equivalence -/

/-- A bundled real Hilbert carrier carrying a completed-native HP
certificate.  No preferred analytic state is part of this package. -/
structure CompletedNativeRealHPCarrierRealization where
  carrier : Type
  normedAddCommGroup : NormedAddCommGroup carrier
  innerProductSpace :
    letI := normedAddCommGroup
    InnerProductSpace ℝ carrier
  jet : (ℕ ⊕ ℕ) → carrier
  certificate :
    letI := normedAddCommGroup
    letI := innerProductSpace
    CompletedNativeRealHPCarrierCertificate jet

/-- The canonical direct-sum moment realization bundled as one existential
HP carrier. -/
def canonicalCompletedNativeStieltjesRealization
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    CompletedNativeRealHPCarrierRealization where
  carrier := CanonicalCompletedNativeStieltjesCarrier hpos
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  jet := canonicalCompletedNativeStieltjesJet hpos
  certificate :=
    completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos

/-- Strict positivity of the two canonical Hankel towers is equivalent to
the existence of some real Hilbert realization carrying the exact HP
certificate. -/
theorem canonicalCompletedNativeStieltjesPositivity_iff_nonempty_carrier :
    CanonicalCompletedNativeStieltjesPositivity ↔
      Nonempty CompletedNativeRealHPCarrierRealization := by
  constructor
  · exact fun hpos => ⟨canonicalCompletedNativeStieltjesRealization hpos⟩
  · rintro ⟨realization⟩
    letI := realization.normedAddCommGroup
    letI := realization.innerProductSpace
    exact canonicalCompletedNativeStieltjesPositivity_of_certificate
      realization.certificate

/-! ## Canonical operator package from moment positivity -/

/-- Unshifted Hankel positivity selected from the Stieltjes gate. -/
theorem canonicalCompletedNativeStieltjes_hankelGram_posDef
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosDef :=
  (hpos N).1

/-- Shifted Hankel positivity selected from the Stieltjes gate. -/
theorem canonicalCompletedNativeStieltjes_shiftedHankel_posDef
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment N).PosDef :=
  (hpos N).2

/-- Exact canonical finite Jacobi tower selected purely by the moment gate. -/
def canonicalCompletedNativeStieltjesFiniteJacobiTower
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :=
  canonicalFiniteJacobiSection
    canonicalCompletedNativeLogDerivativeMoment N
    (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos N)

/-- The momentally selected finite Jacobi sections form an exact principal
tower. -/
theorem canonicalCompletedNativeStieltjesFiniteJacobiTower_isExactPrincipal :
    ∀ hpos : CanonicalCompletedNativeStieltjesPositivity,
      IsExactPrincipalTower
        (canonicalCompletedNativeStieltjesFiniteJacobiTower hpos) := by
  intro hpos
  exact canonicalFiniteJacobiSection_isExactPrincipalTower_unconditional
    canonicalCompletedNativeLogDerivativeMoment
    (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos)

/-- Entrywise projective limit matrix of the canonical moment Jacobi tower. -/
def canonicalCompletedNativeStieltjesJacobiTowerLimitMatrix
    (hpos : CanonicalCompletedNativeStieltjesPositivity) : Matrix ℕ ℕ ℝ :=
  canonicalJacobiTowerLimitMatrix
    canonicalCompletedNativeLogDerivativeMoment
    (canonicalCompletedNativeStieltjes_hankelGram_posDef hpos)

/-- Every finite section is the exact compression of the infinite Jacobi core
built from the canonical moment carrier. -/
theorem canonicalCompletedNativeStieltjes_finiteCompression_eq_finiteSection
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (N : ℕ) :
    let hrep := canonicalCompletedNativeStieltjesJet_momentKernel hpos
    let heven := canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos
    (fun i j : Fin N =>
      inner ℝ
        (greenJetJacobiCoreMap heven
          (canonicalGreenJetEvenJacobiCoreVector hrep heven N i))
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N j :
          greenJetEvenHilbertSubspace
            (canonicalCompletedNativeStieltjesJet hpos))) =
      canonicalCompletedNativeStieltjesFiniteJacobiTower hpos N := by
  dsimp only
  exact greenJetJacobiCore_finiteCompression_eq_canonicalFiniteJacobiSection
    (canonicalCompletedNativeStieltjesJet_momentKernel hpos)
    (canonicalCompletedNativeStieltjesJet_even_linearIndependent hpos) N

/-- Positive Jacobi operator instantiated solely by all-order moment
positivity. -/
def canonicalCompletedNativeStieltjesJacobiEnergyOperator
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.completedJacobiEnergyOperator

/-- Maximal self-adjoint package of the positive Jacobi operator. -/
def canonicalCompletedNativeStieltjesJacobiEnergySelfAdjointData
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.completedJacobiEnergySelfAdjointData

/-- Reduced signed-height maximal self-adjoint operator selected by the same
moment gate. -/
def canonicalCompletedNativeStieltjesReducedSignedHeightData
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.toReducedMaximalSelfAdjointHeightData

/-- Local complex graph-resolvent germ at the cyclic head. -/
def canonicalCompletedNativeStieltjesComplexGraphResolventGerm
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.completedJacobiComplexGraphResolvent_germ

/-- The cyclic readout of the canonical moment resolvent is locally exactly
the completed-native logarithmic derivative.  This is the native
characteristic-to-Jacobi seam; it does not use a Green carrier. -/
theorem canonicalCompletedNativeStieltjesResolventReadout_eventuallyEq_logDerivative
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    let germ :=
      canonicalCompletedNativeStieltjesComplexGraphResolventGerm hpos
    (fun z => germ.readout (germ.graphResolvent z)) =ᶠ[nhds 0]
      completedNativeLogDerivative := by
  dsimp only
  exact
    (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
      |>.completedJacobiComplexGraphResolvent_germ.eventually_readout_eq

/-- Global positive-Jacobi height-resolvent state, extended by zero on the
real axis exactly as in the existing analytic construction. -/
def canonicalCompletedNativeStieltjesGlobalResolventState
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.positiveJacobiHeightGlobalResolventState

/-- Scalar Weyl readout of the positive Jacobi resolvent selected by the
canonical moment gate. -/
def canonicalCompletedNativeStieltjesWeylReadout
    (hpos : CanonicalCompletedNativeStieltjesPositivity) : ℂ → ℂ :=
  (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
    |>.positiveJacobiHeightGluedBoundaryReadout

/-- Away from the real height axis and away from zeros of the characteristic,
the canonical Jacobi Weyl readout is exactly the native logarithmic
derivative divided by the forced square-coordinate factor `2 * z`.  The
proof uses the global division-free ODE, not Green scalarization. -/
theorem completedNativeOperatorLogDerivative_eq_two_mul_height_mul_stieltjesWeylReadout
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    {z : ℂ} (hzDomain : z ∈ completedNativeHeightDomain)
    (hzIm : z.im ≠ 0)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeOperatorLogDerivative z =
      ((2 : ℂ) * z) *
        canonicalCompletedNativeStieltjesWeylReadout hpos z := by
  let certificate :=
    completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos
  have hbounds :=
    CompletedNativeRealHPCarrierCertificate.mem_completedNativeHeightDomain_iff_im_bounds.mp
      hzDomain
  have hdefect : certificate.positiveJacobiWeylODEDefect z = 0 := by
    rcases lt_or_gt_of_ne hzIm with hzNeg | hzPos
    · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_lower
        (Or.inr ⟨hbounds.1, hzNeg⟩)
    · exact certificate.positiveJacobiWeylODEDefect_eq_zero_on_upper
        (Or.inr ⟨hzPos, hbounds.2⟩)
  unfold completedNativeOperatorLogDerivative
  apply (div_eq_iff hF).2
  unfold canonicalCompletedNativeStieltjesWeylReadout
  change
    -deriv completedNativeOperatorCharacteristic z =
      ((2 : ℂ) * z) *
        certificate.positiveJacobiHeightGluedBoundaryReadout z *
          completedNativeOperatorCharacteristic z
  unfold CompletedNativeRealHPCarrierCertificate.positiveJacobiWeylODEDefect at hdefect
  linear_combination -hdefect

/-- All-order Stieltjes positivity is sufficient for completed-native
confinement.  This theorem deliberately does not assert the positivity gate. -/
theorem completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  exact
    (completedNativeRealHPCarrierCertificate_of_stieltjesPositivity hpos)
      |>.completedNativeOperator_zero_im_eq_zero_of_positiveJacobiResolvent
        hzDomain hzero

end

end CarrySelfAdjointOperator
