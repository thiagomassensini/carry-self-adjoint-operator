import CarrySelfAdjointOperator.GreenJetJacobiFiniteCompression
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenMomentGramBridge
import CarrySelfAdjointOperator.MomentGramPositivity
import Mathlib.Tactic

/-!
# Native TFVD--Green shifted-Hankel factorization

The geometric positive factor is defined before any moment matrix: finite
coefficient vectors are synthesized from the odd Green jets.  Its Gram is the
shifted Hankel matrix precisely when the already-isolated Green--Wronskian
Gram representation holds.  The module therefore records both the honest
conditional factorization and the exact defect when the concrete native Gram
bridge is not yet available.
-/

open scoped InnerProductSpace Matrix BigOperators RealInnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The finite odd Green-sector factor.  This is the geometric candidate for
`B_N`: it synthesizes a coefficient vector from the first `N` odd Green jets.
Its definition uses only the jet family and the Hilbert structure, never the
moment sequence or any Hankel/Cholesky data. -/
def greenJetOddPrefixSynthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    (Fin N → ℝ) →ₗ[ℝ] greenJetOddHilbertSubspace jet where
  toFun c := ∑ i : Fin N, c i • greenJetOddSectorJet jet (i : ℕ)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    rfl

/-- The basis Gram of the geometric odd-prefix synthesis.  This is the
finite `B_N^* B_N` object before it is compared with any scalar moments. -/
def greenJetOddPrefixGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.gram ℝ (fun i : Fin N => greenJetOddSectorJet jet (i : ℕ))

/-- The finite coordinate basis is sent to the corresponding odd Green jet.
This is the pointwise statement that makes the matrix above the coordinate
`B_N^* B_N` Gram. -/
theorem greenJetOddPrefixSynthesis_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) (i : Fin N) :
    greenJetOddPrefixSynthesis jet N (fun j => if j = i then 1 else 0) =
      greenJetOddSectorJet jet (i : ℕ) := by
  classical
  apply Subtype.ext
  simp [greenJetOddPrefixSynthesis]

/-- The matrix Gram of the actual finite synthesis map on coordinate basis
vectors is exactly `greenJetOddPrefixGram`. -/
theorem greenJetOddPrefixSynthesis_basisGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    Matrix.gram ℝ
        (fun i : Fin N =>
          greenJetOddPrefixSynthesis jet N (fun j => if j = i then 1 else 0)) =
      greenJetOddPrefixGram jet N := by
  ext i j
  change ⟪greenJetOddPrefixSynthesis jet N (fun k => if k = i then 1 else 0),
      greenJetOddPrefixSynthesis jet N (fun k => if k = j then 1 else 0)⟫_ℝ = _
  rw [greenJetOddPrefixSynthesis_basis, greenJetOddPrefixSynthesis_basis]
  rfl

/-- Polarized finite energy of the geometric factor, expressed in its basis
Gram. -/
theorem greenJetOddPrefixSynthesis_inner_eq_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) (c d : Fin N → ℝ) :
    ⟪greenJetOddPrefixSynthesis jet N c,
      greenJetOddPrefixSynthesis jet N d⟫_ℝ =
      ∑ i : Fin N, ∑ j : Fin N,
        c i * (greenJetOddPrefixGram jet N i j) * d j := by
  classical
  change ⟪(∑ i : Fin N, c i • greenJetOddSectorJet jet (i : ℕ)),
      (∑ j : Fin N, d j • greenJetOddSectorJet jet (j : ℕ))⟫_ℝ = _
  simp only [sum_inner, inner_sum, greenJetOddPrefixGram, Matrix.gram_apply]
  calc
    (∑ x : Fin N, ∑ i : Fin N, ⟪c i • greenJetOddSectorJet jet ↑i,
        d x • greenJetOddSectorJet jet ↑x⟫_ℝ) =
      ∑ x : Fin N, ∑ i : Fin N, c i * ⟪greenJetOddSectorJet jet ↑i,
        greenJetOddSectorJet jet ↑x⟫_ℝ * d x := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_smul_left
        (greenJetOddSectorJet jet (i : ℕ))
        (d x • greenJetOddSectorJet jet (x : ℕ)) (c i)]
      rw [real_inner_smul_right
        (greenJetOddSectorJet jet (i : ℕ))
        (greenJetOddSectorJet jet (x : ℕ)) (d x)]
      ring
    _ = ∑ i : Fin N, ∑ j : Fin N, c i * ⟪greenJetOddSectorJet jet ↑i,
        greenJetOddSectorJet jet ↑j⟫_ℝ * d j := by
      rw [Finset.sum_comm]

/-- Entrywise defect between the geometric odd-prefix Gram and the shifted
moment kernel. -/
def greenJetShiftedHankelFactorizationDefect
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) (N : ℕ)
    (i j : Fin N) : ℝ :=
  moments ((i : ℕ) + (j : ℕ) + 1) -
    (greenJetOddPrefixGram jet N) i j

/-- The factorization defect vanishes exactly when the geometric odd-prefix
Gram is the shifted Hankel matrix. -/
theorem greenJetOddPrefixGram_eq_shiftedHankel_iff_defect_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    greenJetOddPrefixGram jet N = shiftedHankel moments N ↔
      ∀ i j, greenJetShiftedHankelFactorizationDefect moments jet N i j = 0 := by
  constructor
  · intro h i j
    unfold greenJetShiftedHankelFactorizationDefect
    rw [h]
    simp [shiftedHankel]
  · intro h
    ext i j
    have hij := h i j
    unfold greenJetShiftedHankelFactorizationDefect at hij
    change (greenJetOddPrefixGram jet N) i j =
      moments ((i : ℕ) + (j : ℕ) + 1)
    exact (sub_eq_zero.mp hij).symm

/-- The Green--Wronskian representation supplies the shifted-Hankel
factorization of the geometric odd-prefix factor. -/
theorem greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    greenJetOddPrefixGram jet N = shiftedHankel moments N := by
  exact gram_greenJetOddSectorJet_prefix hrep N

/-- The exact geometric factorization statement at order `N`. -/
def IsGreenJetShiftedHankelFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) : Prop :=
  greenJetOddPrefixGram jet N = shiftedHankel moments N

/-- The Green representation proves the finite `K_N = B_N^* B_N` statement.
The displayed synthesis is defined independently of `K_N`; this theorem only
performs the later Gram comparison. -/
theorem greenJetShiftedHankelFactorization_of_greenRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    IsGreenJetShiftedHankelFactorization moments jet N := by
  exact greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation hrep N

/-- The quadratic form of the geometric `B_N` is the shifted Hankel
quadratic form once the Green--Wronskian Gram identity is supplied. -/
theorem greenJetOddPrefixSynthesis_norm_sq_eq_shiftedHankel_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) (c : Fin N → ℝ) :
    ‖greenJetOddPrefixSynthesis jet N c‖ ^ 2 =
      ∑ i : Fin N, ∑ j : Fin N,
        c i * moments ((i : ℕ) + (j : ℕ) + 1) * c j := by
  rw [← real_inner_self_eq_norm_sq]
  rw [greenJetOddPrefixSynthesis_inner_eq_gram]
  rw [greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation hrep N]
  rfl

/-- The geometric Gram is positive semidefinite without using moments. -/
theorem greenJetOddPrefixGram_posSemidef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    (greenJetOddPrefixGram jet N).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ _

/-- Any vanishing factorization defect is enough to transfer positivity; the
Gram representation is used only as one way to discharge this proposition. -/
theorem shiftedHankel_posSemidef_of_greenJetShiftedHankelFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (N : ℕ)
    (hfactor : IsGreenJetShiftedHankelFactorization moments jet N) :
    (shiftedHankel moments N).PosSemidef := by
  rw [← hfactor]
  exact greenJetOddPrefixGram_posSemidef jet N

/-- A factorization and finite odd-jet independence give strict positivity of
that shifted section. -/
theorem shiftedHankel_posDef_of_greenJetShiftedHankelFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (N : ℕ)
    (hfactor : IsGreenJetShiftedHankelFactorization moments jet N)
    (hli : LinearIndependent ℝ
      (fun i : Fin N => greenJetOddSectorJet jet (i : ℕ))) :
    (shiftedHankel moments N).PosDef := by
  rw [← hfactor]
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- Under the Green representation, positivity transfers to the native
shifted Hankel section. -/
theorem shiftedHankel_posSemidef_of_greenJetFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    (shiftedHankel moments N).PosSemidef := by
  exact shiftedHankel_posSemidef_of_greenJetShiftedHankelFactorization N
    (greenJetShiftedHankelFactorization_of_greenRepresentation hrep N)

/-- Strict positivity remains exactly the geometric linear-independence
condition on the odd Green jets. -/
theorem shiftedHankel_posDef_of_greenJetFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (hli : LinearIndependent ℝ
      (fun i : Fin N => greenJetOddSectorJet jet (i : ℕ))) :
    (shiftedHankel moments N).PosDef := by
  rw [← greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation hrep N]
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- The odd-prefix factor agrees on the canonical generators with the
already-defined all-order Green energy factor.  No moment matrix is used in
this generator-level identity. -/
theorem greenJetOddPrefixSynthesis_generator_eq_greenJetEnergyFactorCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) (i : Fin N) :
    greenJetOddPrefixSynthesis jet N (fun j => if j = i then 1 else 0) =
      greenJetEnergyFactorCore heven (greenJetEvenCoreJet jet (i : ℕ)) := by
  classical
  rw [greenJetEnergyFactorCore_jet]
  apply Subtype.ext
  simp [greenJetOddPrefixSynthesis, greenJetOddSectorJet]

/-- If a concrete completed Green jet is available through the existing
forward-difference kernel certificate, its odd prefix has the native shifted
Hankel Gram at every order.  This is the precise conditional completion
statement; it does not manufacture the missing native kernel certificate. -/
theorem canonicalCompletedNativeForwardDifferenceOddPrefixFactorization
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    [CompleteSpace Hxi]
    (state : ℂ → Hxi)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel
      (completedNativeC3ProductLedgerState state))
    (N : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    greenJetOddPrefixGram
        (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
          (completedNativeC3ProductLedgerState state) hkernel) N =
      shiftedHankel canonicalCompletedNativeLogDerivativeMoment N := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  exact greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation
    (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
      (completedNativeC3ProductLedgerState state) hkernel) N

end

end CarrySelfAdjointOperator
