import CarrySelfAdjointOperator.CompletedGreenJetSignedHeightIntertwiner
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic

/-!
# Hilbert realization of the completed Green-jet/signed-height tower

The exact cutoff system already supplies a complete metric carrier.  This
module identifies the linear Hilbert geometry behind that metric construction.
The ambient object is not added by hand: it is the closed real span of the
Green jets themselves.

At every order `N`, the rows of the canonical finite whitening are used as
coefficients of the raw Green-jet prefix.  The Green Gram identity together
with exact whitening proves that the resulting signed-height vectors are an
orthonormal family.  Hence finite signed-coordinate space embeds linearly and
isometrically in the closed Green span.
-/

open scoped InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-- The canonical Hilbert carrier supplied by a complete ambient Green-jet
realization: the closed real span of all even and odd jets. -/
abbrev CanonicalGreenJetSignedHeightHilbertSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) : Type _ :=
  (Submodule.span ℝ (Set.range jet)).topologicalClosure

/-- When the ambient jet realization is complete, the canonical closed span
is a complete real inner-product space. -/
theorem canonicalGreenJetSignedHeightHilbertSpace_completeSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (jet : (ℕ ⊕ ℕ) → E) :
    CompleteSpace (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  inferInstance

/-- Canonical embedding of an arbitrary Green-jet realization into the
completion of its ambient inner-product space. -/
def completedGreenJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    (ℕ ⊕ ℕ) → UniformSpace.Completion E :=
  fun k => (jet k : UniformSpace.Completion E)

/-- Fully canonical Hilbert promotion, available even when the original
ambient inner-product space was not assumed complete. -/
abbrev CanonicalCompletedGreenJetSignedHeightHilbertSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) : Type _ :=
  CanonicalGreenJetSignedHeightHilbertSpace (completedGreenJet jet)

/-- The automatically promoted carrier is complete. -/
theorem canonicalCompletedGreenJetSignedHeightHilbertSpace_completeSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CompleteSpace
      (CanonicalCompletedGreenJetSignedHeightHilbertSpace jet) :=
  inferInstance

/-- Completion preserves the exact Green Gram representation. -/
theorem completedGreenJet_gramRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    IsGreenWronskianMomentKernelGramRepresentation moments
      (completedGreenJet jet) := by
  intro i j
  simpa [completedGreenJet, Matrix.gram] using hrep i j

/-- Completion preserves global independence of the even Green jets. -/
theorem completedGreenJet_even_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n))) :
    LinearIndependent ℝ
      (fun n : ℕ => completedGreenJet jet (Sum.inl n)) := by
  have h := heven.map'
    (UniformSpace.Completion.toComplₗᵢ :
      E →ₗᵢ[ℝ] UniformSpace.Completion E).toLinearMap
    (LinearMap.ker_eq_bot.mpr
      (UniformSpace.Completion.toComplₗᵢ :
        E →ₗᵢ[ℝ] UniformSpace.Completion E).injective)
  simpa [completedGreenJet, Function.comp_def] using h

/-- Completion preserves global independence of the odd Green jets. -/
theorem completedGreenJet_odd_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    LinearIndependent ℝ
      (fun n : ℕ => completedGreenJet jet (Sum.inr n)) := by
  have h := hodd.map'
    (UniformSpace.Completion.toComplₗᵢ :
      E →ₗᵢ[ℝ] UniformSpace.Completion E).toLinearMap
    (LinearMap.ker_eq_bot.mpr
      (UniformSpace.Completion.toComplₗᵢ :
        E →ₗᵢ[ℝ] UniformSpace.Completion E).injective)
  simpa [completedGreenJet, Function.comp_def] using h

/-- An original Green jet, bundled in the canonical closed span. -/
def greenJetInHilbert
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (k : ℕ ⊕ ℕ) :
    CanonicalGreenJetSignedHeightHilbertSpace jet :=
  ⟨jet k, (Submodule.span ℝ (Set.range jet)).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self k))⟩

/-- Isometric inclusion of the algebraic Green span into its closed span. -/
def greenJetSpanToHilbert
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule.span ℝ (Set.range jet) →ₗᵢ[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet where
  toFun x := ⟨x, (Submodule.span ℝ (Set.range jet)).le_topologicalClosure x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The algebraic Green span is dense in the canonical Hilbert carrier. -/
theorem greenJetSpanToHilbert_denseRange
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    DenseRange (greenJetSpanToHilbert jet) := by
  let S := Submodule.span ℝ (Set.range jet)
  change DenseRange (Set.inclusion S.le_topologicalClosure)
  apply (denseRange_inclusion_iff S.le_topologicalClosure).2
  intro x hx
  exact hx

/-- The original jets, bundled in their algebraic span, still span that
entire algebraic carrier. -/
theorem greenJetInSpan_span_eq_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule.span ℝ
        (Set.range (fun k =>
          (⟨jet k, Submodule.subset_span (Set.mem_range_self k)⟩ :
            Submodule.span ℝ (Set.range jet)))) = ⊤ := by
  let S := Submodule.span ℝ (Set.range jet)
  let w : (ℕ ⊕ ℕ) → S := fun k =>
    ⟨jet k, Submodule.subset_span (Set.mem_range_self k)⟩
  change Submodule.span ℝ (Set.range w) = ⊤
  apply (Submodule.map_injective_of_injective S.injective_subtype)
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have himage : S.subtype '' Set.range w = Set.range jet := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨w k, ⟨k, rfl⟩, rfl⟩
  rw [himage]

/-- The order-`N` raw parity-jet prefix. -/
def greenJetPrefix
    {E : Type*} (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    (Fin N ⊕ Fin N) → E
  | Sum.inl i => jet (Sum.inl (i : ℕ))
  | Sum.inr i => jet (Sum.inr (i : ℕ))

/-- Row-wise synthesis of a vector family by a real matrix. -/
def matrixRowSynthesis
    {I J E : Type*} [Fintype J] [AddCommMonoid E] [Module ℝ E]
    (A : Matrix I J ℝ) (v : J → E) : I → E :=
  fun i => ∑ j, A i j • v j

/-- Row synthesis converts matrix multiplication into composition of
syntheses. -/
theorem matrixRowSynthesis_mul
    {I J K E : Type*} [Fintype J] [Fintype K]
    [AddCommMonoid E] [Module ℝ E]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) (v : K → E) :
    matrixRowSynthesis (A * B) v =
      matrixRowSynthesis A (matrixRowSynthesis B v) := by
  classical
  funext i
  simp only [matrixRowSynthesis, Matrix.mul_apply]
  calc
    (∑ k, (∑ j, A i j * B j k) • v k) =
        ∑ k, ∑ j, (A i j * B j k) • v k := by
          simp only [Finset.sum_smul]
    _ = ∑ j, ∑ k, (A i j * B j k) • v k := Finset.sum_comm
    _ = ∑ j, A i j • ∑ k, B j k • v k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_smul]

/-- The identity matrix synthesizes the original family. -/
@[simp]
theorem matrixRowSynthesis_one
    {I E : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid E] [Module ℝ E]
    (v : I → E) :
    matrixRowSynthesis (1 : Matrix I I ℝ) v = v := by
  classical
  funext i
  simp [matrixRowSynthesis, Matrix.one_apply]

/-- Coordinate restriction synthesizes the corresponding subfamily. -/
theorem matrixRowSynthesis_coordinateRestriction
    {I J E : Type*} [Fintype J] [DecidableEq J]
    [AddCommMonoid E] [Module ℝ E]
    (e : I → J) (v : J → E) :
    matrixRowSynthesis (coordinateRestriction e) v = v ∘ e := by
  funext i
  simp [matrixRowSynthesis, coordinateRestriction]

/-- Transpose matrix action on coefficients is adjoint to row synthesis. -/
theorem transpose_mulVec_synthesis
    {I J E : Type*} [Fintype I] [Fintype J]
    [AddCommMonoid E] [Module ℝ E]
    (A : Matrix I J ℝ) (x : I → ℝ) (v : J → E) :
    (∑ j, (Aᵀ *ᵥ x) j • v j) =
      ∑ i, x i • matrixRowSynthesis A v i := by
  classical
  simp only [matrixRowSynthesis, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  calc
    (∑ j, (∑ i, A i j * x i) • v j) =
        ∑ j, ∑ i, (A i j * x i) • v j := by
          simp only [Finset.sum_smul]
    _ = ∑ i, ∑ j, (A i j * x i) • v j := Finset.sum_comm
    _ = ∑ i, x i • ∑ j, A i j • v j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      ring

/-- The small raw jet prefix is exactly the row synthesis obtained by
restricting the large prefix. -/
theorem greenJetPrefix_restrict
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) {N M : ℕ} (hNM : N ≤ M) :
    matrixRowSynthesis (coordinateRestriction (parityCutoffEmbedding hNM))
        (greenJetPrefix jet M) =
      greenJetPrefix jet N := by
  rw [matrixRowSynthesis_coordinateRestriction]
  funext i
  rcases i with i | i <;> rfl

/-- The Gram matrix of the raw parity prefix is exactly the finite Hankel
pair supplied by the Green coefficient identity. -/
theorem greenJetPrefix_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    Matrix.gram ℝ (greenJetPrefix jet N) =
      parityJetGram (hankelGram moments N) (shiftedHankel moments N) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [greenJetPrefix, parityJetGram, greenWronskianMomentKernel,
      Matrix.gram] using (hrep (Sum.inl (i : ℕ)) (Sum.inl (j : ℕ))).symm
  · simpa [greenJetPrefix, parityJetGram, greenWronskianMomentKernel,
      Matrix.gram] using (hrep (Sum.inl (i : ℕ)) (Sum.inr (j : ℕ))).symm
  · simpa [greenJetPrefix, parityJetGram, greenWronskianMomentKernel,
      Matrix.gram] using (hrep (Sum.inr (i : ℕ)) (Sum.inl (j : ℕ))).symm
  · simpa [greenJetPrefix, parityJetGram, greenWronskianMomentKernel,
      Matrix.gram] using (hrep (Sum.inr (i : ℕ)) (Sum.inr (j : ℕ))).symm

/-- A signed-height basis vector realized as the corresponding whitened
linear combination of raw Green jets. -/
def canonicalGreenJetSignedHeightVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (a : Fin N ⊕ Fin N) : E :=
  ∑ i, canonicalGreenJetSignedHeightSection hrep heven hodd N a i •
    greenJetPrefix jet N i

/-- Every finite signed-height vector lies in the algebraic span of the
original Green jets. -/
theorem canonicalGreenJetSignedHeightVector_mem_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (a : Fin N ⊕ Fin N) :
    canonicalGreenJetSignedHeightVector hrep heven hodd N a ∈
      Submodule.span ℝ (Set.range jet) := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rcases i with i | i
  · exact ⟨Sum.inl (i : ℕ), rfl⟩
  · exact ⟨Sum.inr (i : ℕ), rfl⟩

/-- Exact vector-level cutoff identity.  The signed vectors at order `N`
are precisely the rows of the transported cutoff synthesized from the
order-`M` signed vectors. -/
theorem canonicalGreenJetSignedHeightVector_cutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    matrixRowSynthesis
        (canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM)
        (canonicalGreenJetSignedHeightVector hrep heven hodd M) =
      canonicalGreenJetSignedHeightVector hrep heven hodd N := by
  let AN := canonicalGreenJetSignedHeightSection hrep heven hodd N
  let AM := canonicalGreenJetSignedHeightSection hrep heven hodd M
  let PM := parityJetGram
    (hankelGram moments M) (shiftedHankel moments M)
  let R := coordinateRestriction (parityCutoffEmbedding hNM)
  let S := whiteningSynthesis PM AM
  let vN := greenJetPrefix jet N
  let vM := greenJetPrefix jet M
  have hwhiteM : AM * PM * AMᵀ = 1 :=
    canonicalGreenJetSignedHeightSection_whitens hrep heven hodd M
  have hSA : S * AM = 1 :=
    whiteningSynthesis_mul_whitening hwhiteM
  have hraw : matrixRowSynthesis R vM = vN := by
    simpa [R, vM, vN] using greenJetPrefix_restrict jet hNM
  change matrixRowSynthesis (AN * R * S)
      (matrixRowSynthesis AM vM) = matrixRowSynthesis AN vN
  calc
    matrixRowSynthesis (AN * R * S) (matrixRowSynthesis AM vM) =
        matrixRowSynthesis ((AN * R * S) * AM) vM := by
          exact (matrixRowSynthesis_mul (AN * R * S) AM vM).symm
    _ = matrixRowSynthesis (AN * R * (S * AM)) vM := by
      rw [Matrix.mul_assoc]
    _ = matrixRowSynthesis
        (AN * R * (1 : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℝ))
        vM := by rw [hSA]
    _ = matrixRowSynthesis (AN * R) vM := by rw [Matrix.mul_one]
    _ = matrixRowSynthesis AN (matrixRowSynthesis R vM) :=
      matrixRowSynthesis_mul AN R vM
    _ = matrixRowSynthesis AN vN := by rw [hraw]

/-- The canonical inverse synthesis reconstructs every raw finite Green jet
from the signed-height vectors at the same order. -/
theorem canonicalGreenJetSignedHeightVector_inverse_synthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    matrixRowSynthesis
        (whiteningSynthesis
          (parityJetGram (hankelGram moments N) (shiftedHankel moments N))
          (canonicalGreenJetSignedHeightSection hrep heven hodd N))
        (canonicalGreenJetSignedHeightVector hrep heven hodd N) =
      greenJetPrefix jet N := by
  let A := canonicalGreenJetSignedHeightSection hrep heven hodd N
  let P := parityJetGram (hankelGram moments N) (shiftedHankel moments N)
  let S := whiteningSynthesis P A
  let v := greenJetPrefix jet N
  have hwhite : A * P * Aᵀ = 1 :=
    canonicalGreenJetSignedHeightSection_whitens hrep heven hodd N
  have hSA : S * A = 1 := whiteningSynthesis_mul_whitening hwhite
  change matrixRowSynthesis S (matrixRowSynthesis A v) = v
  calc
    matrixRowSynthesis S (matrixRowSynthesis A v) =
        matrixRowSynthesis (S * A) v :=
      (matrixRowSynthesis_mul S A v).symm
    _ = matrixRowSynthesis 1 v := by rw [hSA]
    _ = v := matrixRowSynthesis_one v

/-- The signed-height vectors obtained from exact whitening are genuinely
orthonormal in the ambient Green-jet geometry. -/
theorem canonicalGreenJetSignedHeightVector_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    Orthonormal ℝ
      (canonicalGreenJetSignedHeightVector hrep heven hodd N) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  let A := canonicalGreenJetSignedHeightSection hrep heven hodd N
  let P := parityJetGram (hankelGram moments N) (shiftedHankel moments N)
  let v := greenJetPrefix jet N
  have hwhite : A * P * Aᵀ = 1 :=
    canonicalGreenJetSignedHeightSection_whitens hrep heven hodd N
  have hentry := congrFun (congrFun hwhite a) b
  have hgram : Matrix.gram ℝ v = P := greenJetPrefix_gram hrep N
  calc
    ⟪canonicalGreenJetSignedHeightVector hrep heven hodd N a,
        canonicalGreenJetSignedHeightVector hrep heven hodd N b⟫_ℝ =
        star (fun i => A a i) ⬝ᵥ
          (Matrix.gram ℝ v *ᵥ (fun i => A b i)) := by
            symm
            simpa [A, v, canonicalGreenJetSignedHeightVector] using
              (Matrix.star_dotProduct_gram_mulVec
                (v := v) (x := fun i => A a i) (y := fun i => A b i))
    _ = (A * P * Aᵀ) a b := by
      rw [hgram]
      rw [star_trivial, Matrix.dotProduct_mulVec]
      rfl
    _ = (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) a b := hentry
    _ = if a = b then 1 else 0 := Matrix.one_apply

/-- The same vectors, now bundled in the closed Green span. -/
def canonicalGreenJetSignedHeightHilbertVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (a : Fin N ⊕ Fin N) :
    CanonicalGreenJetSignedHeightHilbertSpace jet :=
  ⟨canonicalGreenJetSignedHeightVector hrep heven hodd N a,
    (Submodule.span ℝ (Set.range jet)).le_topologicalClosure
      (canonicalGreenJetSignedHeightVector_mem_span
        hrep heven hodd N a)⟩

/-- The finite signed-height family remains orthonormal after bundling it in
the canonical closed Green span. -/
theorem canonicalGreenJetSignedHeightHilbertVector_orthonormal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    Orthonormal ℝ
      (canonicalGreenJetSignedHeightHilbertVector hrep heven hodd N) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  have h := (orthonormal_iff_ite.mp
    (canonicalGreenJetSignedHeightVector_orthonormal
      hrep heven hodd N)) a b
  simpa [canonicalGreenJetSignedHeightHilbertVector] using h

/-- Linear synthesis of an order-`N` signed coordinate vector inside the
canonical Green Hilbert space. -/
def canonicalGreenJetSignedHeightHilbertSynthesisLinearMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →ₗ[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet where
  toFun x := ∑ i, x i •
    canonicalGreenJetSignedHeightHilbertVector hrep heven hodd N i
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.smul_sum, smul_smul]

@[simp]
theorem canonicalGreenJetSignedHeightHilbertSynthesisLinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (x : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    canonicalGreenJetSignedHeightHilbertSynthesisLinearMap
        hrep heven hodd N x =
      ∑ i, x i •
        canonicalGreenJetSignedHeightHilbertVector hrep heven hodd N i :=
  rfl

/-- The finite synthesis is a linear isometry, not merely a distance
preserving map. -/
def canonicalGreenJetSignedHeightToHilbert
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →ₗᵢ[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet := by
  let f := canonicalGreenJetSignedHeightHilbertSynthesisLinearMap
    hrep heven hodd N
  have hq := canonicalGreenJetSignedHeightHilbertVector_orthonormal
    hrep heven hodd N
  apply f.isometryOfInner
  intro x y
  have h := hq.inner_sum (fun i => x i) (fun i => y i) Finset.univ
  simpa [f, canonicalGreenJetSignedHeightHilbertSynthesisLinearMap,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h

@[simp]
theorem canonicalGreenJetSignedHeightToHilbert_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (x : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    canonicalGreenJetSignedHeightToHilbert hrep heven hodd N x =
      ∑ i, x i •
        canonicalGreenJetSignedHeightHilbertVector hrep heven hodd N i :=
  rfl

/-- The Hilbert realizations are compatible with every exact cutoff
inclusion: passing to a larger order changes coordinates, not the vector. -/
theorem canonicalGreenJetSignedHeightToHilbert_commute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    canonicalGreenJetSignedHeightToHilbert hrep heven hodd M
        (canonicalGreenJetSignedHeightCutoffLinearIsometry
          hrep heven hodd hNM x) =
      canonicalGreenJetSignedHeightToHilbert hrep heven hodd N x := by
  rw [canonicalGreenJetSignedHeightToHilbert_apply,
    canonicalGreenJetSignedHeightToHilbert_apply]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    canonicalGreenJetSignedHeightHilbertVector]
  simp only [canonicalGreenJetSignedHeightCutoffLinearIsometry,
    LinearMap.coe_isometryOfInner, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply]
  change (∑ j,
      ((canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM)ᵀ *ᵥ
        (WithLp.ofLp x)) j •
          canonicalGreenJetSignedHeightVector hrep heven hodd M j) =
    ∑ i, x i • canonicalGreenJetSignedHeightVector hrep heven hodd N i
  rw [transpose_mulVec_synthesis]
  rw [canonicalGreenJetSignedHeightVector_cutoff
    hrep heven hodd hNM]

/-- The finite Hilbert ranges are nested along the canonical cutoff
inclusions. -/
theorem canonicalGreenJetSignedHeightToHilbert_range_mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    LinearMap.range
        (canonicalGreenJetSignedHeightToHilbert
          hrep heven hodd N).toLinearMap ≤
      LinearMap.range
        (canonicalGreenJetSignedHeightToHilbert
          hrep heven hodd M).toLinearMap := by
  rintro _ ⟨x, rfl⟩
  refine ⟨canonicalGreenJetSignedHeightCutoffLinearIsometry
    hrep heven hodd hNM x, ?_⟩
  exact canonicalGreenJetSignedHeightToHilbert_commute
    hrep heven hodd hNM x

/-- A raw finite prefix jet bundled in the canonical Hilbert carrier. -/
def greenJetPrefixInHilbert
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (N : ℕ) :
    (Fin N ⊕ Fin N) → CanonicalGreenJetSignedHeightHilbertSpace jet
  | Sum.inl i => greenJetInHilbert jet (Sum.inl (i : ℕ))
  | Sum.inr i => greenJetInHilbert jet (Sum.inr (i : ℕ))

/-- Every raw prefix jet belongs to the range of the finite signed-height
isometry at the same order. -/
theorem greenJetPrefixInHilbert_mem_range
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (i : Fin N ⊕ Fin N) :
    greenJetPrefixInHilbert jet N i ∈
      LinearMap.range
        (canonicalGreenJetSignedHeightToHilbert
          hrep heven hodd N).toLinearMap := by
  let A := canonicalGreenJetSignedHeightSection hrep heven hodd N
  let P := parityJetGram (hankelGram moments N) (shiftedHankel moments N)
  let S := whiteningSynthesis P A
  let x : EuclideanSpace ℝ (Fin N ⊕ Fin N) :=
    WithLp.toLp 2 (fun j => S i j)
  refine ⟨x, ?_⟩
  change canonicalGreenJetSignedHeightToHilbert
    hrep heven hodd N x = greenJetPrefixInHilbert jet N i
  rw [canonicalGreenJetSignedHeightToHilbert_apply]
  apply Subtype.ext
  have hi := congrFun
    (canonicalGreenJetSignedHeightVector_inverse_synthesis
      hrep heven hodd N) i
  rcases i with i | i
  · simpa [x, S, A, P, matrixRowSynthesis,
      canonicalGreenJetSignedHeightHilbertVector,
      greenJetPrefixInHilbert, greenJetInHilbert,
      greenJetPrefix] using hi
  · simpa [x, S, A, P, matrixRowSynthesis,
      canonicalGreenJetSignedHeightHilbertVector,
      greenJetPrefixInHilbert, greenJetInHilbert,
      greenJetPrefix] using hi

/-- The subspace generated by all finite signed-height realizations. -/
def canonicalFiniteSignedHeightHilbertSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    Submodule ℝ (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  ⨆ N, LinearMap.range
    (canonicalGreenJetSignedHeightToHilbert hrep heven hodd N).toLinearMap

/-- Every original Green jet appears in one finite signed-height range. -/
theorem greenJetInHilbert_mem_finiteSignedHeightSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (k : ℕ ⊕ ℕ) :
    greenJetInHilbert jet k ∈
      canonicalFiniteSignedHeightHilbertSubspace hrep heven hodd := by
  rcases k with n | n
  · apply Submodule.mem_iSup_of_mem (n + 1)
    simpa [greenJetPrefixInHilbert] using
      (greenJetPrefixInHilbert_mem_range hrep heven hodd (n + 1)
        (Sum.inl ⟨n, Nat.lt_succ_self n⟩))
  · apply Submodule.mem_iSup_of_mem (n + 1)
    simpa [greenJetPrefixInHilbert] using
      (greenJetPrefixInHilbert_mem_range hrep heven hodd (n + 1)
        (Sum.inr ⟨n, Nat.lt_succ_self n⟩))

/-- The finite signed-height subspace is dense in the full closed Green
span.  Thus the Hilbert carrier is exactly the completion of the compatible
finite tower, rather than an ambient enlargement with unused directions. -/
theorem canonicalFiniteSignedHeightHilbertSubspace_topologicalClosure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    (canonicalFiniteSignedHeightHilbertSubspace
      hrep heven hodd).topologicalClosure = ⊤ := by
  let S := Submodule.span ℝ (Set.range jet)
  let w : (ℕ ⊕ ℕ) → S := fun k =>
    ⟨jet k, Submodule.subset_span (Set.mem_range_self k)⟩
  let f := greenJetSpanToHilbert jet
  let Q := canonicalFiniteSignedHeightHilbertSubspace hrep heven hodd
  have hwspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    simpa [S, w] using greenJetInSpan_span_eq_top jet
  have hw : ∀ k, f (w k) ∈ Q := by
    intro k
    simpa [f, w, Q, greenJetSpanToHilbert, greenJetInHilbert] using
      greenJetInHilbert_mem_finiteSignedHeightSubspace
        hrep heven hodd k
  have hrange_le : LinearMap.range f.toLinearMap ≤ Q := by
    rintro y ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℝ (Set.range w) := by
      rw [hwspan]
      exact Submodule.mem_top
    have hspan : Submodule.span ℝ (Set.range w) ≤
        Q.comap f.toLinearMap := by
      apply Submodule.span_le.2
      rintro _ ⟨k, rfl⟩
      exact hw k
    exact hspan hx
  have hDenseRange : DenseRange f :=
    greenJetSpanToHilbert_denseRange jet
  have hrangeDense : Dense (LinearMap.range f.toLinearMap :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)) := by
    change Dense (Set.range fun x => f x)
    exact hDenseRange
  have hrangeClosure :
      (LinearMap.range f.toLinearMap).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hrangeDense
  apply top_unique
  rw [← hrangeClosure]
  exact Submodule.topologicalClosure_mono hrange_le

end

end CarrySelfAdjointOperator
