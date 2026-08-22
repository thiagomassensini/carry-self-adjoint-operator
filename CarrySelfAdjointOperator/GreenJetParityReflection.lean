import CarrySelfAdjointOperator.GreenJetSignedHeightHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# The global Green-jet parity reflection

The completed Green-jet Hilbert space has two intrinsic sectors.  The even
sector is the closed span of the even jets and the odd sector is the closed
span of the odd jets.  The Green coefficient identity makes the two sectors
orthogonal.  Since all Green jets generate the ambient Hilbert carrier, the
two closed sectors exhaust it.

Reflection in the even sector is therefore the canonical bounded extension
of the finite signed-height reflection.  It is a self-adjoint unitary
involution and, at every cutoff, its action is exactly the matrix
`signedSectorReflection` in signed coordinates.
-/

open scoped InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-- The algebraic even Green-jet sector in the canonical Hilbert carrier. -/
def greenJetEvenAlgebraicSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  Submodule.span ℝ
    (Set.range (fun n : ℕ => greenJetInHilbert jet (Sum.inl n)))

/-- The algebraic odd Green-jet sector in the canonical Hilbert carrier. -/
def greenJetOddAlgebraicSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  Submodule.span ℝ
    (Set.range (fun n : ℕ => greenJetInHilbert jet (Sum.inr n)))

/-- The closed even sector. -/
def greenJetEvenHilbertSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  (greenJetEvenAlgebraicSubspace jet).topologicalClosure

/-- The closed odd sector. -/
def greenJetOddHilbertSubspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    Submodule ℝ (CanonicalGreenJetSignedHeightHilbertSpace jet) :=
  (greenJetOddAlgebraicSubspace jet).topologicalClosure

theorem greenJetEvenHilbertSubspace_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    IsClosed (greenJetEvenHilbertSubspace jet :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)) :=
  (greenJetEvenAlgebraicSubspace jet).isClosed_topologicalClosure

theorem greenJetOddHilbertSubspace_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    IsClosed (greenJetOddHilbertSubspace jet :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)) :=
  (greenJetOddAlgebraicSubspace jet).isClosed_topologicalClosure

/-- Every even raw jet lies in the closed even sector. -/
theorem greenJetInHilbert_even_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    greenJetInHilbert jet (Sum.inl n) ∈
      greenJetEvenHilbertSubspace jet :=
  (greenJetEvenAlgebraicSubspace jet).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self n))

/-- Every odd raw jet lies in the closed odd sector. -/
theorem greenJetInHilbert_odd_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    greenJetInHilbert jet (Sum.inr n) ∈
      greenJetOddHilbertSubspace jet :=
  (greenJetOddAlgebraicSubspace jet).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self n))

/-- The coefficient-level Green identity is exactly orthogonality of an even
and an odd bundled jet. -/
theorem greenJetInHilbert_even_odd_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    ⟪greenJetInHilbert jet (Sum.inl i),
      greenJetInHilbert jet (Sum.inr j)⟫_ℝ = 0 := by
  have h := greenWronskianMomentKernel_even_odd_orthogonal hrep i j
  simpa [Matrix.gram, greenJetInHilbert] using h

/-- The algebraic even and odd Green sectors are orthogonal. -/
theorem greenJetAlgebraicSubspaces_isOrtho
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    greenJetEvenAlgebraicSubspace jet ⟂
      greenJetOddAlgebraicSubspace jet := by
  rw [greenJetEvenAlgebraicSubspace, greenJetOddAlgebraicSubspace,
    Submodule.isOrtho_span]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact greenJetInHilbert_even_odd_inner_eq_zero hrep i j

/-- Orthogonality survives completion of both parity sectors. -/
theorem greenJetHilbertSubspaces_isOrtho
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    greenJetEvenHilbertSubspace jet ⟂
      greenJetOddHilbertSubspace jet := by
  rw [Submodule.isOrtho_iff_le]
  change (greenJetEvenAlgebraicSubspace jet).topologicalClosure ≤
    (greenJetOddAlgebraicSubspace jet).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact (greenJetEvenAlgebraicSubspace jet).topologicalClosure_minimal
    (greenJetAlgebraicSubspaces_isOrtho hrep)
    (greenJetOddAlgebraicSubspace jet).isClosed_orthogonal

/-- The bundled raw Green jets have dense algebraic span in the canonical
Hilbert carrier. -/
theorem greenJetInHilbert_span_topologicalClosure_eq_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    (Submodule.span ℝ (Set.range (greenJetInHilbert jet))).topologicalClosure =
      ⊤ := by
  let S := Submodule.span ℝ (Set.range jet)
  let w : (ℕ ⊕ ℕ) → S := fun k =>
    ⟨jet k, Submodule.subset_span (Set.mem_range_self k)⟩
  let f := greenJetSpanToHilbert jet
  let Q := Submodule.span ℝ (Set.range (greenJetInHilbert jet))
  have hwspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    simpa [S, w] using greenJetInSpan_span_eq_top jet
  have hw : ∀ k, f (w k) ∈ Q := by
    intro k
    apply Submodule.subset_span
    exact ⟨k, by
      rfl⟩
  have hrange_le : LinearMap.range f.toLinearMap ≤ Q := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℝ (Set.range w) := by
      rw [hwspan]
      exact Submodule.mem_top
    have hspan : Submodule.span ℝ (Set.range w) ≤
        Q.comap f.toLinearMap := by
      apply Submodule.span_le.2
      rintro _ ⟨k, rfl⟩
      exact hw k
    exact hspan hx
  have hrangeDense : Dense (LinearMap.range f.toLinearMap :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)) := by
    change Dense (Set.range fun x => f x)
    exact greenJetSpanToHilbert_denseRange jet
  have hrangeClosure :
      (LinearMap.range f.toLinearMap).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hrangeDense
  apply top_unique
  rw [← hrangeClosure]
  exact Submodule.topologicalClosure_mono hrange_le

/-- The closed odd Green sector is exactly the orthogonal complement of the
closed even Green sector.  Thus completion adds no unused parity direction. -/
theorem greenJetOddHilbertSubspace_eq_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    greenJetOddHilbertSubspace jet =
      (greenJetEvenHilbertSubspace jet)ᗮ := by
  let K := greenJetEvenHilbertSubspace jet
  let O := greenJetOddHilbertSubspace jet
  let P := Kᗮ.starProjection
  let Q := O.comap P.toLinearMap
  have hOK : O ≤ Kᗮ := by
    exact (greenJetHilbertSubspaces_isOrtho hrep).symm
  apply le_antisymm hOK
  have hQclosed : IsClosed (Q :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)) := by
    change IsClosed (P ⁻¹' (O :
      Set (CanonicalGreenJetSignedHeightHilbertSpace jet)))
    exact (greenJetOddHilbertSubspace_isClosed jet).preimage P.continuous
  have hrawQ : ∀ k, greenJetInHilbert jet k ∈ Q := by
    intro k
    rcases k with n | n
    · change P (greenJetInHilbert jet (Sum.inl n)) ∈ O
      have heven : greenJetInHilbert jet (Sum.inl n) ∈ K := by
        simpa [K] using greenJetInHilbert_even_mem jet n
      simp only [P, Submodule.starProjection_orthogonal_apply_eq_zero heven]
      exact O.zero_mem
    · change P (greenJetInHilbert jet (Sum.inr n)) ∈ O
      have hoddO : greenJetInHilbert jet (Sum.inr n) ∈ O := by
        simpa [O] using greenJetInHilbert_odd_mem jet n
      have hoddK : greenJetInHilbert jet (Sum.inr n) ∈ Kᗮ :=
        hOK hoddO
      simp only [P, Submodule.starProjection_eq_self_iff.mpr hoddK]
      exact hoddO
  have hspanQ :
      Submodule.span ℝ (Set.range (greenJetInHilbert jet)) ≤ Q := by
    apply Submodule.span_le.2
    rintro _ ⟨k, rfl⟩
    exact hrawQ k
  have htopQ :
      (⊤ : Submodule ℝ
        (CanonicalGreenJetSignedHeightHilbertSpace jet)) ≤ Q := by
    rw [← greenJetInHilbert_span_topologicalClosure_eq_top jet]
    exact (Submodule.span ℝ
      (Set.range (greenJetInHilbert jet))).topologicalClosure_minimal
        hspanQ hQclosed
  intro x hx
  have hxQ : x ∈ Q := htopQ Submodule.mem_top
  change P x ∈ O at hxQ
  simpa only [P, Submodule.starProjection_eq_self_iff.mpr hx] using hxQ

/-- The parity sectors form an exact orthogonal total decomposition of the
canonical Green-jet Hilbert space. -/
theorem greenJetParity_sup_eq_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    greenJetEvenHilbertSubspace jet ⊔
        greenJetOddHilbertSubspace jet = ⊤ := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  rw [greenJetOddHilbertSubspace_eq_orthogonal hrep]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- The canonical global parity reflection: `+1` on the closed even Green
sector and `-1` on its orthogonal complement. -/
def greenJetParityReflection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalGreenJetSignedHeightHilbertSpace jet ≃ₗᵢ[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  exact (greenJetEvenHilbertSubspace jet).reflection

/-- The same reflection as a bounded, everywhere-defined operator. -/
def greenJetParityReflectionCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalGreenJetSignedHeightHilbertSpace jet →L[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet :=
  (greenJetParityReflection jet).toContinuousLinearEquiv.toContinuousLinearMap

/-- Orthogonal projection onto the closed even Green sector. -/
def greenJetEvenProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalGreenJetSignedHeightHilbertSpace jet →L[ℝ]
      CanonicalGreenJetSignedHeightHilbertSpace jet := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  exact (greenJetEvenHilbertSubspace jet).starProjection

/-- Reflection is given by the exact projection formula `2 P_even - I`. -/
theorem greenJetParityReflection_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E)
    (x : CanonicalGreenJetSignedHeightHilbertSpace jet) :
    greenJetParityReflection jet x =
      2 • greenJetEvenProjection jet x - x := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  change (greenJetEvenHilbertSubspace jet).reflection x =
    2 • (greenJetEvenHilbertSubspace jet).starProjection x - x
  exact Submodule.reflection_apply x

/-- The global reflection fixes the entire closed even sector. -/
theorem greenJetParityReflection_eq_self_of_mem_even
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {jet : (ℕ ⊕ ℕ) → E}
    {x : CanonicalGreenJetSignedHeightHilbertSpace jet}
    (hx : x ∈ greenJetEvenHilbertSubspace jet) :
    greenJetParityReflection jet x = x := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  exact Submodule.reflection_mem_subspace_eq_self hx

/-- The global reflection negates the entire closed odd sector. -/
theorem greenJetParityReflection_eq_neg_of_mem_odd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    {x : CanonicalGreenJetSignedHeightHilbertSpace jet}
    (hx : x ∈ greenJetOddHilbertSubspace jet) :
    greenJetParityReflection jet x = -x := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  apply Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
  rw [← greenJetOddHilbertSubspace_eq_orthogonal hrep]
  exact hx

/-- On the raw generators, the global reflection is exactly parity. -/
@[simp]
theorem greenJetParityReflection_even
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) (n : ℕ) :
    greenJetParityReflection jet (greenJetInHilbert jet (Sum.inl n)) =
      greenJetInHilbert jet (Sum.inl n) :=
  greenJetParityReflection_eq_self_of_mem_even
    (greenJetInHilbert_even_mem jet n)

/-- On the raw odd generators, the global reflection is minus parity. -/
@[simp]
theorem greenJetParityReflection_odd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (n : ℕ) :
    greenJetParityReflection jet (greenJetInHilbert jet (Sum.inr n)) =
      -greenJetInHilbert jet (Sum.inr n) :=
  greenJetParityReflection_eq_neg_of_mem_odd hrep
    (greenJetInHilbert_odd_mem jet n)

/-- Reflection is an involution on the completed Hilbert space. -/
@[simp]
theorem greenJetParityReflection_involutive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E)
    (x : CanonicalGreenJetSignedHeightHilbertSpace jet) :
    greenJetParityReflection jet (greenJetParityReflection jet x) = x := by
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  exact Submodule.reflection_reflection _ x

/-- Reflection preserves the Hilbert inner product. -/
theorem greenJetParityReflection_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E)
    (x y : CanonicalGreenJetSignedHeightHilbertSpace jet) :
    ⟪greenJetParityReflection jet x,
        greenJetParityReflection jet y⟫_ℝ = ⟪x, y⟫_ℝ :=
  (greenJetParityReflection jet).inner_map_map x y

/-- In particular, the reflection preserves norm exactly. -/
@[simp]
theorem greenJetParityReflection_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E)
    (x : CanonicalGreenJetSignedHeightHilbertSpace jet) :
    ‖greenJetParityReflection jet x‖ = ‖x‖ :=
  (greenJetParityReflection jet).norm_map x

/-- The bounded reflection is symmetric. -/
theorem greenJetParityReflection_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) :
    (greenJetParityReflectionCLM jet :
      CanonicalGreenJetSignedHeightHilbertSpace jet →ₗ[ℝ]
        CanonicalGreenJetSignedHeightHilbertSpace jet).IsSymmetric := by
  intro x y
  change ⟪greenJetParityReflection jet x, y⟫_ℝ =
    ⟪x, greenJetParityReflection jet y⟫_ℝ
  calc
    ⟪greenJetParityReflection jet x, y⟫_ℝ =
        ⟪greenJetParityReflection jet x,
          greenJetParityReflection jet
            (greenJetParityReflection jet y)⟫_ℝ := by
          rw [greenJetParityReflection_involutive]
    _ = ⟪x, greenJetParityReflection jet y⟫_ℝ :=
      (greenJetParityReflection jet).inner_map_map x
        (greenJetParityReflection jet y)

/-- The global bounded parity operator is self-adjoint. -/
theorem greenJetParityReflection_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (jet : (ℕ ⊕ ℕ) → E) :
    IsSelfAdjoint (greenJetParityReflectionCLM jet) :=
  (greenJetParityReflection_isSymmetric jet).isSelfAdjoint

/-- On every raw finite prefix, the global reflection is the diagonal Green
parity grading. -/
theorem greenJetParityReflection_prefix_eq_grading
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    (fun i => greenJetParityReflection jet
      (greenJetPrefixInHilbert jet N i)) =
        matrixRowSynthesis signedSectorGrading
          (greenJetPrefixInHilbert jet N) := by
  classical
  funext i
  rcases i with i | i
  · change greenJetParityReflection jet
      (greenJetInHilbert jet (Sum.inl (i : ℕ))) = _
    rw [greenJetParityReflection_even]
    simp [greenJetPrefixInHilbert, matrixRowSynthesis,
      signedSectorGrading, Matrix.one_apply]
  · change greenJetParityReflection jet
      (greenJetInHilbert jet (Sum.inr (i : ℕ))) = _
    rw [greenJetParityReflection_odd hrep]
    simp [greenJetPrefixInHilbert, matrixRowSynthesis,
      signedSectorGrading, Matrix.one_apply]

/-- The bundled finite signed-height vector is row synthesis of the bundled
raw Green prefix by the canonical section. -/
theorem canonicalGreenJetSignedHeightHilbertVector_eq_rowSynthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (a : Fin N ⊕ Fin N) :
    canonicalGreenJetSignedHeightHilbertVector hrep heven hodd N a =
      matrixRowSynthesis
        (canonicalGreenJetSignedHeightSection hrep heven hodd N)
        (greenJetPrefixInHilbert jet N) a := by
  apply Subtype.ext
  simp only [canonicalGreenJetSignedHeightHilbertVector,
    canonicalGreenJetSignedHeightVector, matrixRowSynthesis,
    Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i _
  rcases i with i | i <;> rfl

/-- At every order, the global Hilbert reflection acts on each canonical
signed-height vector by the finite sector-swap matrix. -/
theorem greenJetParityReflection_signedHeightVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (a : Fin N ⊕ Fin N) :
    greenJetParityReflection jet
        (canonicalGreenJetSignedHeightHilbertVector
          hrep heven hodd N a) =
      matrixRowSynthesis signedSectorReflection
        (canonicalGreenJetSignedHeightHilbertVector
          hrep heven hodd N) a := by
  classical
  let A := canonicalGreenJetSignedHeightSection hrep heven hodd N
  let G := signedSectorGrading (ι := Fin N)
  let S := signedSectorReflection (ι := Fin N)
  let v := greenJetPrefixInHilbert jet N
  let q := canonicalGreenJetSignedHeightHilbertVector
    hrep heven hodd N
  have hq : q = matrixRowSynthesis A v := by
    funext b
    exact canonicalGreenJetSignedHeightHilbertVector_eq_rowSynthesis
      hrep heven hodd N b
  have hv : (fun i => greenJetParityReflection jet (v i)) =
      matrixRowSynthesis G v := by
    simpa [G, v] using greenJetParityReflection_prefix_eq_grading hrep N
  have hAG : A * G = S * A := by
    simpa [A, G, S] using
      canonicalGreenJetSignedHeightSection_intertwines
        hrep heven hodd N
  change greenJetParityReflection jet (q a) =
    matrixRowSynthesis S q a
  rw [hq]
  calc
    greenJetParityReflection jet (matrixRowSynthesis A v a) =
        matrixRowSynthesis A
          (fun i => greenJetParityReflection jet (v i)) a := by
      simp [matrixRowSynthesis]
    _ = matrixRowSynthesis A (matrixRowSynthesis G v) a := by rw [hv]
    _ = matrixRowSynthesis (A * G) v a := by
      rw [matrixRowSynthesis_mul]
    _ = matrixRowSynthesis (S * A) v a := by rw [hAG]
    _ = matrixRowSynthesis S (matrixRowSynthesis A v) a :=
      congrFun (matrixRowSynthesis_mul S A v) a

/-- Exact finite/global intertwining law.  The restriction of the global
self-adjoint reflection to every canonical order-`N` signed realization is
precisely `signedSectorReflection`; no limiting error is present. -/
theorem greenJetParityReflection_intertwines_finite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) (x : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    greenJetParityReflection jet
        (canonicalGreenJetSignedHeightToHilbert
          hrep heven hodd N x) =
      canonicalGreenJetSignedHeightToHilbert hrep heven hodd N
        (Matrix.toEuclideanLin signedSectorReflection x) := by
  classical
  let S := signedSectorReflection (ι := Fin N)
  let q := canonicalGreenJetSignedHeightHilbertVector
    hrep heven hodd N
  have hcoeff :
      WithLp.ofLp (Matrix.toEuclideanLin S x) =
        S *ᵥ (WithLp.ofLp x) := by
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [canonicalGreenJetSignedHeightToHilbert_apply,
    canonicalGreenJetSignedHeightToHilbert_apply]
  change greenJetParityReflection jet
      (∑ i, (WithLp.ofLp x) i • q i) =
    ∑ j, (WithLp.ofLp (Matrix.toEuclideanLin S x)) j • q j
  rw [hcoeff]
  calc
    greenJetParityReflection jet
        (∑ i, (WithLp.ofLp x) i • q i) =
      ∑ i, (WithLp.ofLp x) i •
        greenJetParityReflection jet (q i) := by simp
    _ = ∑ i, (WithLp.ofLp x) i • matrixRowSynthesis S q i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [greenJetParityReflection_signedHeightVector
        hrep heven hodd N i]
    _ = ∑ j, (Sᵀ *ᵥ (WithLp.ofLp x)) j • q j := by
      symm
      exact transpose_mulVec_synthesis S (WithLp.ofLp x) q
    _ = ∑ j, (S *ᵥ (WithLp.ofLp x)) j • q j := by
      rw [signedSectorReflection_isSymm.eq]

/-- Every finite signed-height range is invariant under the global
reflection. -/
theorem greenJetParityReflection_mem_finite_range
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ)
    {y : CanonicalGreenJetSignedHeightHilbertSpace jet}
    (hy : y ∈ LinearMap.range
      (canonicalGreenJetSignedHeightToHilbert
        hrep heven hodd N).toLinearMap) :
    greenJetParityReflection jet y ∈ LinearMap.range
      (canonicalGreenJetSignedHeightToHilbert
        hrep heven hodd N).toLinearMap := by
  rcases hy with ⟨x, rfl⟩
  refine ⟨Matrix.toEuclideanLin signedSectorReflection x, ?_⟩
  exact (greenJetParityReflection_intertwines_finite
    hrep heven hodd N x).symm

/-- The finite/global intertwining is independent of the chosen larger
cutoff.  Enlarging coordinates before applying reflection gives exactly the
same Hilbert vector as reflecting at the smaller order and then enlarging. -/
theorem greenJetParityReflection_cutoff_exact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M)
    (x : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    greenJetParityReflection jet
        (canonicalGreenJetSignedHeightToHilbert hrep heven hodd M
          (canonicalGreenJetSignedHeightCutoffLinearIsometry
            hrep heven hodd hNM x)) =
      canonicalGreenJetSignedHeightToHilbert hrep heven hodd M
        (canonicalGreenJetSignedHeightCutoffLinearIsometry
          hrep heven hodd hNM
          (Matrix.toEuclideanLin signedSectorReflection x)) := by
  rw [canonicalGreenJetSignedHeightToHilbert_commute
      hrep heven hodd hNM x,
    greenJetParityReflection_intertwines_finite
      hrep heven hodd N x,
    canonicalGreenJetSignedHeightToHilbert_commute
      hrep heven hodd hNM
      (Matrix.toEuclideanLin signedSectorReflection x)]

/-- Fully automatic Hilbert reflection: first complete an arbitrary ambient
Green realization and then reflect in its closed even sector. -/
def canonicalCompletedGreenJetParityReflection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalCompletedGreenJetSignedHeightHilbertSpace jet ≃ₗᵢ[ℝ]
      CanonicalCompletedGreenJetSignedHeightHilbertSpace jet :=
  greenJetParityReflection (completedGreenJet jet)

/-- The automatic completed reflection as a bounded operator. -/
def canonicalCompletedGreenJetParityReflectionCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    CanonicalCompletedGreenJetSignedHeightHilbertSpace jet →L[ℝ]
      CanonicalCompletedGreenJetSignedHeightHilbertSpace jet :=
  greenJetParityReflectionCLM (completedGreenJet jet)

/-- Self-adjointness requires no completeness assumption on the original
ambient realization; completion supplies it canonically. -/
theorem canonicalCompletedGreenJetParityReflection_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (jet : (ℕ ⊕ ℕ) → E) :
    IsSelfAdjoint (canonicalCompletedGreenJetParityReflectionCLM jet) :=
  greenJetParityReflection_isSelfAdjoint (completedGreenJet jet)

end

end CarrySelfAdjointOperator
