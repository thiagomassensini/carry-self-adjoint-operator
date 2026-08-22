import CarrySelfAdjointOperator.GreenJetSignedHeightIntertwiner
import CarrySelfAdjointOperator.ExactProjectiveMatrixTower
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Exact cutoff system for the completed Green-jet/signed-height intertwiner

The finite Green-jet intertwiners do not have to be principal submatrices of
one another.  In particular, inverse square root does not in general commute
with principal compression.  The canonical compatibility law is instead
obtained by transporting the raw prefix inclusion through the exact finite
whitenings.

If `A_N P_N A_Nᵀ = I`, put `S_N = P_N A_Nᵀ`.  Square-matrix finiteness makes
`S_N` the two-sided inverse of `A_N`.  For a raw coordinate restriction
`R_NM`, define

`C_NM = A_N R_NM S_M`.

Then `C_NM C_NMᵀ = I`; hence `C_NMᵀ` is the isometric inclusion of the
order-`N` signed coordinates into order `M`.  Moreover these maps compose
exactly and intertwine the signed-sector reflections.  This is the precise
algebraic system whose metric/Hilbert completion carries the all-order
intertwiner.
-/

open scoped InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-- Coordinate restriction along an embedding of a small finite index type
into a larger one. -/
def coordinateRestriction
    {ι κ : Type*} [DecidableEq κ]
    (e : ι → κ) : Matrix ι κ ℝ :=
  fun i j => if e i = j then 1 else 0

/-- Restriction followed by its transpose is the identity when the coordinate
map is injective. -/
theorem coordinateRestriction_mul_transpose
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {e : ι → κ} (he : Function.Injective e) :
    coordinateRestriction e * (coordinateRestriction e)ᵀ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [coordinateRestriction, Matrix.mul_apply]
  · have heij : e i ≠ e j := fun h => hij (he h)
    simp [coordinateRestriction, Matrix.mul_apply, hij, heij]

/-- Coordinate restrictions compose contravariantly. -/
theorem coordinateRestriction_mul
    {ι κ o : Type*} [Fintype κ]
    [DecidableEq κ] [DecidableEq o]
    (e : ι → κ) (f : κ → o) :
    coordinateRestriction e * coordinateRestriction f =
      coordinateRestriction (f ∘ e) := by
  ext i k
  simp only [coordinateRestriction, Matrix.mul_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · simp

/-- Restricting a bilinear form on both indices is matrix multiplication by
the coordinate restriction and its transpose. -/
theorem coordinateRestriction_mul_mul_transpose
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (gram : Matrix κ κ ℝ) :
    coordinateRestriction e * gram * (coordinateRestriction e)ᵀ =
      gram.submatrix e e := by
  ext i j
  simp [coordinateRestriction, Matrix.mul_apply]

/-- Canonical synthesis/inverse matrix associated to an exact whitening. -/
def whiteningSynthesis
    {ι : Type*} [Fintype ι]
    (gram whitening : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  gram * whiteningᵀ

/-- The synthesis matrix is a right inverse of an exact whitening. -/
theorem whitening_mul_whiteningSynthesis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {gram whitening : Matrix ι ι ℝ}
    (hwhite : whitening * gram * whiteningᵀ = 1) :
    whitening * whiteningSynthesis gram whitening = 1 := by
  simpa [whiteningSynthesis, Matrix.mul_assoc] using hwhite

/-- For finite square matrices the same synthesis is automatically also a
left inverse. -/
theorem whiteningSynthesis_mul_whitening
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {gram whitening : Matrix ι ι ℝ}
    (hwhite : whitening * gram * whiteningᵀ = 1) :
    whiteningSynthesis gram whitening * whitening = 1 := by
  exact (mul_eq_one_comm.mp
    (whitening_mul_whiteningSynthesis hwhite))

/-- The inverse synthesis reconstructs the original Gram matrix. -/
theorem whiteningSynthesis_mul_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {gram whitening : Matrix ι ι ℝ}
    (hwhite : whitening * gram * whiteningᵀ = 1) :
    whiteningSynthesis gram whitening *
        (whiteningSynthesis gram whitening)ᵀ = gram := by
  let synthesis := whiteningSynthesis gram whitening
  have hleft : synthesis * whitening = 1 :=
    whiteningSynthesis_mul_whitening hwhite
  have hleftT : whiteningᵀ * synthesisᵀ = 1 := by
    have h := congrArg Matrix.transpose hleft
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using h
  calc
    synthesis * synthesisᵀ =
        synthesis * (whitening * gram * whiteningᵀ) * synthesisᵀ := by
          rw [hwhite]
          simp
    _ = (synthesis * whitening) * gram *
        (whiteningᵀ * synthesisᵀ) := by noncomm_ring
    _ = gram := by rw [hleft, hleftT]; simp

/-- Raw cutoff restriction transported to the orthonormal signed coordinates.
Its transpose is the corresponding inclusion. -/
def orthonormalCutoffTransition
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (e : ι → κ)
    (largeGram : Matrix κ κ ℝ)
    (smallWhitening : Matrix ι ι ℝ)
    (largeWhitening : Matrix κ κ ℝ) : Matrix ι κ ℝ :=
  smallWhitening * coordinateRestriction e *
    whiteningSynthesis largeGram largeWhitening

/-- Transported cutoff maps are exact coisometries. -/
theorem orthonormalCutoffTransition_mul_transpose
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {e : ι → κ}
    {smallGram : Matrix ι ι ℝ} {largeGram : Matrix κ κ ℝ}
    {smallWhitening : Matrix ι ι ℝ}
    {largeWhitening : Matrix κ κ ℝ}
    (hsmall : smallWhitening * smallGram * smallWhiteningᵀ = 1)
    (hlarge : largeWhitening * largeGram * largeWhiteningᵀ = 1)
    (hprincipal : largeGram.submatrix e e = smallGram) :
    orthonormalCutoffTransition e largeGram smallWhitening largeWhitening *
        (orthonormalCutoffTransition
          e largeGram smallWhitening largeWhitening)ᵀ = 1 := by
  rw [orthonormalCutoffTransition, Matrix.transpose_mul,
    Matrix.transpose_mul]
  have hsynthesis := whiteningSynthesis_mul_transpose hlarge
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc
    (whiteningSynthesis largeGram largeWhitening)
    (whiteningSynthesis largeGram largeWhitening)ᵀ]
  rw [hsynthesis]
  rw [← Matrix.mul_assoc largeGram (coordinateRestriction e)ᵀ]
  rw [← Matrix.mul_assoc (coordinateRestriction e)
    (largeGram * (coordinateRestriction e)ᵀ)]
  rw [← Matrix.mul_assoc (coordinateRestriction e) largeGram]
  rw [coordinateRestriction_mul_mul_transpose, hprincipal]
  simpa only [Matrix.mul_assoc] using hsmall

/-- Exact cocycle law for transported cutoffs. -/
theorem orthonormalCutoffTransition_comp
    {ι κ o : Type*} [Fintype ι] [Fintype κ] [Fintype o]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq o]
    (e : ι → κ) (f : κ → o)
    (middleGram : Matrix κ κ ℝ) (largeGram : Matrix o o ℝ)
    (smallWhitening : Matrix ι ι ℝ)
    (middleWhitening : Matrix κ κ ℝ)
    (largeWhitening : Matrix o o ℝ)
    (hmiddle : middleWhitening * middleGram * middleWhiteningᵀ = 1) :
    orthonormalCutoffTransition e middleGram
        smallWhitening middleWhitening *
      orthonormalCutoffTransition f largeGram
        middleWhitening largeWhitening =
      orthonormalCutoffTransition (f ∘ e) largeGram
        smallWhitening largeWhitening := by
  have hinverse := whiteningSynthesis_mul_whitening hmiddle
  unfold orthonormalCutoffTransition
  calc
    (smallWhitening * coordinateRestriction e *
          whiteningSynthesis middleGram middleWhitening) *
        (middleWhitening * coordinateRestriction f *
          whiteningSynthesis largeGram largeWhitening) =
      smallWhitening * coordinateRestriction e *
        (whiteningSynthesis middleGram middleWhitening * middleWhitening) *
        coordinateRestriction f *
        whiteningSynthesis largeGram largeWhitening := by
          simp only [Matrix.mul_assoc]
    _ = smallWhitening *
        (coordinateRestriction e * coordinateRestriction f) *
        whiteningSynthesis largeGram largeWhitening := by
          rw [hinverse]
          simp [Matrix.mul_assoc]
    _ = smallWhitening * coordinateRestriction (f ∘ e) *
        whiteningSynthesis largeGram largeWhitening := by
          rw [coordinateRestriction_mul]

/-- The inverse of a reflection intertwiner intertwines in the reverse
direction. -/
theorem whiteningSynthesis_intertwines
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {gram whitening sourceReflection targetReflection : Matrix ι ι ℝ}
    (hwhite : whitening * gram * whiteningᵀ = 1)
    (hintertwine : whitening * sourceReflection =
      targetReflection * whitening) :
    whiteningSynthesis gram whitening * targetReflection =
      sourceReflection * whiteningSynthesis gram whitening := by
  let synthesis := whiteningSynthesis gram whitening
  have hleft : synthesis * whitening = 1 :=
    whiteningSynthesis_mul_whitening hwhite
  have hright : whitening * synthesis = 1 :=
    whitening_mul_whiteningSynthesis hwhite
  calc
    synthesis * targetReflection =
        synthesis * targetReflection * (whitening * synthesis) := by
          rw [hright, Matrix.mul_one]
    _ = synthesis * (targetReflection * whitening) * synthesis := by
          noncomm_ring
    _ = synthesis * (whitening * sourceReflection) * synthesis := by
          rw [hintertwine]
    _ = (synthesis * whitening) * sourceReflection * synthesis := by
          noncomm_ring
    _ = sourceReflection * synthesis := by rw [hleft]; simp

/-- Transported cutoff maps preserve a reflection whenever raw restriction
preserves the source grading and both finite whitenings realize the same
source-to-target intertwining law. -/
theorem orthonormalCutoffTransition_intertwines
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {e : ι → κ}
    {largeGram : Matrix κ κ ℝ}
    {smallWhitening : Matrix ι ι ℝ}
    {largeWhitening : Matrix κ κ ℝ}
    {smallSource smallTarget : Matrix ι ι ℝ}
    {largeSource largeTarget : Matrix κ κ ℝ}
    (hlarge : largeWhitening * largeGram * largeWhiteningᵀ = 1)
    (hsmallIntertwine : smallWhitening * smallSource =
      smallTarget * smallWhitening)
    (hlargeIntertwine : largeWhitening * largeSource =
      largeTarget * largeWhitening)
    (hrestriction : coordinateRestriction e * largeSource =
      smallSource * coordinateRestriction e) :
    orthonormalCutoffTransition e largeGram
        smallWhitening largeWhitening * largeTarget =
      smallTarget * orthonormalCutoffTransition e largeGram
        smallWhitening largeWhitening := by
  have hsynthesis := whiteningSynthesis_intertwines
    hlarge hlargeIntertwine
  unfold orthonormalCutoffTransition
  calc
    (smallWhitening * coordinateRestriction e *
        whiteningSynthesis largeGram largeWhitening) * largeTarget =
      smallWhitening * coordinateRestriction e *
        (whiteningSynthesis largeGram largeWhitening * largeTarget) := by
          simp only [Matrix.mul_assoc]
    _ = smallWhitening * coordinateRestriction e *
        (largeSource * whiteningSynthesis largeGram largeWhitening) := by
          rw [hsynthesis]
    _ = smallWhitening *
        ((coordinateRestriction e * largeSource) *
          whiteningSynthesis largeGram largeWhitening) := by
          simp only [Matrix.mul_assoc]
    _ = smallWhitening *
        ((smallSource * coordinateRestriction e) *
          whiteningSynthesis largeGram largeWhitening) := by
          rw [hrestriction]
    _ = smallWhitening *
        (smallSource * coordinateRestriction e) *
        whiteningSynthesis largeGram largeWhitening := by
          simp only [Matrix.mul_assoc]
    _ = (smallWhitening * smallSource) * coordinateRestriction e *
        whiteningSynthesis largeGram largeWhitening := by
          simp only [Matrix.mul_assoc]
    _ = smallTarget * smallWhitening * coordinateRestriction e *
        whiteningSynthesis largeGram largeWhitening := by
          rw [hsmallIntertwine]
    _ = smallTarget *
        (smallWhitening * coordinateRestriction e *
          whiteningSynthesis largeGram largeWhitening) := by
            simp only [Matrix.mul_assoc]

/-- The transpose of a coisometric cutoff map preserves the Euclidean dot
product exactly. -/
theorem transpose_mulVec_dotProduct_of_mul_transpose_eq_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    {cutoff : Matrix ι κ ℝ}
    (hcutoff : cutoff * cutoffᵀ = 1)
    (x y : ι → ℝ) :
    dotProduct (cutoffᵀ *ᵥ x) (cutoffᵀ *ᵥ y) =
      dotProduct x y := by
  calc
    dotProduct (cutoffᵀ *ᵥ x) (cutoffᵀ *ᵥ y) =
        dotProduct y (cutoff *ᵥ (cutoffᵀ *ᵥ x)) := by
          exact Matrix.dotProduct_transpose_mulVec cutoff
            (cutoffᵀ *ᵥ x) y
    _ = dotProduct y ((cutoff * cutoffᵀ) *ᵥ x) := by
          rw [Matrix.mulVec_mulVec]
    _ = dotProduct y x := by rw [hcutoff]; simp
    _ = dotProduct x y := dotProduct_comm _ _

/-! ## Canonical Green-jet specialization -/

/-- Embedding of both parity sectors from cutoff `N` into cutoff `M`. -/
def parityCutoffEmbedding {N M : ℕ} (hNM : N ≤ M) :
    (Fin N ⊕ Fin N) → (Fin M ⊕ Fin M) :=
  Sum.map (Fin.castLE hNM) (Fin.castLE hNM)

theorem parityCutoffEmbedding_injective
    {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (parityCutoffEmbedding hNM) :=
  (Fin.castLE_injective hNM).sumMap (Fin.castLE_injective hNM)

/-- Sign attached to the two parity sectors. -/
def paritySectorSign {ι : Type*} : ι ⊕ ι → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- The parity grading is the diagonal matrix of the sector sign. -/
theorem signedSectorGrading_eq_diagonal
    {ι : Type*} [DecidableEq ι] :
    signedSectorGrading (ι := ι) =
      Matrix.diagonal paritySectorSign := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst j
      simp [signedSectorGrading, paritySectorSign]
    · simp [signedSectorGrading, hij]
  · simp [signedSectorGrading]
  · simp [signedSectorGrading]
  · by_cases hij : i = j
    · subst j
      simp [signedSectorGrading, paritySectorSign]
    · simp [signedSectorGrading, hij]

/-- The full even/odd Green Gram has the same exact principal law as its two
Hankel blocks. -/
theorem parityJetGram_submatrix_parityCutoffEmbedding
    (moments : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    (parityJetGram (hankelGram moments M) (shiftedHankel moments M)).submatrix
        (parityCutoffEmbedding hNM) (parityCutoffEmbedding hNM) =
      parityJetGram (hankelGram moments N) (shiftedHankel moments N) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    rfl

/-- Raw parity restriction commutes exactly with the even/odd grading. -/
theorem coordinateRestriction_parityCutoffEmbedding_mul_grading
    {N M : ℕ} (hNM : N ≤ M) :
    coordinateRestriction (parityCutoffEmbedding hNM) *
        signedSectorGrading =
      signedSectorGrading *
        coordinateRestriction (parityCutoffEmbedding hNM) := by
  rw [signedSectorGrading_eq_diagonal,
    signedSectorGrading_eq_diagonal]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold coordinateRestriction
  split_ifs with hij
  · subst j
    rcases i with i | i <;>
      simp [paritySectorSign, parityCutoffEmbedding]
  · simp

/-- A globally independent even Green-jet family has independent finite
prefixes. -/
theorem greenJetEven_prefix_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inl (i : ℕ))) := by
  simpa [Function.comp_def] using
    heven.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective

/-- A globally independent odd Green-jet family has independent finite
prefixes. -/
theorem greenJetOdd_prefix_linearIndependent
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inr (i : ℕ))) := by
  simpa [Function.comp_def] using
    hodd.comp (fun i : Fin N => (i : ℕ)) Fin.val_injective

/-- The canonical finite intertwiner selected from globally independent
Green jets. -/
def canonicalGreenJetSignedHeightSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  canonicalGreenJetSignedHeightIntertwiner hrep N
    (greenJetEven_prefix_linearIndependent heven N)
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- Transported signed-coordinate cutoff from order `M` down to order `N`.
Its transpose is the canonical inclusion from `N` into `M`. -/
def canonicalGreenJetSignedHeightCutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    Matrix (Fin N ⊕ Fin N) (Fin M ⊕ Fin M) ℝ :=
  orthonormalCutoffTransition
    (parityCutoffEmbedding hNM)
    (parityJetGram (hankelGram moments M) (shiftedHankel moments M))
    (canonicalGreenJetSignedHeightSection hrep heven hodd N)
    (canonicalGreenJetSignedHeightSection hrep heven hodd M)

/-- Every finite section still whitens the corresponding parity Gram. -/
theorem canonicalGreenJetSignedHeightSection_whitens
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    canonicalGreenJetSignedHeightSection hrep heven hodd N *
        parityJetGram (hankelGram moments N) (shiftedHankel moments N) *
        (canonicalGreenJetSignedHeightSection hrep heven hodd N)ᵀ = 1 := by
  exact canonicalGreenJetSignedHeightIntertwiner_whitens hrep N
    (greenJetEven_prefix_linearIndependent heven N)
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- Every finite section realizes the Green grading as signed-sector
reflection. -/
theorem canonicalGreenJetSignedHeightSection_intertwines
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    canonicalGreenJetSignedHeightSection hrep heven hodd N *
        signedSectorGrading =
      signedSectorReflection *
        canonicalGreenJetSignedHeightSection hrep heven hodd N := by
  exact canonicalGreenJetSignedHeightIntertwiner_intertwines hrep N
    (greenJetEven_prefix_linearIndependent heven N)
    (greenJetOdd_prefix_linearIndependent hodd N)

/-- The transported cutoff is an exact coisometry, so its transpose embeds
the smaller signed section isometrically in the larger one. -/
theorem canonicalGreenJetSignedHeightCutoff_mul_transpose
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM *
        (canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM)ᵀ = 1 := by
  apply orthonormalCutoffTransition_mul_transpose
  · exact canonicalGreenJetSignedHeightSection_whitens
      hrep heven hodd N
  · exact canonicalGreenJetSignedHeightSection_whitens
      hrep heven hodd M
  · exact parityJetGram_submatrix_parityCutoffEmbedding moments hNM

/-- Exact cocycle law: going from `L` to `N` through `M` is identical to the
direct transported cutoff. -/
theorem canonicalGreenJetSignedHeightCutoff_comp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M L : ℕ} (hNM : N ≤ M) (hML : M ≤ L) :
    canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM *
        canonicalGreenJetSignedHeightCutoff hrep heven hodd hML =
      canonicalGreenJetSignedHeightCutoff hrep heven hodd
        (hNM.trans hML) := by
  simpa [canonicalGreenJetSignedHeightCutoff,
    parityCutoffEmbedding, Function.comp_def] using
    (orthonormalCutoffTransition_comp
      (parityCutoffEmbedding hNM) (parityCutoffEmbedding hML)
      (parityJetGram (hankelGram moments M) (shiftedHankel moments M))
      (parityJetGram (hankelGram moments L) (shiftedHankel moments L))
      (canonicalGreenJetSignedHeightSection hrep heven hodd N)
      (canonicalGreenJetSignedHeightSection hrep heven hodd M)
      (canonicalGreenJetSignedHeightSection hrep heven hodd L)
      (canonicalGreenJetSignedHeightSection_whitens
        hrep heven hodd M))

/-- The entire cutoff system preserves the signed-sector reflection. -/
theorem canonicalGreenJetSignedHeightCutoff_intertwines_reflection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM *
        signedSectorReflection =
      signedSectorReflection *
        canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM := by
  apply orthonormalCutoffTransition_intertwines
  · exact canonicalGreenJetSignedHeightSection_whitens hrep heven hodd M
  · exact canonicalGreenJetSignedHeightSection_intertwines hrep heven hodd N
  · exact canonicalGreenJetSignedHeightSection_intertwines hrep heven hodd M
  · exact coordinateRestriction_parityCutoffEmbedding_mul_grading hNM

/-- Inclusion form of reflection compatibility. -/
theorem canonicalGreenJetSignedHeightCutoff_transpose_intertwines_reflection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    signedSectorReflection *
        (canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM)ᵀ =
      (canonicalGreenJetSignedHeightCutoff hrep heven hodd hNM)ᵀ *
        signedSectorReflection := by
  have h := congrArg Matrix.transpose
    (canonicalGreenJetSignedHeightCutoff_intertwines_reflection
      hrep heven hodd hNM)
  simpa only [Matrix.transpose_mul,
    signedSectorReflection_isSymm.eq] using h

/-- Dot products are independent of the finite cutoff after transport to any
larger section.  This is the exact pre-completion metric identity. -/
theorem canonicalGreenJetSignedHeightCutoff_transpose_preserves_dotProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M)
    (x y : (Fin N ⊕ Fin N) → ℝ) :
    dotProduct
        ((canonicalGreenJetSignedHeightCutoff
          hrep heven hodd hNM)ᵀ *ᵥ x)
        ((canonicalGreenJetSignedHeightCutoff
          hrep heven hodd hNM)ᵀ *ᵥ y) =
      dotProduct x y := by
  exact transpose_mulVec_dotProduct_of_mul_transpose_eq_one
    (canonicalGreenJetSignedHeightCutoff_mul_transpose
      hrep heven hodd hNM) x y

/-! ## Metric inductive limit and completion -/

/-- The transpose cutoff preserves the real inner product on finite
Euclidean signed-coordinate spaces. -/
theorem canonicalGreenJetSignedHeightCutoff_transpose_preserves_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M)
    (x y : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    ⟪(Matrix.toEuclideanLin
          (canonicalGreenJetSignedHeightCutoff
            hrep heven hodd hNM)ᵀ) x,
        (Matrix.toEuclideanLin
          (canonicalGreenJetSignedHeightCutoff
            hrep heven hodd hNM)ᵀ) y⟫_ℝ =
      ⟪x, y⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    star_trivial]
  exact canonicalGreenJetSignedHeightCutoff_transpose_preserves_dotProduct
    hrep heven hodd hNM (WithLp.ofLp y) (WithLp.ofLp x)

/-- Canonical linear isometric inclusion from the order-`N` signed section
into the order-`M` signed section. -/
def canonicalGreenJetSignedHeightCutoffLinearIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    {N M : ℕ} (hNM : N ≤ M) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin M ⊕ Fin M) :=
  (Matrix.toEuclideanLin
      (canonicalGreenJetSignedHeightCutoff
        hrep heven hodd hNM)ᵀ).isometryOfInner
    (canonicalGreenJetSignedHeightCutoff_transpose_preserves_inner
      hrep heven hodd hNM)

/-- Consecutive isometric inclusion used by the inductive-limit
construction. -/
def canonicalGreenJetSignedHeightSuccessorMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →
      EuclideanSpace ℝ (Fin (N + 1) ⊕ Fin (N + 1)) :=
  canonicalGreenJetSignedHeightCutoffLinearIsometry
    hrep heven hodd (Nat.le_succ N)

/-- Each successor map is an isometry. -/
theorem canonicalGreenJetSignedHeightSuccessorMap_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    Isometry (canonicalGreenJetSignedHeightSuccessorMap
      hrep heven hodd N) :=
  (canonicalGreenJetSignedHeightCutoffLinearIsometry
    hrep heven hodd (Nat.le_succ N)).isometry

/-- Algebraic/metric direct limit of all canonical finite signed-height
sections. -/
def CanonicalGreenJetSignedHeightInductiveLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) : Type _ :=
  Metric.InductiveLimit
    (canonicalGreenJetSignedHeightSuccessorMap_isometry hrep heven hodd)

noncomputable instance canonicalGreenJetSignedHeightInductiveLimitMetricSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) :
    MetricSpace
      (CanonicalGreenJetSignedHeightInductiveLimit hrep heven hodd) :=
  inferInstanceAs
    (MetricSpace
      (Metric.InductiveLimit
        (canonicalGreenJetSignedHeightSuccessorMap_isometry
          hrep heven hodd)))

/-- Complete metric carrier generated by the exact finite intertwiner tower. -/
abbrev CanonicalGreenJetSignedHeightCompletion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n))) : Type _ :=
  UniformSpace.Completion
    (CanonicalGreenJetSignedHeightInductiveLimit hrep heven hodd)

/-- Canonical map of a finite signed section into the inductive limit. -/
def canonicalGreenJetSignedHeightToInductiveLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →
      CanonicalGreenJetSignedHeightInductiveLimit hrep heven hodd :=
  Metric.toInductiveLimit
    (canonicalGreenJetSignedHeightSuccessorMap_isometry hrep heven hodd) N

/-- Canonical finite-section map into the completed carrier. -/
def canonicalGreenJetSignedHeightToCompletion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) →
      CanonicalGreenJetSignedHeightCompletion hrep heven hodd :=
  fun x => (canonicalGreenJetSignedHeightToInductiveLimit
    hrep heven hodd N x :
      CanonicalGreenJetSignedHeightCompletion hrep heven hodd)

/-- Every finite signed section embeds isometrically into the completed
carrier. -/
theorem canonicalGreenJetSignedHeightToCompletion_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    Isometry (canonicalGreenJetSignedHeightToCompletion
      hrep heven hodd N) :=
  UniformSpace.Completion.coe_isometry.comp
    (Metric.toInductiveLimit_isometry
      (canonicalGreenJetSignedHeightSuccessorMap_isometry
        hrep heven hodd) N)

/-- Consecutive finite inclusions become literally equal in the inductive
limit. -/
theorem canonicalGreenJetSignedHeightToInductiveLimit_commute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (hodd : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inr n)))
    (N : ℕ) :
    canonicalGreenJetSignedHeightToInductiveLimit hrep heven hodd (N + 1) ∘
        canonicalGreenJetSignedHeightSuccessorMap hrep heven hodd N =
      canonicalGreenJetSignedHeightToInductiveLimit hrep heven hodd N := by
  exact Metric.toInductiveLimit_commute
    (canonicalGreenJetSignedHeightSuccessorMap_isometry
      hrep heven hodd) N

end

end CarrySelfAdjointOperator
