import CarrySelfAdjointOperator.GreenWronskianHankelBridge
import CarrySelfAdjointOperator.SignedFiniteHeightOperator
import NativeCarrySpectralWeyl.Finite.Whitening
import Mathlib.Tactic

/-!
# Canonical finite Green-jet to signed-height intertwiner

One reflected Green kernel supplies two orthogonal finite jet sectors.  Their
Gram matrices are the Hankel pair `G_N` and `K_N`.  Canonical LDL whitening
normalizes `G_N`; the transported matrix is `J_N`, and the already constructed
height `T_N = J_N⁻¹ᐟ²` normalizes that remaining positive form.

Consequently

`W_N = diag(B_N, T_N B_N)`

whitens the full parity Gram `diag(G_N,K_N)`.  The canonical Hadamard rotation
turns the even/odd grading into the signed-sector swap.  Their composition

`B_N = U_N W_N`

is therefore the exact finite intertwiner from Green parity coordinates to
signed-height coordinates.  It is derived from the moment kernel and its
positivity certificates; no target height or fitted matrix is an input.
-/

open scoped Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Finite

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The normalized two-sector Hadamard rotation. -/
def signedSectorHadamard : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  let q := (Real.sqrt 2)⁻¹
  Matrix.fromBlocks (q • 1) (q • 1) (q • 1) ((-q) • 1)

/-- The Hadamard rotation is symmetric. -/
theorem signedSectorHadamard_isSymm :
    (signedSectorHadamard (ι := ι)).IsSymm := by
  exact Matrix.IsSymm.fromBlocks (by simp) (by simp) (by simp)

/-- The normalized Hadamard rotation squares to the identity. -/
theorem signedSectorHadamard_sq [Fintype ι] :
    signedSectorHadamard (ι := ι) * signedSectorHadamard = 1 := by
  have hq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2 = 1 := by
    rw [← sq, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    by_cases hij : i = j
    · subst j
      simp [signedSectorHadamard, Matrix.fromBlocks_multiply]
      try nlinarith [hq]
    · simp [signedSectorHadamard, Matrix.fromBlocks_multiply, hij]

/-- Orthogonality of the Hadamard rotation. -/
theorem signedSectorHadamard_mul_transpose [Fintype ι] :
    signedSectorHadamard (ι := ι) * signedSectorHadamardᵀ = 1 := by
  rw [signedSectorHadamard_isSymm.eq]
  exact signedSectorHadamard_sq

/-- Hadamard converts the parity grading into the signed-sector reflection. -/
theorem signedSectorHadamard_intertwines_grading_reflection [Fintype ι] :
    signedSectorHadamard (ι := ι) * signedSectorGrading =
      signedSectorReflection * signedSectorHadamard := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [signedSectorHadamard, signedSectorGrading,
      signedSectorReflection, Matrix.fromBlocks_multiply]

/-- Equivalent conjugation form of the grading/reflection crosswalk. -/
theorem signedSectorHadamard_conj_grading [Fintype ι] :
    signedSectorHadamard (ι := ι) * signedSectorGrading *
        signedSectorHadamard = signedSectorReflection := by
  rw [signedSectorHadamard_intertwines_grading_reflection,
    Matrix.mul_assoc, signedSectorHadamard_sq, Matrix.mul_one]

/-- Raw parity Gram carried by the even and odd Green-jet sectors. -/
def parityJetGram (evenGram oddGram : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks evenGram 0 0 oddGram

/-- Block whitening: ordinary Hankel whitening in the even sector and the
height-normalized whitening in the odd sector. -/
def parityJetWhitening
    [Fintype ι]
    (gramWhitening height : Matrix ι ι ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks gramWhitening 0 0 (height * gramWhitening)

/-- Block whitening commutes with the even/odd grading. -/
theorem parityJetWhitening_commute_grading
    [Fintype ι]
    (gramWhitening height : Matrix ι ι ℝ) :
    Commute (parityJetWhitening gramWhitening height)
      signedSectorGrading := by
  show parityJetWhitening gramWhitening height * signedSectorGrading =
    signedSectorGrading * parityJetWhitening gramWhitening height
  simp [parityJetWhitening, signedSectorGrading,
    Matrix.fromBlocks_multiply]

/-- Simultaneous whitening of the two parity sectors. -/
theorem parityJetWhitening_whitens
    [Fintype ι]
    {evenGram oddGram gramWhitening height : Matrix ι ι ℝ}
    (heven : gramWhitening * evenGram * gramWhiteningᵀ = 1)
    (hodd : height *
        (gramWhitening * oddGram * gramWhiteningᵀ) * height = 1)
    (hheight : height.IsSymm) :
    parityJetWhitening gramWhitening height *
        parityJetGram evenGram oddGram *
        (parityJetWhitening gramWhitening height)ᵀ = 1 := by
  rw [parityJetWhitening, parityJetGram, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_mul,
    Matrix.fromBlocks_multiply]
  rw [hheight.eq]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [heven]
  have hodd' :
      (height * gramWhitening) * oddGram *
          (gramWhiteningᵀ * height) = 1 := by
    calc
      (height * gramWhitening) * oddGram *
          (gramWhiteningᵀ * height) =
        height * (gramWhitening * oddGram * gramWhiteningᵀ) *
          height := by noncomm_ring
      _ = 1 := hodd
  rw [hodd']
  simp only [← Matrix.fromBlocks_one]

/-- The functional-calculus height agrees exactly with the positive inverse
square root used by the whitening package. -/
theorem finiteHeightOperator_eq_positiveInverseSqrt
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    finiteHeightOperator hjacobi = positiveInverseSqrt jacobi := by
  rw [finiteHeightOperator,
    ← Matrix.IsHermitian.cfc_eq hjacobi.isHermitian]
  unfold positiveInverseSqrt
  rw [CFC.sqrt_eq_real_sqrt jacobi hjacobi.posSemidef.nonneg,
    cfcₙ_eq_cfc]
  simpa only [← Matrix.nonsing_inv_eq_ringInverse] using
    (cfc_inv Real.sqrt jacobi (fun x hx ↦ ne_of_gt
      (Real.sqrt_pos.2 (hjacobi.isStrictlyPositive.spectrum_pos hx))))

/-- The finite height exactly whitens its positive Jacobi section. -/
theorem finiteHeightOperator_whitens
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    finiteHeightOperator hjacobi * jacobi *
        finiteHeightOperator hjacobi = 1 := by
  rw [finiteHeightOperator_eq_positiveInverseSqrt]
  exact positiveInverseSqrt_whitens hjacobi

/-- Canonical simultaneous whitening of the finite Green parity jets. -/
def canonicalGreenParityJetWhitening
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inr (i : ℕ)))) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  let evenRep := greenWronskianMomentKernel_even_momentGram hrep
  let oddRep := greenWronskianMomentKernel_odd_shiftedMomentGram hrep
  let hgram := hankelGram_posDef_of_gramRepresentation evenRep N heven
  let hjacobi := canonicalFiniteJacobiSection_posDef_of_shiftedGram
    oddRep N hgram hodd
  parityJetWhitening
    (canonicalLDLInverseFactor hgram)
    (finiteHeightOperator hjacobi)

/-- Canonical finite intertwiner from Green parity-jet coordinates to the
signed-height sector coordinates. -/
def canonicalGreenJetSignedHeightIntertwiner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inr (i : ℕ)))) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  signedSectorHadamard *
    canonicalGreenParityJetWhitening hrep N heven hodd

/-- The canonical finite map is the desired reflection intertwiner:
Green even/odd grading on the source becomes signed-sector swap on the
target. -/
theorem canonicalGreenJetSignedHeightIntertwiner_intertwines
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inr (i : ℕ)))) :
    canonicalGreenJetSignedHeightIntertwiner hrep N heven hodd *
        signedSectorGrading =
      signedSectorReflection *
        canonicalGreenJetSignedHeightIntertwiner hrep N heven hodd := by
  have hcomm :
      Commute (canonicalGreenParityJetWhitening hrep N heven hodd)
        signedSectorGrading := by
    unfold canonicalGreenParityJetWhitening
    exact parityJetWhitening_commute_grading _ _
  unfold canonicalGreenJetSignedHeightIntertwiner
  rw [Matrix.mul_assoc,
    hcomm.eq]
  rw [← Matrix.mul_assoc,
    signedSectorHadamard_intertwines_grading_reflection,
    Matrix.mul_assoc]

/-- Adjoint/synthesis form of the same intertwining law. -/
theorem canonicalGreenJetSignedHeightIntertwiner_transpose_intertwines
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inr (i : ℕ)))) :
    signedSectorGrading *
        (canonicalGreenJetSignedHeightIntertwiner
          hrep N heven hodd)ᵀ =
      (canonicalGreenJetSignedHeightIntertwiner
        hrep N heven hodd)ᵀ * signedSectorReflection := by
  have h := congrArg Matrix.transpose
    (canonicalGreenJetSignedHeightIntertwiner_intertwines
      hrep N heven hodd)
  simpa only [Matrix.transpose_mul,
    signedSectorGrading_isSymm.eq,
    signedSectorReflection_isSymm.eq] using h

/-- The same canonical map whitens the complete finite parity Gram exactly. -/
theorem canonicalGreenJetSignedHeightIntertwiner_whitens
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N ↦ jet (Sum.inr (i : ℕ)))) :
    canonicalGreenJetSignedHeightIntertwiner hrep N heven hodd *
        parityJetGram (hankelGram moments N) (shiftedHankel moments N) *
        (canonicalGreenJetSignedHeightIntertwiner
          hrep N heven hodd)ᵀ = 1 := by
  let evenRep := greenWronskianMomentKernel_even_momentGram hrep
  let oddRep := greenWronskianMomentKernel_odd_shiftedMomentGram hrep
  let hgram := hankelGram_posDef_of_gramRepresentation evenRep N heven
  let hjacobi := canonicalFiniteJacobiSection_posDef_of_shiftedGram
    oddRep N hgram hodd
  have hW :
      canonicalGreenParityJetWhitening hrep N heven hodd *
          parityJetGram (hankelGram moments N) (shiftedHankel moments N) *
          (canonicalGreenParityJetWhitening hrep N heven hodd)ᵀ = 1 := by
    unfold canonicalGreenParityJetWhitening
    exact parityJetWhitening_whitens
      (canonicalLDLInverseFactor_whitens hgram)
      (by
        change finiteHeightOperator hjacobi *
            canonicalFiniteJacobiSection moments N hgram *
            finiteHeightOperator hjacobi = 1
        exact finiteHeightOperator_whitens hjacobi)
      (finiteHeightOperator_isSymm hjacobi)
  unfold canonicalGreenJetSignedHeightIntertwiner
  rw [Matrix.transpose_mul]
  calc
    (signedSectorHadamard *
          canonicalGreenParityJetWhitening hrep N heven hodd) *
        parityJetGram (hankelGram moments N) (shiftedHankel moments N) *
        ((canonicalGreenParityJetWhitening hrep N heven hodd)ᵀ *
          signedSectorHadamardᵀ) =
      signedSectorHadamard *
        (canonicalGreenParityJetWhitening hrep N heven hodd *
          parityJetGram (hankelGram moments N) (shiftedHankel moments N) *
          (canonicalGreenParityJetWhitening hrep N heven hodd)ᵀ) *
        signedSectorHadamardᵀ := by noncomm_ring
    _ = signedSectorHadamard * 1 * signedSectorHadamardᵀ := by rw [hW]
    _ = 1 := by simpa using
      (signedSectorHadamard_mul_transpose (ι := Fin N))

end

end CarrySelfAdjointOperator
