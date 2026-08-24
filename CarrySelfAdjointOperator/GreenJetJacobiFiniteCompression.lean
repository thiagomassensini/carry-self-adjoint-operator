import CarrySelfAdjointOperator.GreenJetFormalAdjointSquare
import CarrySelfAdjointOperator.CanonicalLDLPrefixReduction
import Mathlib.Tactic

/-!
# Finite compressions of the infinite Green-jet Jacobi core

The exact projective matrix tower and the infinite Green-jet operator were
previously available as separate constructions.  This file identifies them:
the canonical LDL-whitened finite vectors lie in the dense Jacobi core, and
the matrix coefficients of the infinite core on those vectors are exactly
the canonical finite Jacobi section at every order.
-/

open scoped InnerProductSpace Matrix BigOperators

namespace CarrySelfAdjointOperator

noncomputable section

/-- Row synthesis transports Gram matrices by the same congruence used in the
finite Jacobi construction. -/
theorem gram_matrixRowSynthesis
    {I J E : Type*} [Fintype I] [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Matrix I J ℝ) (v : J → E) :
    Matrix.gram ℝ (matrixRowSynthesis A v) =
      A * Matrix.gram ℝ v * Aᵀ := by
  classical
  ext i j
  simp only [Matrix.gram_apply, matrixRowSynthesis, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  ring

/-- Linear maps commute with finite row synthesis. -/
theorem LinearMap.map_matrixRowSynthesis
    {I J E F : Type*} [Fintype J]
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (A : Matrix I J ℝ) (v : J → E) (i : I) :
    f (matrixRowSynthesis A v i) =
      matrixRowSynthesis A (fun j => f (v j)) i := by
  classical
  simp [matrixRowSynthesis]

/-- Canonical all-order positive-definite Hankel certificate obtained from
the globally independent even Green jets. -/
theorem canonicalGreenJetHankelGramCertificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (hankelGram moments N).PosDef :=
  hankelGram_posDef_of_gramRepresentation
    (greenWronskianMomentKernel_even_momentGram hrep) N
    (greenJetEven_prefix_linearIndependent heven N)

/-- The order-`N` canonical LDL-whitened even vector, retained as an element
of the algebraic domain of the infinite Jacobi core. -/
def canonicalGreenJetEvenJacobiCoreVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) (i : Fin N) : greenJetEvenOperatorCore jet :=
  matrixRowSynthesis
    (canonicalLDLInverseFactor
      (canonicalGreenJetHankelGramCertificate hrep heven N))
    (fun j : Fin N => greenJetEvenCoreJet jet (j : ℕ)) i

/-- The energy factor sends a whitened even core vector to the same row
synthesis of odd Green jets. -/
theorem greenJetEnergyFactorCore_canonicalEvenJacobiCoreVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) (i : Fin N) :
    greenJetEnergyFactorCore heven
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N i) =
      matrixRowSynthesis
        (canonicalLDLInverseFactor
          (canonicalGreenJetHankelGramCertificate hrep heven N))
        (fun j : Fin N => greenJetOddSectorJet jet (j : ℕ)) i := by
  classical
  calc
    greenJetEnergyFactorCore heven
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N i) =
        ((greenJetEnergyFactorToFormalAdjointDomain heven
          (canonicalGreenJetEvenJacobiCoreVector hrep heven N i) :
            greenJetOddOperatorCore jet) :
          greenJetOddHilbertSubspace jet) :=
      (greenJetEnergyFactorToFormalAdjointDomain_coe heven _).symm
    _ = matrixRowSynthesis
        (canonicalLDLInverseFactor
          (canonicalGreenJetHankelGramCertificate hrep heven N))
        (fun j : Fin N => greenJetOddSectorJet jet (j : ℕ)) i := by
      unfold canonicalGreenJetEvenJacobiCoreVector
      rw [LinearMap.map_matrixRowSynthesis]
      change (greenJetOddOperatorCore jet).subtype
          (matrixRowSynthesis
            (canonicalLDLInverseFactor
              (canonicalGreenJetHankelGramCertificate hrep heven N))
            (fun j : Fin N =>
              greenJetEnergyFactorToFormalAdjointDomain heven
                (greenJetEvenCoreJet jet (j : ℕ))) i) = _
      rw [LinearMap.map_matrixRowSynthesis]
      congr 1
      funext j
      rw [greenJetEnergyFactorToFormalAdjointDomain_jet]
      rfl

/-- The finite odd Green-sector prefix has exactly the shifted Hankel Gram. -/
theorem gram_greenJetOddSectorJet_prefix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    Matrix.gram ℝ
        (fun j : Fin N => greenJetOddSectorJet jet (j : ℕ)) =
      shiftedHankel moments N := by
  ext i j
  have hodd :=
    greenWronskianMomentKernel_odd_shiftedMomentGram hrep
      (i : ℕ) (j : ℕ)
  simpa [Matrix.gram, greenJetOddSectorJet, greenJetInHilbert] using
    hodd.symm

/-- Main finite-to-infinite passage: every canonical finite Jacobi section is
the exact compression matrix of the single infinite Green-jet Jacobi core on
the corresponding canonical LDL-whitened vectors. -/
theorem greenJetJacobiCore_finiteCompression_eq_canonicalFiniteJacobiSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (fun i j : Fin N =>
      ⟪greenJetJacobiCoreMap heven
          (canonicalGreenJetEvenJacobiCoreVector hrep heven N i),
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N j :
          greenJetEvenHilbertSubspace jet)⟫_ℝ) =
      canonicalFiniteJacobiSection moments N
        (canonicalGreenJetHankelGramCertificate hrep heven N) := by
  let A := canonicalLDLInverseFactor
    (canonicalGreenJetHankelGramCertificate hrep heven N)
  let oddPrefix : Fin N → greenJetOddHilbertSubspace jet :=
    fun j => greenJetOddSectorJet jet (j : ℕ)
  have hgram := gram_matrixRowSynthesis A oddPrefix
  rw [gram_greenJetOddSectorJet_prefix hrep N] at hgram
  ext i j
  rw [greenJetJacobiCore_energyIdentity hrep heven,
    greenJetEnergyFactorCore_canonicalEvenJacobiCoreVector,
    greenJetEnergyFactorCore_canonicalEvenJacobiCoreVector]
  have hij := congrArg (fun B : Matrix (Fin N) (Fin N) ℝ => B i j) hgram
  simpa [Matrix.gram_apply, A, oddPrefix,
    canonicalFiniteJacobiSection, finiteJacobiSection,
    canonicalHankelWhitening, FiniteGramWhitening.ofIdentity,
    finiteJacobiTransport] using hij

/-- The operator-core compression and the entrywise projective limit have the
same order-`N` cylinder.  Hence the two independently constructed infinite
objects agree on every finite matrix coefficient. -/
theorem greenJetJacobiCore_finiteCompression_eq_projectiveLimit_submatrix
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (fun i j : Fin N =>
      ⟪greenJetJacobiCoreMap heven
          (canonicalGreenJetEvenJacobiCoreVector hrep heven N i),
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N j :
          greenJetEvenHilbertSubspace jet)⟫_ℝ) =
      (canonicalJacobiTowerLimitMatrix moments
          (canonicalGreenJetHankelGramCertificate hrep heven)).submatrix
        (fun i : Fin N => (i : ℕ))
        (fun i : Fin N => (i : ℕ)) := by
  rw [canonicalJacobiTowerLimitMatrix_submatrix_unconditional]
  exact
    greenJetJacobiCore_finiteCompression_eq_canonicalFiniteJacobiSection
      hrep heven N

/-! ## Passage to the canonical closed realization -/

/-- Every canonical finite LDL vector belongs canonically to the domain of
the graph closure of the infinite Jacobi core. -/
def canonicalGreenJetEvenClosedJacobiDomainVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) (i : Fin N) :
    (closedGreenJetJacobiOperator hrep heven).domain :=
  Submodule.inclusion (greenJetJacobiCore heven).le_closure.1
    (⟨canonicalGreenJetEvenJacobiCoreVector hrep heven N i,
      (canonicalGreenJetEvenJacobiCoreVector hrep heven N i).property⟩ :
      (greenJetJacobiCore heven).domain)

/-- Closing the graph does not alter the Jacobi action on any canonical
finite vector. -/
theorem closedGreenJetJacobiOperator_canonicalFiniteVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) (i : Fin N) :
    closedGreenJetJacobiOperator hrep heven
        (canonicalGreenJetEvenClosedJacobiDomainVector
          hrep heven N i) =
      greenJetJacobiCoreMap heven
        (canonicalGreenJetEvenJacobiCoreVector hrep heven N i) := by
  have haction := LinearPMap.apply_comp_inclusion
    (greenJetJacobiCore heven).le_closure
    (⟨canonicalGreenJetEvenJacobiCoreVector hrep heven N i,
      (canonicalGreenJetEvenJacobiCoreVector hrep heven N i).property⟩ :
      (greenJetJacobiCore heven).domain)
  simpa [closedGreenJetJacobiOperator,
    canonicalGreenJetEvenClosedJacobiDomainVector,
    greenJetJacobiCore] using haction.symm

/-- The actual closed infinite Jacobi realization retains every finite
canonical section exactly.  This is the graph-closure form of the
finite-to-infinite passage. -/
theorem closedGreenJetJacobiOperator_finiteCompression_eq_canonicalSection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (N : ℕ) :
    (fun i j : Fin N =>
      ⟪closedGreenJetJacobiOperator hrep heven
          (canonicalGreenJetEvenClosedJacobiDomainVector
            hrep heven N i),
        (canonicalGreenJetEvenClosedJacobiDomainVector
          hrep heven N j : greenJetEvenHilbertSubspace jet)⟫_ℝ) =
      canonicalFiniteJacobiSection moments N
        (canonicalGreenJetHankelGramCertificate hrep heven N) := by
  ext i j
  rw [closedGreenJetJacobiOperator_canonicalFiniteVector]
  have hcompression := congrArg
    (fun A : Matrix (Fin N) (Fin N) ℝ => A i j)
    (greenJetJacobiCore_finiteCompression_eq_canonicalFiniteJacobiSection
      hrep heven N)
  simpa [canonicalGreenJetEvenClosedJacobiDomainVector] using hcompression

end

end CarrySelfAdjointOperator
