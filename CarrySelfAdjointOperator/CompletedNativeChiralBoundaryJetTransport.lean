import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifference
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundarySplit

/-!
# Whole-source boundary transport through the existing signed difference jets

Only finite vector synthesis is added. The old projective/chiral carrier,
radial grid, factorial normalization and signed form remain unchanged. The
phases come from the raw boundary. No sign, metric or new operator is supplied.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

private def boundaryJetOrder {n : ℕ} : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i => 2*(i : ℕ)) (fun i => 2*(i : ℕ)+1)

private def boundaryJetCoefficient (n : ℕ) (x : Fin (2*n) → ℂ) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (nativeSourceEvenBoundaryPhase n x) (nativeSourceOddBoundaryPhase n x)

/-- Synthesizes ALL even/odd jets before either norm or scalar readout.
Every finite-step mixed cross is retained. -/
def nativeSourceProjectiveBoundaryJetSynthesis (n k : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  ∑ i : Fin n ⊕ Fin n, boundaryJetCoefficient n x i •
    projectiveChiralDifferenceJet k (boundaryJetOrder i)

private theorem form_synthesis {ι : Type*} [Fintype ι]
    (u v : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (∑ i, u i) (∑ j, v j) =
      ∑ i, ∑ j, canonicalCompletedNativeProjectiveChiralForm (u i) (v j) := by
  have hf (f : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
      (∑ i, f i).1 = ∑ i, (f i).1 :=
    map_sum (AddMonoidHom.fst _ _) f Finset.univ
  have hs (f : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
      (∑ i, f i).2 = ∑ i, (f i).2 :=
    map_sum (AddMonoidHom.snd _ _) f Finset.univ
  simp only [canonicalCompletedNativeProjectiveChiralForm,hf,hs,sum_inner,inner_sum]
  rw [Finset.sum_comm (f := fun j i => inner ℂ (u i).1 (v j).1),
    Finset.sum_comm (f := fun j i => inner ℂ (u i).2 (v j).2)]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

/-- Two independent whole-source syntheses, with every ordered cross and
Mathlib's conjugate-linear first argument. No limiting mixed zero is used. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_pairing (n k : ℕ)
    (x y : Fin (2*n) → ℂ) :
    canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y) =
    ∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
      conj (boundaryJetCoefficient n x i) * boundaryJetCoefficient n y j *
        canonicalCompletedNativeProjectiveChiralForm
          (projectiveChiralDifferenceJet k (boundaryJetOrder i))
          (projectiveChiralDifferenceJet k (boundaryJetOrder j)) := by
  unfold nativeSourceProjectiveBoundaryJetSynthesis
  rw [form_synthesis]
  simp only [projectiveChiralForm_smul]

private theorem pairing_limit (n : ℕ) (x y : Fin (2*n) → ℂ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y)) atTop
      (nhds (∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
        conj (boundaryJetCoefficient n x i) * boundaryJetCoefficient n y j *
          polarizedGreenMomentCoefficient primeDepthGeometricMoment
            (boundaryJetOrder i) (boundaryJetOrder j))) := by
  simp_rw [nativeSourceProjectiveBoundaryJetSynthesis_pairing]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient
    (boundaryJetOrder i) (boundaryJetOrder j)).const_mul _

/-- Polarized all-order limit for TWO independent coefficient families.
Mixed finite-step sectors vanish only after taking the proved kernel limit. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto (n : ℕ)
    (x y : Fin (2*n) → ℂ) :
    Tendsto (fun k => canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y)) atTop
      (nhds ((∑ i : Fin n, ∑ j : Fin n,
        conj (nativeSourceEvenBoundaryPhase n x i) * nativeSourceEvenBoundaryPhase n y j *
          (primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)) : ℂ)) +
        ∑ i : Fin n, ∑ j : Fin n,
        conj (nativeSourceOddBoundaryPhase n x i) * nativeSourceOddBoundaryPhase n y j *
          (primeDepthGeometricMoment ((i : ℕ)+(j : ℕ)+1) : ℂ))) := by
  simpa only [Fintype.sum_sum_type,boundaryJetOrder,boundaryJetCoefficient,
    Sum.elim_inl,Sum.elim_inr,polarizedGreenMomentCoefficient_even_even,
    polarizedGreenMomentCoefficient_odd_odd,polarizedGreenMomentCoefficient_even_odd,
    polarizedGreenMomentCoefficient_odd_even,mul_zero,Finset.sum_const_zero,
    add_zero,zero_add] using pairing_limit n x y

/-- The signed diagonal is EXACTLY a difference of the two actual component
energies. This identity occurs after the complete finite synthesis. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_energy (n k : ℕ) (x : Fin (2*n) → ℂ) :
    4 * (canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)).re =
    2 * (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
      ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re,Complex.sub_re,← Complex.ofReal_pow]
  ring

/-- All finite orders: the ACTUAL two-chirality energy difference converges
to the original raw limiting boundary, without any positivity premise. -/
theorem nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto (n : ℕ)
    (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => 2 *
      (‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2 -
       ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2)) atTop
      (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
  have h := (Complex.continuous_re.continuousAt.tendsto.comp (pairing_limit n x x)).const_mul (4 : ℝ)
  have hr (f : Fin n → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  have he : 4 * (∑ i : Fin n ⊕ Fin n, ∑ j : Fin n ⊕ Fin n,
      conj (boundaryJetCoefficient n x i) * boundaryJetCoefficient n x j *
        polarizedGreenMomentCoefficient primeDepthGeometricMoment
          (boundaryJetOrder i) (boundaryJetOrder j)).re =
      nativeSourceFiniteBoundaryEnergy (2*n) x := by
    simp only [Fintype.sum_sum_type,boundaryJetOrder,boundaryJetCoefficient,
      Sum.elim_inl,Sum.elim_inr,polarizedGreenMomentCoefficient_even_even,
      polarizedGreenMomentCoefficient_odd_odd,polarizedGreenMomentCoefficient_even_odd,
      polarizedGreenMomentCoefficient_odd_even,mul_zero,Finset.sum_const_zero,
      add_zero,zero_add,Complex.add_re]
    simp only [hr]
    rw [nativeSourceFiniteBoundaryEnergy_even_split]
    congr 1
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;>
      simp [Complex.mul_re,Complex.mul_im] <;> ring
  rw [he] at h
  simpa only [Function.comp_apply,nativeSourceProjectiveBoundaryJetSynthesis_energy] using h
end
end CarrySelfAdjointOperator
