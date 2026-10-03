import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.CompletedNativeGeometryHeightProvenance

namespace CarrySelfAdjointOperator

open scoped BigOperators
open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-!
# Finite seeded-clock atlas versus the infinite Green/Stieltjes carrier

This module records a conditional no-go at the exact source boundary.  The
finite seeded-clock atlas is not compared with a raw camera Gram: its first
column is first transported to the canonical polarized Green moment
coefficient.  The finite atomic characteristic then forces a constant
coefficient recurrence.  Under the already-defined strict Stieltjes
positivity certificate, the parity Green jet is linearly independent, so no
nonzero finite recurrence can exist.

The conclusion is deliberately conditional on the carrier-honest positivity
certificate and on the proposed corrected native transport.  It therefore
names the incompatible seam instead of replacing the native carrier by a
positive proxy.
-/

def canonicalParityIndexEquiv : ℕ ≃ ℕ ⊕ ℕ where
  toFun n := if Even n then Sum.inl (n / 2) else Sum.inr ((n - 1) / 2)
  invFun s := match s with
    | Sum.inl n => 2 * n
    | Sum.inr n => 2 * n + 1
  left_inv n := by
    rcases Nat.even_or_odd n with hn | hn
    · rcases hn with ⟨k, rfl⟩
      simp
      omega
    · rcases hn with ⟨k, rfl⟩
      simp
  right_inv s := by
    cases s with
    | inl n => simp
    | inr n => simp

def canonicalParityScalarMoment (moments : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Even n then moments (n / 2) else 0

def canonicalParityJet
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (n : ℕ) :
    CanonicalCompletedNativeStieltjesCarrier hpos :=
  canonicalCompletedNativeStieltjesJet hpos (canonicalParityIndexEquiv n)

theorem canonicalParityJet_inner
    (hpos : CanonicalCompletedNativeStieltjesPositivity) (n m : ℕ) :
    inner ℝ (canonicalParityJet hpos n) (canonicalParityJet hpos m) =
      canonicalParityScalarMoment canonicalCompletedNativeLogDerivativeMoment
        (n + m) := by
  rcases Nat.even_or_odd' n with ⟨i, rfl | rfl⟩
  · have hi : Even (2 * i) := ⟨i, by omega⟩
    have hdivi : (2 * i) / 2 = i := by omega
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have hj : Even (2 * j) := ⟨j, by omega⟩
      have hdivj : (2 * j) / 2 = j := by omega
      have hsum : Even (2 * i + 2 * j) := ⟨i + j, by omega⟩
      have hsumdiv : (2 * i + 2 * j) / 2 = i + j := by omega
      have h := (canonicalCompletedNativeStieltjesJet_momentKernel hpos
        (Sum.inl i) (Sum.inl j)).symm
      simpa [canonicalParityJet, canonicalParityIndexEquiv, hi, hj, hdivi, hdivj,
        hsum, hsumdiv, canonicalParityScalarMoment, greenWronskianMomentKernel,
        Matrix.gram] using h
    · have hj : Odd (2 * j + 1) := ⟨j, rfl⟩
      have hdivj : (2 * j + 1 - 1) / 2 = j := by omega
      have hj' : ¬ Even (2 * j + 1) := by
        rintro ⟨k, hk⟩
        omega
      have hsum : ¬ Even (2 * i + (2 * j + 1)) := by
        rintro ⟨k, hk⟩
        omega
      have h := (canonicalCompletedNativeStieltjesJet_momentKernel hpos
        (Sum.inl i) (Sum.inr j)).symm
      simpa [canonicalParityJet, canonicalParityIndexEquiv, hi, hj', hdivi, hdivj,
        hsum, canonicalParityScalarMoment, greenWronskianMomentKernel,
        Matrix.gram] using h
  · have hi : Odd (2 * i + 1) := ⟨i, rfl⟩
    have hdivi : (2 * i + 1 - 1) / 2 = i := by omega
    have hi' : ¬ Even (2 * i + 1) := by
      rintro ⟨k, hk⟩
      omega
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have hj : Even (2 * j) := ⟨j, by omega⟩
      have hdivj : (2 * j) / 2 = j := by omega
      have hsum : ¬ Even (2 * i + 1 + 2 * j) := by
        rintro ⟨k, hk⟩
        omega
      have h := (canonicalCompletedNativeStieltjesJet_momentKernel hpos
        (Sum.inr i) (Sum.inl j)).symm
      simpa [canonicalParityJet, canonicalParityIndexEquiv, hi', hj, hdivi, hdivj,
        hsum, canonicalParityScalarMoment, greenWronskianMomentKernel,
        Matrix.gram] using h
    · have hj : Odd (2 * j + 1) := ⟨j, rfl⟩
      have hdivj : (2 * j + 1 - 1) / 2 = j := by omega
      have hj' : ¬ Even (2 * j + 1) := by
        rintro ⟨k, hk⟩
        omega
      have hsum : Even (2 * i + 1 + (2 * j + 1)) := ⟨i + j + 1, by omega⟩
      have hsumdiv : (2 * i + 1 + (2 * j + 1)) / 2 = i + j + 1 := by omega
      have h := (canonicalCompletedNativeStieltjesJet_momentKernel hpos
        (Sum.inr i) (Sum.inr j)).symm
      simpa [canonicalParityJet, canonicalParityIndexEquiv, hi', hj', hdivi, hdivj,
        hsum, hsumdiv, canonicalParityScalarMoment, greenWronskianMomentKernel,
        Matrix.gram] using h

theorem canonicalParityJet_linearIndependent
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    LinearIndependent ℝ (canonicalParityJet hpos) := by
  let A := CanonicalCompletedNativeEvenMomentHilbertSpace hpos
  let B := CanonicalCompletedNativeOddMomentHilbertSpace hpos
  let ve : ℕ → A :=
    momentHilbertBasisVector canonicalCompletedNativeLogDerivativeMoment 0
      (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos)
  let vo : ℕ → B :=
    momentHilbertBasisVector canonicalCompletedNativeLogDerivativeMoment 1
      (canonicalCompletedNativeOddInfiniteHankelPosDef hpos)
  have hve : LinearIndependent ℝ ve := by
    exact momentHilbertBasisVector_linearIndependent
      canonicalCompletedNativeLogDerivativeMoment 0
      (canonicalCompletedNativeEvenInfiniteHankelPosDef hpos)
  have hvo : LinearIndependent ℝ vo := by
    exact momentHilbertBasisVector_linearIndependent
      canonicalCompletedNativeLogDerivativeMoment 1
      (canonicalCompletedNativeOddInfiniteHankelPosDef hpos)
  let vprod : (ℕ ⊕ ℕ) → A × B :=
    Sum.elim (fun n => LinearMap.inl ℝ A B (ve n))
      (fun n => LinearMap.inr ℝ A B (vo n))
  have hvprod : LinearIndependent ℝ vprod := by
    exact linearIndependent_inl_union_inr' hve hvo
  let f : A × B →ₗ[ℝ] WithLp 2 (A × B) :=
    (WithLp.linearEquiv 2 ℝ (A × B)).symm.toLinearMap
  have hf : LinearMap.ker f = ⊥ := by
    simp [f]
  have hmapped := hvprod.map' f hf
  have hfamily : f ∘ vprod = canonicalCompletedNativeStieltjesJet hpos := by
    funext s
    cases s with
    | inl n =>
        simp [f, vprod, ve, canonicalCompletedNativeStieltjesJet,
          WithLp.coe_symm_linearEquiv]
    | inr n =>
        simp [f, vprod, vo, canonicalCompletedNativeStieltjesJet,
          WithLp.coe_symm_linearEquiv]
  have hcanonical :
      LinearIndependent ℝ (canonicalCompletedNativeStieltjesJet hpos) := by
    rw [← hfamily]
    exact hmapped
  have hcomp := hcanonical.comp canonicalParityIndexEquiv
    canonicalParityIndexEquiv.injective
  change LinearIndependent ℝ
    (canonicalCompletedNativeStieltjesJet hpos ∘ canonicalParityIndexEquiv)
  exact hcomp

theorem canonicalNative_no_finite_real_recurrence
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    (d : ℕ) (coeff : Fin (d + 1) → ℝ)
    (hlead : coeff ⟨d, Nat.lt_succ_self d⟩ ≠ 0)
    (hrec : ∀ n : ℕ,
      ∑ r : Fin (d + 1),
        coeff r * canonicalParityScalarMoment
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) = 0) :
    False := by
  let w : CanonicalCompletedNativeStieltjesCarrier hpos :=
    ∑ r : Fin (d + 1), coeff r • canonicalParityJet hpos (r : ℕ)
  have hworth (n : ℕ) : inner ℝ (canonicalParityJet hpos n) w = 0 := by
    change inner ℝ (canonicalParityJet hpos n)
      (∑ r : Fin (d + 1), coeff r • canonicalParityJet hpos (r : ℕ)) = 0
    rw [inner_sum]
    simp_rw [inner_smul_right]
    rw [Finset.sum_congr rfl]
    · exact hrec n
    · intro r hr
      rw [canonicalParityJet_inner]
  have hww : inner ℝ w w = 0 := by
    change inner ℝ
      (∑ r : Fin (d + 1), coeff r • canonicalParityJet hpos (r : ℕ)) w = 0
    rw [sum_inner]
    simp_rw [inner_smul_left]
    simp [hworth]
  have hwzero : w = 0 := inner_self_eq_zero.mp hww
  have hcoeffzero : ∀ r : Fin (d + 1), coeff r = 0 := by
    intro r
    have hliFin : LinearIndependent ℝ
        (fun s : Fin (d + 1) => canonicalParityJet hpos (s : ℕ)) :=
      (canonicalParityJet_linearIndependent hpos).comp
        (fun s : Fin (d + 1) => (s : ℕ)) Fin.val_injective
    have hli := (linearIndependent_iff'.mp hliFin)
      (Finset.univ : Finset (Fin (d + 1)))
      (fun s => coeff s)
      (by simpa [w] using hwzero)
    exact hli r (Finset.mem_univ r)
  exact hlead (hcoeffzero ⟨d, Nat.lt_succ_self d⟩)

theorem canonicalPolarizedFirstColumn_re
    (n : ℕ) :
    (polarizedGreenMomentCoefficient
      canonicalCompletedNativeLogDerivativeMoment n 0).re =
      canonicalParityScalarMoment canonicalCompletedNativeLogDerivativeMoment n := by
  by_cases h : Even n <;>
    simp [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient,
      canonicalParityScalarMoment, h]

theorem canonicalPolarizedFirstColumn_im
    (n : ℕ) :
    (polarizedGreenMomentCoefficient
      canonicalCompletedNativeLogDerivativeMoment n 0).im = 0 := by
  by_cases h : Even n <;>
    simp [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient, h]

theorem canonicalNative_no_finite_complex_recurrence
    (hpos : CanonicalCompletedNativeStieltjesPositivity)
    (d : ℕ) (coeff : Fin (d + 1) → ℂ)
    (hlead : coeff ⟨d, Nat.lt_succ_self d⟩ ≠ 0)
    (hrec : ∀ n : ℕ,
      ∑ r : Fin (d + 1),
        coeff r * polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0 = 0) :
    False := by
  have hrec_re : ∀ n : ℕ,
      ∑ r : Fin (d + 1),
        (coeff r).re * canonicalParityScalarMoment
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) = 0 := by
    intro n
    have h := congrArg Complex.re (hrec n)
    have hsum :
        (∑ r : Fin (d + 1),
          coeff r * polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0).re =
          ∑ r : Fin (d + 1),
            (coeff r * polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0).re := by
      exact map_sum (Complex.reCLM)
        (fun r : Fin (d + 1) => coeff r * polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0)
        (Finset.univ : Finset (Fin (d + 1)))
    rw [hsum] at h
    simpa [Complex.mul_re, canonicalPolarizedFirstColumn_re,
      canonicalPolarizedFirstColumn_im] using h
  have hrec_im : ∀ n : ℕ,
      ∑ r : Fin (d + 1),
        (coeff r).im * canonicalParityScalarMoment
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) = 0 := by
    intro n
    have h := congrArg Complex.im (hrec n)
    have hsum :
        (∑ r : Fin (d + 1),
          coeff r * polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0).im =
          ∑ r : Fin (d + 1),
            (coeff r * polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0).im := by
      exact map_sum (Complex.imCLM)
        (fun r : Fin (d + 1) => coeff r * polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0)
        (Finset.univ : Finset (Fin (d + 1)))
    rw [hsum] at h
    simpa [Complex.mul_im, canonicalPolarizedFirstColumn_re,
      canonicalPolarizedFirstColumn_im] using h
  by_cases hre : (coeff ⟨d, Nat.lt_succ_self d⟩).re ≠ 0
  · exact canonicalNative_no_finite_real_recurrence hpos d
      (fun r => (coeff r).re) hre hrec_re
  · have him : (coeff ⟨d, Nat.lt_succ_self d⟩).im ≠ 0 := by
      intro him
      apply hlead
      apply Complex.ext
      · exact not_ne_iff.mp hre
      · exact him
    exact canonicalNative_no_finite_real_recurrence hpos d
      (fun r => (coeff r).im) him hrec_im

theorem canonicalC2Geometry_seededClockAtlas_noGo_of_stieltjesPositivity
    {ι : Type*} [Fintype ι]
    (M cutoff : ℕ) (block : ι → C3TraceDynamics.SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block)
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    False := by
  let p : Polynomial ℂ :=
    canonicalC2Geometry_seededClockAtlasCharacteristic block
  have hmonic : p.Monic := by
    unfold p canonicalC2Geometry_seededClockAtlasCharacteristic
    apply Polynomial.monic_prod_of_monic
    intro k hk
    unfold canonicalC2Geometry_seededClockBlockCharacteristic
    apply Polynomial.monic_prod_of_monic
    intro i hi
    exact Polynomial.monic_X_sub_C _
  let d : ℕ := p.natDegree
  let coeff : Fin (d + 1) → ℂ := fun r => p.coeff (r : ℕ)
  have hlead : coeff ⟨d, Nat.lt_succ_self d⟩ ≠ 0 := by
    dsimp [coeff, d]
    rw [hmonic.leadingCoeff]
    norm_num
  have hrec : ∀ n : ℕ,
      ∑ r : Fin (d + 1),
        coeff r * polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0 = 0 := by
    intro n
    change ∑ r : Fin (d + 1),
      p.coeff (r : ℕ) * polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0 = 0
    calc
      ∑ r : Fin (d + 1),
          p.coeff (r : ℕ) * polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment (n + (r : ℕ)) 0 =
          ∑ i ∈ Finset.range (d + 1),
            p.coeff i * polarizedGreenMomentCoefficient
              canonicalCompletedNativeLogDerivativeMoment (n + i) 0 := by
        exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
          p.coeff i * polarizedGreenMomentCoefficient
            canonicalCompletedNativeLogDerivativeMoment (n + i) 0) (d + 1)
      _ = 0 := by
        exact canonicalC2Geometry_seededClockAtlas_canonicalTarget_recurrence
          M cutoff block htransport n
  exact canonicalNative_no_finite_complex_recurrence hpos d coeff hlead hrec

theorem canonicalC2Geometry_seededClockBoundaryResidual_not_identically_zero
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → C3TraceDynamics.SeededClockBlock)
    (hpos : CanonicalCompletedNativeStieltjesPositivity) :
    ¬ (∀ p : ℕ,
      canonicalC2Geometry_seededClockBoundaryResidual M block p = 0) := by
  intro hzero
  have htransport :=
    (canonicalC2Geometry_seededClockBoundaryResidual_zero_iff_correctedTransport
      M block).mp hzero
  exact canonicalC2Geometry_seededClockAtlas_noGo_of_stieltjesPositivity
    M 0 block htransport hpos

theorem canonicalC2Geometry_seededClockAtlas_noGo_of_greenMomentKernel_and_incidenceTransport
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {base radius : ℕ}
    {jet : (ℕ ⊕ ℕ) → E}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (hgreen :
      IsGreenWronskianMomentKernelGramRepresentation
        canonicalCompletedNativeLogDerivativeMoment jet)
    (transport : BR2BracketIncidenceJetTransport base radius jet)
    (M cutoff N : ℕ)
    (block : ι → C3TraceDynamics.SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block) :
    False := by
  obtain ⟨hpos, _⟩ :=
    nativeGeometry_to_finiteHeight_chain_of_greenMomentKernel_and_incidenceTransport
      hbase hradius hgreen transport cutoff N
  exact canonicalC2Geometry_seededClockAtlas_noGo_of_stieltjesPositivity
    M cutoff block htransport hpos

end
end CarrySelfAdjointOperator
