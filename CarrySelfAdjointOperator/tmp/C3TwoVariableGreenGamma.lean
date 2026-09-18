import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity

/-!
# Polarized C3 Green identity and the division-free gamma interface

This file isolates two algebraic steps.

1.  The raw Genuine C3 port is kept holomorphic in its parameter.  Its Green
    pairing at two independent parameters factors as the difference of the
    exact C3 eigenvalues times the Gram pairing of the horizontal gradients.
2.  An abstract division-free Wronskian identity implies the usual normalized
    response kernel wherever the scalar boundary value is nonzero.

The first statement is concrete and finite.  The second makes explicit the
single operator-domain input still required to identify a scalar response
with a gamma-field Gram kernel.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Raw holomorphic Green port for an arbitrary camera `p`.  This version is
purely geometric and uses the already telescoped block gradient. -/
def finiteCpHolomorphicGreenBoundaryPair (p M : ℕ) (s : ℂ) :
    FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M :=
  (WithLp.toLp 2 (fun n : Fin M ↦ cpBlockGradient p s n),
    WithLp.toLp 2 (fun n : Fin M ↦ positiveDirichletGradient s n))

@[simp] theorem finiteCpHolomorphicGreenBoundaryPair_fst_apply
    (p M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteCpHolomorphicGreenBoundaryPair p M s).1 n =
      cpBlockGradient p s n :=
  rfl

@[simp] theorem finiteCpHolomorphicGreenBoundaryPair_snd_apply
    (p M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteCpHolomorphicGreenBoundaryPair p M s).2 n =
      positiveDirichletGradient s n :=
  rfl

/-- Exact two-parameter Green polarization for every natural camera. -/
theorem greenForm_finiteCpHolomorphicGreenBoundaryPair
    (p M : ℕ) (r s : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteCpHolomorphicGreenBoundaryPair p M r)
        (finiteCpHolomorphicGreenBoundaryPair p M s) =
      (natDirichletTerm s p -
          (starRingEnd ℂ) (natDirichletTerm r p)) *
        ∑ n ∈ Finset.range M,
          (starRingEnd ℂ) (positiveDirichletGradient r n) *
            positiveDirichletGradient s n := by
  rw [greenForm, PiLp.inner_apply, PiLp.inner_apply,
    ← Finset.sum_sub_distrib]
  simp only [finiteCpHolomorphicGreenBoundaryPair_fst_apply,
    finiteCpHolomorphicGreenBoundaryPair_snd_apply,
    RCLike.inner_apply']
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  simp only [hlt, dite_true]
  rw [cpBlockGradient_eq_eigenvalue_mul,
    cpBlockGradient_eq_eigenvalue_mul]
  simp only [map_mul]
  ring

/-- On a prime camera, the raw geometric port is literally the port obtained
from the normalized differentiated Genuine residual. -/
theorem finiteCpHolomorphicGenuineGreenBoundaryPair_eq_blockPair
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (WithLp.toLp 2 (fun n : Fin M ↦ cpGenuineGreenGradient p s n),
      WithLp.toLp 2 (fun n : Fin M ↦ positiveDirichletGradient s n)) =
        finiteCpHolomorphicGreenBoundaryPair p M s := by
  apply Prod.ext
  · ext n
    exact cpGenuineGreenGradient_eq_cpBlockGradient p hp s n
  · rfl

/-- The undressed C3 Green port.  Unlike the radial phase-normalized port, this
pair retains the holomorphic eigenvalue `3 ^ (-s)` in its first coordinate. -/
def finiteC3HolomorphicGenuineGreenBoundaryPair (M : ℕ) (s : ℂ) :
    FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M :=
  (WithLp.toLp 2 (fun n : Fin M ↦ cpGenuineGreenGradient 3 s n),
    WithLp.toLp 2 (fun n : Fin M ↦ positiveDirichletGradient s n))

@[simp] theorem finiteC3HolomorphicGenuineGreenBoundaryPair_fst_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3HolomorphicGenuineGreenBoundaryPair M s).1 n =
      cpGenuineGreenGradient 3 s n :=
  rfl

@[simp] theorem finiteC3HolomorphicGenuineGreenBoundaryPair_snd_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3HolomorphicGenuineGreenBoundaryPair M s).2 n =
      positiveDirichletGradient s n :=
  rfl

/-- Exact two-parameter polarization of the finite C3 Green form. -/
theorem greenForm_finiteC3HolomorphicGenuineGreenBoundaryPair
    (M : ℕ) (r s : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteC3HolomorphicGenuineGreenBoundaryPair M r)
        (finiteC3HolomorphicGenuineGreenBoundaryPair M s) =
      (natDirichletTerm s 3 -
          (starRingEnd ℂ) (natDirichletTerm r 3)) *
        ∑ n ∈ Finset.range M,
          (starRingEnd ℂ) (positiveDirichletGradient r n) *
            positiveDirichletGradient s n := by
  rw [greenForm, PiLp.inner_apply, PiLp.inner_apply,
    ← Finset.sum_sub_distrib]
  simp only [finiteC3HolomorphicGenuineGreenBoundaryPair_fst_apply,
    finiteC3HolomorphicGenuineGreenBoundaryPair_snd_apply,
    RCLike.inner_apply']
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  simp only [hlt, dite_true]
  rw [cpGenuineGreenGradient_eq_cpBlockGradient 3 (by norm_num),
    cpGenuineGreenGradient_eq_cpBlockGradient 3 (by norm_num),
    cpBlockGradient_eq_eigenvalue_mul,
    cpBlockGradient_eq_eigenvalue_mul]
  simp only [map_mul]
  ring

/-- Division-free scalar Green numerator attached to two boundary traces. -/
def scalarGreenWronskian (F Psi : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Psi z * (starRingEnd ℂ) (F w) -
    F z * (starRingEnd ℂ) (Psi w)

/-- Scalar boundary response.  The sign is left in `Psi`; for a jet one uses
`Psi = -F'`. -/
def scalarBoundaryResponse (F Psi : ℂ → ℂ) (z : ℂ) : ℂ :=
  Psi z / F z

/-- Purely algebraic passage from the division-free Wronskian to the divided
two-variable response kernel. -/
theorem scalarBoundaryResponse_sub_star_div
    (F Psi : ℂ → ℂ) (z w : ℂ)
    (hz : F z ≠ 0) (hw : F w ≠ 0) (hzw : z ≠ (starRingEnd ℂ) w) :
    (scalarBoundaryResponse F Psi z -
          (starRingEnd ℂ) (scalarBoundaryResponse F Psi w)) /
        (z - (starRingEnd ℂ) w) =
      scalarGreenWronskian F Psi z w /
        ((z - (starRingEnd ℂ) w) * F z *
          (starRingEnd ℂ) (F w)) := by
  unfold scalarBoundaryResponse scalarGreenWronskian
  have hwstar : (starRingEnd ℂ) (F w) ≠ 0 := by
    intro hzero
    apply hw
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  rw [map_div₀]
  field_simp [hz, hwstar, hzw]

/-- Minimal gamma-field interface.  Once an operator-domain Green identity
identifies the division-free scalar Wronskian with this Gram numerator, the
normalized response kernel follows without any additional analytic step. -/
theorem scalarBoundaryResponse_kernel_eq_gram_of_greenWronskian
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F Psi : ℂ → ℂ) (f : ℂ → H) (z w : ℂ)
    (hz : F z ≠ 0) (hw : F w ≠ 0) (hzw : z ≠ (starRingEnd ℂ) w)
    (hgreen :
      scalarGreenWronskian F Psi z w =
        (z - (starRingEnd ℂ) w) * inner ℂ (f w) (f z)) :
    (scalarBoundaryResponse F Psi z -
          (starRingEnd ℂ) (scalarBoundaryResponse F Psi w)) /
        (z - (starRingEnd ℂ) w) =
      inner ℂ ((F w)⁻¹ • f w) ((F z)⁻¹ • f z) := by
  rw [scalarBoundaryResponse_sub_star_div F Psi z w hz hw hzw, hgreen]
  have hwstar : (starRingEnd ℂ) (F w) ≠ 0 := by
    intro hzero
    apply hw
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  simp only [inner_smul_left, inner_smul_right, map_inv₀]
  field_simp [hz, hwstar, hzw]

end

end NativeCarryC3Crosswalk

#print axioms NativeCarryC3Crosswalk.greenForm_finiteCpHolomorphicGreenBoundaryPair
#print axioms NativeCarryC3Crosswalk.greenForm_finiteC3HolomorphicGenuineGreenBoundaryPair
#print axioms NativeCarryC3Crosswalk.scalarBoundaryResponse_kernel_eq_gram_of_greenWronskian
