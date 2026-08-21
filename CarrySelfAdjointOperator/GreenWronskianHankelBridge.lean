import CarrySelfAdjointOperator.MomentGramPositivity
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Green--Wronskian coefficient kernel to Hankel positivity

For an even completed characteristic

`F(z) = F(0) * Phi(z^2)`

write

`q(u) = -Phi'(u) / Phi(u) = sum h_n u^n`

and

`m(z) = -F'(z) / F(z) = 2 * z * q(z^2)`.

Consequently the normalized polarized response

`(1/2) * (m(z) - conj (m(w))) / (z - conj w)`

has a parity-split coefficient kernel: the even/even block is
`h_(i+j)`, the odd/odd block is `h_(i+j+1)`, and the mixed blocks vanish.

This file formalizes the finite-dimensional consequence of that coefficient
identity.  If the normalized completed Green--Wronskian kernel is realized as
one Hilbert-space Gram kernel, then both Hankel matrices used by the native
Jacobi construction are positive simultaneously at every order.  Strict
positivity requires only linear independence of the corresponding even and
odd Green jets.

The analytic construction of the actual completed Green jet is deliberately
kept separate: the raw C3 Green--gamma kernel has the required positivity but
uses the local camera eigenvalue, while the completed scalar response still
requires the provenance/log-jet/completion scalarization already isolated in
the repository.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Parity-split coefficient kernel forced by an odd response
`m(z) = 2 z * sum_n h_n z^(2n)`, after the fixed normalization by `1/2`.
The left summand indexes even Green jets and the right summand indexes odd
Green jets. -/
def greenWronskianMomentKernel (moments : ℕ → ℝ) :
    Matrix (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) ℝ
  | Sum.inl i, Sum.inl j => moments (i + j)
  | Sum.inr i, Sum.inr j => moments (i + j + 1)
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- One normalized Green jet family realizes the full parity-split moment
kernel.  This is the single coefficient-level interface expected from the
completed two-variable Green--Wronskian/gamma identity. -/
def IsGreenWronskianMomentKernelGramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    greenWronskianMomentKernel moments i j = Matrix.gram ℝ jet i j

/-- The even Green jets realize the unshifted Hankel moment kernel. -/
theorem greenWronskianMomentKernel_even_momentGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    IsMomentGramRepresentation moments (fun n : ℕ => jet (Sum.inl n)) := by
  intro i j
  have h := hrep (Sum.inl i) (Sum.inl j)
  simpa [greenWronskianMomentKernel, Matrix.gram] using h

/-- The odd Green jets realize the shifted Hankel moment kernel. -/
theorem greenWronskianMomentKernel_odd_shiftedMomentGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet) :
    IsShiftedMomentGramRepresentation moments
      (fun n : ℕ => jet (Sum.inr n)) := by
  intro i j
  have h := hrep (Sum.inr i) (Sum.inr j)
  simpa [greenWronskianMomentKernel, Matrix.gram] using h

/-- The same Green coefficient identity forces the even and odd jet sectors to
be orthogonal.  This is the coefficient-level form of the parity split in the
polarized Wronskian kernel. -/
theorem greenWronskianMomentKernel_even_odd_orthogonal
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (i j : ℕ) :
    Matrix.gram ℝ jet (Sum.inl i) (Sum.inr j) = 0 := by
  have h := hrep (Sum.inl i) (Sum.inr j)
  simpa [greenWronskianMomentKernel] using h.symm

/-- A single positive Green--Wronskian coefficient kernel proves positivity of
both native Hankel sections, at every finite order, with no separate positivity
hypothesis for either matrix. -/
theorem hankelPair_posSemidef_of_greenWronskianMomentKernel
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧
      (shiftedHankel moments N).PosSemidef := by
  constructor
  · exact hankelGram_posSemidef_of_gramRepresentation
      (greenWronskianMomentKernel_even_momentGram hrep) N
  · exact shiftedHankel_posSemidef_of_gramRepresentation
      (greenWronskianMomentKernel_odd_shiftedMomentGram hrep) N

/-- Linear independence of the even and odd Green-jet prefixes upgrades the
same one-kernel certificate to strict positivity of both Hankel sections. -/
theorem hankelPair_posDef_of_greenWronskianMomentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ)
    (heven : LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ
      (fun i : Fin N => jet (Sum.inr (i : ℕ)))) :
    (hankelGram moments N).PosDef ∧
      (shiftedHankel moments N).PosDef := by
  constructor
  · exact hankelGram_posDef_of_gramRepresentation
      (greenWronskianMomentKernel_even_momentGram hrep) N heven
  · exact shiftedHankel_posDef_of_gramRepresentation
      (greenWronskianMomentKernel_odd_shiftedMomentGram hrep) N hodd

end

end CarrySelfAdjointOperator
