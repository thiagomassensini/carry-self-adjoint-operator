import CarrySelfAdjointOperator.CompletedNativeLogDerivativeTriangularTransport
import CarrySelfAdjointOperator.CompletedGreenMomentJets
import Mathlib.Tactic

/-!
# Vector-valued triangular transport for completed Green jets

The original native self-adjoint construction performs the scalar division
`q Phi = -Phi'` before forming the two Hankel towers.  The scalar finite
Toeplitz transport is already packaged in
`CompletedNativeLogDerivativeTriangularTransport`.

This file records the corresponding vector-valued operation.  It deliberately
does not assert the remaining analytic product identity for a concrete Green
state.  Instead it isolates that identity as an explicit convolution premise
and proves that, once supplied, every finite jet prefix is transported by the
same completed-native triangular matrix.

This is the algebraic bridge needed before comparing a pre-normalization Green
Gram with the Hankel Gram of the normalized moment jets.
-/

open scoped BigOperators Matrix

namespace CarrySelfAdjointOperator

noncomputable section

/-- Apply the completed-native lower-triangular scalar transport to a finite
vector-valued jet family. -/
def completedNativeGreenVectorTriangularAct
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (N : ℕ) (jet : Fin N → E) : Fin N → E :=
  fun i => ∑ j : Fin N,
    completedNativeLogDerivativeTriangularMatrix N i j • jet j

/-- All-order coefficient form of a vector product by the completed even
characteristic.  This is the vector analogue of the scalar convolution used
in `q Phi = -Phi'`.

The intended concrete specialization is the identity obtained from
`rawState = F • normalizedState` (up to the canonical `sqrt 2` factor), after
taking factorial-normalized Taylor coefficients. -/
def HasCompletedNativeGreenVectorTriangularConvolution
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (raw normalized : ℕ → E) : Prop :=
  ∀ n : ℕ,
    (∑ j ∈ Finset.range (n + 1),
      completedNativeEvenCharacteristicCoefficient (n - j) • normalized j) =
      raw n

/-- The all-order vector convolution is exactly the finite triangular matrix
transport on every prefix. -/
theorem completedNativeGreenVectorTriangularAct_eq_of_convolution
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {raw normalized : ℕ → E}
    (hconv : HasCompletedNativeGreenVectorTriangularConvolution raw normalized)
    (N : ℕ) :
    completedNativeGreenVectorTriangularAct N
        (fun j : Fin N => normalized j.val) =
      fun i : Fin N => raw i.val := by
  funext i
  let f : ℕ → E := fun j =>
    if hj : j ≤ i.val then
      completedNativeEvenCharacteristicCoefficient (i.val - j) • normalized j
    else 0
  change (∑ j : Fin N, f j.val) = raw i.val
  rw [Fin.sum_univ_eq_sum_range]
  have hsum :
      (∑ j ∈ Finset.range (i.val + 1), f j) =
        ∑ j ∈ Finset.range N, f j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hij : i.val < j := by
      have hj' : i.val + 1 ≤ j := by
        simpa only [Finset.mem_range, not_lt] using hj
      omega
    simp [f, Nat.not_le.mpr hij]
  rw [← hsum]
  calc
    (∑ j ∈ Finset.range (i.val + 1), f j) =
        ∑ j ∈ Finset.range (i.val + 1),
          completedNativeEvenCharacteristicCoefficient (i.val - j) •
            normalized j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≤ i.val :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp [f, hji]
    _ = raw i.val := hconv i.val

/-- The concrete Green Taylor-jet family, exposed as a sequence so the final
analytic specialization of the triangular transport has a small interface. -/
def completedGreenTaylorJetSequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (state : ℂ → E) : ℕ → E :=
  fun n => completedGreenTaylorJet state n

/-- Finite-prefix form specialized to Taylor jets.  The only premise left is
the actual vector product/convolution identity for the chosen raw and
normalized Green states. -/
theorem completedGreenTaylorJet_prefix_triangular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {rawState normalizedState : ℂ → E}
    (hconv : HasCompletedNativeGreenVectorTriangularConvolution
      (completedGreenTaylorJetSequence rawState)
      (completedGreenTaylorJetSequence normalizedState))
    (N : ℕ) :
    completedNativeGreenVectorTriangularAct N
        (fun j : Fin N => completedGreenTaylorJet normalizedState j.val) =
      fun i : Fin N => completedGreenTaylorJet rawState i.val := by
  exact completedNativeGreenVectorTriangularAct_eq_of_convolution hconv N

end

end CarrySelfAdjointOperator
