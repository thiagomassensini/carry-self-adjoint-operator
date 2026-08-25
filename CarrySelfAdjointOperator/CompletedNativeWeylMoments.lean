import CarrySelfAdjointOperator.CompletedGreenMomentJets
import CarrySelfAdjointOperator.LogarithmicMomentHankel
import Mathlib.Tactic

/-!
# Weyl moments of the concrete completed native characteristic

This module removes the abstract coefficient sequence `phi` from the
completed-native branch of the construction.  Its coefficient in order `n`
is the actual order-`2n` Taylor coefficient at zero of
`completedNativeOperatorCharacteristic`.  The division-free identity

`q_G * Phi_G = -Phi_G'`

is then stated directly for this concrete sequence.  Center nonvanishing of
the completed characteristic proves that the resulting real moment sequence
is unique.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

noncomputable section

/-- The coefficient of `u^n` in the centered even characteristic
`F_G(z) = F_G(0) Phi_G(z^2)`, read directly as the order-`2n` Taylor
coefficient of the concrete completed native characteristic. -/
def completedNativeEvenCharacteristicCoefficient (n : ℕ) : ℂ :=
  completedGreenTaylorJet completedNativeOperatorCharacteristic (2 * n)

@[simp] theorem completedNativeEvenCharacteristicCoefficient_zero :
    completedNativeEvenCharacteristicCoefficient 0 =
      completedNativeOperatorCharacteristic 0 := by
  simp [completedNativeEvenCharacteristicCoefficient,
    completedGreenTaylorJet]

/-- The constant coefficient is nonzero by the proved center positivity of
the completed Genuine characteristic. -/
theorem completedNativeEvenCharacteristicCoefficient_zero_ne_zero :
    completedNativeEvenCharacteristicCoefficient 0 ≠ 0 := by
  rw [completedNativeEvenCharacteristicCoefficient_zero]
  exact completedNativeOperatorCharacteristic_zero_ne_zero

/-- Division-free coefficient form of
`q_G(u) Phi_G(u) = -Phi_G'(u)` for the actual completed native
characteristic.  The moments remain real because they feed the real Hankel
and Jacobi construction; only the characteristic coefficients are viewed in
`ℂ`, so no premature reality assertion about each Taylor coefficient is
needed. -/
def IsCompletedNativeLogDerivativeMomentSequence
    (moments : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    completedNativeEvenCharacteristicCoefficient 0 * (moments n : ℂ) +
        ∑ k ∈ Finset.range n,
          (moments k : ℂ) *
            completedNativeEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1))

/-- Full convolution form of the concrete completed-native identity.  This
is the coefficient statement consumed by the polarized Green recurrence. -/
theorem completedNativeLogDerivativeMoment_fullConvolution
    {moments : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (moments k : ℂ) *
          completedNativeEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1)) := by
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self]
  have h := hrel n
  rw [mul_comm] at h
  simpa [add_comm] using h

/-- The concrete completed Genuine characteristic has at most one real
logarithmic Weyl-moment sequence. -/
theorem IsCompletedNativeLogDerivativeMomentSequence.unique
    {moments moments' : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments') :
    moments = moments' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hsum :
          ∑ k ∈ Finset.range n,
              (moments k : ℂ) *
                completedNativeEvenCharacteristicCoefficient (n - k) =
            ∑ k ∈ Finset.range n,
              (moments' k : ℂ) *
                completedNativeEvenCharacteristicCoefficient (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      have hn :
          completedNativeEvenCharacteristicCoefficient 0 * (moments n : ℂ) =
            completedNativeEvenCharacteristicCoefficient 0 *
              (moments' n : ℂ) := by
        calc
          completedNativeEvenCharacteristicCoefficient 0 * (moments n : ℂ) =
              (completedNativeEvenCharacteristicCoefficient 0 *
                    (moments n : ℂ) +
                  ∑ k ∈ Finset.range n,
                    (moments k : ℂ) *
                      completedNativeEvenCharacteristicCoefficient (n - k)) -
                ∑ k ∈ Finset.range n,
                  (moments k : ℂ) *
                    completedNativeEvenCharacteristicCoefficient (n - k) := by
                      ring
          _ = -(((n + 1 : ℕ) : ℂ) *
                  completedNativeEvenCharacteristicCoefficient (n + 1)) -
                ∑ k ∈ Finset.range n,
                  (moments k : ℂ) *
                    completedNativeEvenCharacteristicCoefficient (n - k) := by
                      rw [hrel n]
          _ = -(((n + 1 : ℕ) : ℂ) *
                  completedNativeEvenCharacteristicCoefficient (n + 1)) -
                ∑ k ∈ Finset.range n,
                  (moments' k : ℂ) *
                    completedNativeEvenCharacteristicCoefficient (n - k) := by
                      rw [hsum]
          _ = (completedNativeEvenCharacteristicCoefficient 0 *
                    (moments' n : ℂ) +
                  ∑ k ∈ Finset.range n,
                    (moments' k : ℂ) *
                      completedNativeEvenCharacteristicCoefficient (n - k)) -
                ∑ k ∈ Finset.range n,
                  (moments' k : ℂ) *
                    completedNativeEvenCharacteristicCoefficient (n - k) := by
                      rw [hrel' n]
          _ = completedNativeEvenCharacteristicCoefficient 0 *
              (moments' n : ℂ) := by ring
      have hcast : (moments n : ℂ) = (moments' n : ℂ) :=
        mul_left_cancel₀
          completedNativeEvenCharacteristicCoefficient_zero_ne_zero hn
      exact_mod_cast hcast

/-- Pointwise concrete Genuine-moment uniqueness. -/
theorem completedNativeLogDerivativeMoment_eq
    {moments moments' : ℕ → ℝ}
    (hrel : IsCompletedNativeLogDerivativeMomentSequence moments)
    (hrel' : IsCompletedNativeLogDerivativeMomentSequence moments')
    (n : ℕ) :
    moments n = moments' n := by
  rw [hrel.unique hrel']

end

end CarrySelfAdjointOperator
