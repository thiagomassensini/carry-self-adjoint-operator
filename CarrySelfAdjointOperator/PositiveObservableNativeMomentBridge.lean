import CarrySelfAdjointOperator.PositiveObservableParityKernel
import CarrySelfAdjointOperator.CompletedNativeHPGateAudit

/-!
# From a constructed positive-observable kernel to native moments

The Hilbert state and both coefficient Grams are constructed in
`PositiveObservableParityKernel`. This module connects those actual Grams to
the native HP interface via the existing uniqueness theorem for the concrete
completed characteristic. The remaining readout equality is exposed as one
explicit real convolution defect. No vanishing of that defect is asserted
for an unspecified geometric operator.
-/

namespace CarrySelfAdjointOperator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The two coefficient channels realize the complete parity kernel of the
constructed positive observable, before any native identification. -/
theorem positiveObservableParityJet_momentKernel
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H) :
    IsGreenWronskianMomentKernelGramRepresentation
      (positiveObservableMoment S u) (positiveObservableParityJet S u) := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          exact (inner_positiveObservableParityJet_even S hS u i j).symm
      | inr j =>
          exact (inner_positiveObservableParityJet_even_odd S u i j).symm
  | inr i =>
      cases j with
      | inl j =>
          change 0 = inner ℝ (positiveObservableParityJet S u (Sum.inr i))
            (positiveObservableParityJet S u (Sum.inl j))
          rw [real_inner_comm, inner_positiveObservableParityJet_even_odd]
      | inr j =>
          exact (inner_positiveObservableParityJet_odd S hS u i j).symm

/-- Literal difference between the geometric moments and the division-free
convolution required by the completed-native characteristic. -/
def positiveObservableNativeConvolutionDefect
    (S : H →L[ℝ] H) (u : H) (n : ℕ) : ℝ :=
  completedNativeRealEvenCharacteristicCoefficient 0 * positiveObservableMoment S u n +
    ∑ k ∈ Finset.range n,
      positiveObservableMoment S u k * completedNativeRealEvenCharacteristicCoefficient (n - k) +
    ((n + 1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n + 1)

/-- An exact real-valued formulation of the remaining readout obligation. -/
theorem positiveObservable_isNativeMomentSequence_iff_defect_zero
    (S : H →L[ℝ] H) (u : H) :
    IsCompletedNativeLogDerivativeMomentSequence (positiveObservableMoment S u) ↔
      ∀ n, positiveObservableNativeConvolutionDefect S u n = 0 := by
  unfold IsCompletedNativeLogDerivativeMomentSequence positiveObservableNativeConvolutionDefect
  simp_rw [completedNativeEvenCharacteristicCoefficient_eq_real]
  constructor
  · intro h n
    have hn := h n
    have hr :
        completedNativeRealEvenCharacteristicCoefficient 0 * positiveObservableMoment S u n +
          ∑ k ∈ Finset.range n,
            positiveObservableMoment S u k * completedNativeRealEvenCharacteristicCoefficient (n - k) =
        -(((n + 1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n + 1)) := by
      exact_mod_cast hn
    linarith
  · intro h n
    have hn := h n
    have hr :
        completedNativeRealEvenCharacteristicCoefficient 0 * positiveObservableMoment S u n +
          ∑ k ∈ Finset.range n,
            positiveObservableMoment S u k * completedNativeRealEvenCharacteristicCoefficient (n - k) =
        -(((n + 1 : ℕ) : ℝ) * completedNativeRealEvenCharacteristicCoefficient (n + 1)) := by
      linarith
    exact_mod_cast hr

/-- The first equation already calibrates the norm of the actual source. -/
theorem positiveObservableNativeConvolutionDefect_zero
    (S : H →L[ℝ] H) (u : H) :
    positiveObservableNativeConvolutionDefect S u 0 =
      completedNativeRealEvenCharacteristicCoefficient 0 * ‖u‖ ^ 2 +
        completedNativeRealEvenCharacteristicCoefficient 1 := by
  simp [positiveObservableNativeConvolutionDefect, positiveObservableMoment,
    positiveObservableOrbit]

/-- Equality of the scalar convolution identifies every geometric moment
with the existing native sequence; no moment is defined from a zero set. -/
theorem positiveObservableMoment_eq_native_of_defect_zero
    (S : H →L[ℝ] H) (u : H)
    (hdefect : ∀ n, positiveObservableNativeConvolutionDefect S u n = 0) :
    positiveObservableMoment S u = canonicalCompletedNativeLogDerivativeMoment :=
  completedNativeLogDerivativeMoment_eq_canonical
    ((positiveObservable_isNativeMomentSequence_iff_defect_zero S u).2 hdefect)

/-- A geometric source meeting the convolution has the native zeroth mass. -/
theorem positiveObservable_source_norm_sq_eq_native_zero
    (S : H →L[ℝ] H) (u : H)
    (hdefect : ∀ n, positiveObservableNativeConvolutionDefect S u n = 0) :
    ‖u‖ ^ 2 = canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := congrFun (positiveObservableMoment_eq_native_of_defect_zero S u hdefect) 0
  simpa [positiveObservableMoment, positiveObservableOrbit,
    real_inner_self_eq_norm_sq] using h

/-- Conditional native bridge for a fully constructed kernel. The only
scalar input is the displayed convolution; cyclicity supplies both strict
Gram sectors and remains an explicit geometric condition. -/
theorem completedNativeRealHPCarrierCertificate_of_positiveObservable
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H)
    (hcyclic : LinearIndependent ℝ (positiveObservableOrbit S u))
    (hdefect : ∀ n, positiveObservableNativeConvolutionDefect S u n = 0) :
    CompletedNativeRealHPCarrierCertificate (positiveObservableParityJet S u) := by
  have hrep := positiveObservableParityJet_momentKernel S hS u
  rw [positiveObservableMoment_eq_native_of_defect_zero S u hdefect] at hrep
  have hi := positiveObservableParityJet_linearIndependent_of_cyclic S u hcyclic
  exact ⟨hrep, hi.1, hi.2⟩

end
end CarrySelfAdjointOperator
