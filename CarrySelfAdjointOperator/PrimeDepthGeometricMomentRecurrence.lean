import CarrySelfAdjointOperator.PrimeDepthAllOrderMomentBridge

/-!
# Source-first prime-depth response moments

The candidate is extracted from the existing prime-depth material response,
with exact TFVD head/tail and independent archimedean completion retained.
Its recurrence comes from the analytic product identity and Leibniz rule,
not from equality with a prescribed moment sequence. Identification with
the canonical recursive sequence occurs only in the final theorem.

No incidence, Gram, positivity, Jacobi, or height construction is an input.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators

noncomputable section

/-- Real readout of the odd Taylor coefficients of the prime-depth completed
response. No target moment or spectral datum enters this definition. -/
def primeDepthGeometricMoment (n : ℕ) : ℝ :=
  (primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1)).re

/-- The response product identity transports through equality of germs.
The authoritative convolution proof uses analytic Leibniz and factorials,
not the already-known moment identification. -/
theorem primeDepthResponse_oddCoefficient_recurrence (n : ℕ) :
    completedNativeEvenCharacteristicCoefficient 0 *
        primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1) +
      ∑ k ∈ Finset.range n,
        primeDepthCompletedNativeResponseTaylorCoefficient (2 * k + 1) *
          completedNativeEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1)) := by
  simp_rw [primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed]
  exact completedNativeGreenResponse_oddCoefficient_recurrence n

private theorem primeDepthGeometricMoment_real_recurrence (n : ℕ) :
    completedNativeRealEvenCharacteristicCoefficient 0 * primeDepthGeometricMoment n +
      ∑ k ∈ Finset.range n,
        primeDepthGeometricMoment k *
          completedNativeRealEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℝ) *
        completedNativeRealEvenCharacteristicCoefficient (n + 1)) := by
  have h := primeDepthResponse_oddCoefficient_recurrence n
  simp_rw [completedNativeEvenCharacteristicCoefficient_eq_real] at h
  simpa [primeDepthGeometricMoment, Complex.mul_re] using congrArg Complex.re h

/-- Zeroth canary from the response recurrence, before canonical comparison. -/
theorem primeDepthGeometricMoment_zero :
    primeDepthGeometricMoment 0 =
      -completedNativeRealEvenCharacteristicCoefficient 1 /
        completedNativeRealEvenCharacteristicCoefficient 0 := by
  apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
  have h := primeDepthGeometricMoment_real_recurrence 0
  simpa [mul_comm] using h

/-- First canary retains the zeroth response coefficient in its source recurrence. -/
theorem primeDepthGeometricMoment_one :
    primeDepthGeometricMoment 1 =
      (-(2 * completedNativeRealEvenCharacteristicCoefficient 2) -
        primeDepthGeometricMoment 0 * completedNativeRealEvenCharacteristicCoefficient 1) /
        completedNativeRealEvenCharacteristicCoefficient 0 := by
  apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
  have h := primeDepthGeometricMoment_real_recurrence 1
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- Second canary, with both preceding geometric coefficients retained. -/
theorem primeDepthGeometricMoment_two :
    primeDepthGeometricMoment 2 =
      (-(3 * completedNativeRealEvenCharacteristicCoefficient 3) -
        primeDepthGeometricMoment 0 * completedNativeRealEvenCharacteristicCoefficient 2 -
        primeDepthGeometricMoment 1 * completedNativeRealEvenCharacteristicCoefficient 1) /
        completedNativeRealEvenCharacteristicCoefficient 0 := by
  apply (eq_div_iff completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero).2
  have h := primeDepthGeometricMoment_real_recurrence 2
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- All-order source-first log-derivative recurrence. -/
theorem primeDepthGeometricMoment_isLogDerivativeMomentSequence :
    IsLogDerivativeMomentSequence
      completedNativeRealEvenCharacteristicCoefficient primeDepthGeometricMoment :=
  primeDepthGeometricMoment_real_recurrence

/-- Reality follows recursively from the independent response equation and
real characteristic coefficients. No target moment equality is used. -/
theorem primeDepthResponse_oddCoefficient_im_zero (n : ℕ) :
    (primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1)).im = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrec := primeDepthResponse_oddCoefficient_recurrence n
      simp_rw [completedNativeEvenCharacteristicCoefficient_eq_real] at hrec
      have him :
          completedNativeRealEvenCharacteristicCoefficient 0 *
              (primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1)).im +
            ∑ k ∈ Finset.range n,
              (primeDepthCompletedNativeResponseTaylorCoefficient (2 * k + 1)).im *
                completedNativeRealEvenCharacteristicCoefficient (n - k) = 0 := by
        simpa [Complex.mul_im] using congrArg Complex.im hrec
      have hsum :
          ∑ k ∈ Finset.range n,
            (primeDepthCompletedNativeResponseTaylorCoefficient (2 * k + 1)).im *
              completedNativeRealEvenCharacteristicCoefficient (n - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [ih k (Finset.mem_range.mp hk), zero_mul]
      rw [hsum, add_zero] at him
      exact (mul_eq_zero.mp him).resolve_left
        completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero

/-- Taking the real part loses nothing in this source sequence. -/
theorem primeDepthGeometricMoment_coe (n : ℕ) :
    (primeDepthGeometricMoment n : ℂ) =
      primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1) := by
  apply Complex.ext
  · rfl
  · simp [primeDepthResponse_oddCoefficient_im_zero]

/-- Concrete predecessor readout: the normalized Wronskian of the existing
structured TFVD head/tail carrier has exactly these response coefficients.
This is a scalar readout theorem, not a Hilbert Gram or a vector-jet theorem. -/
theorem primeDepthGeometricMoment_eq_bracketTfvdReadoutTaylor (M n : ℕ) :
    (primeDepthGeometricMoment n : ℂ) =
      canonicalC3BracketTfvdResponseTaylorCoefficient M (2 * n + 1) := by
  rw [primeDepthGeometricMoment_coe,
    primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed,
    canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed]

/-- First comparison with the canonical sequence: independent recurrence,
center nonvanishing, and real log-derivative uniqueness alone identify it. -/
theorem primeDepthGeometricMoment_eq_canonical :
    primeDepthGeometricMoment = canonicalCompletedNativeLogDerivativeMoment := by
  apply IsLogDerivativeMomentSequence.unique
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
    primeDepthGeometricMoment_isLogDerivativeMomentSequence
  intro n
  simpa only [neg_mul] using canonicalCompletedNativeLogDerivativeMoment_real_recurrence n

end

end CarrySelfAdjointOperator
