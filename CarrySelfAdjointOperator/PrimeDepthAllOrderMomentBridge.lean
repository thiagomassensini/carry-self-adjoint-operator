import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk
import CarrySelfAdjointOperator.CompletedC3AllOrderChartResponseCorrection
import CarrySelfAdjointOperator.AllOrderLogJetLedger
import Mathlib.Tactic

/-!
# Prime-depth to all-order completed moments

This module keeps the arithmetic origin of the logarithmic clock visible all
the way to the completed moment sequence.

The prime-depth ledger is not declared to be spectral data.  Instead, it
reconstructs the ordinary logarithm inside each C3 log-jet atom.  The completed
native response is then obtained by retaining the independent archimedean
completion channel.  Consequently every canonical completed-native moment is
the corresponding odd Taylor coefficient of a response whose material
logarithmic channel is written entirely through prime-camera depths.

The arbitrary finite factors of `AllOrderLogJetLedger` remain arbitrary:
this file does not identify them with clock nodes or with zero heights, and it
does not discard the quotient remainder.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- One C3 logarithmic bracket with every logarithm replaced by the exact
prime-camera depth ledger of the same integer. -/
def primeDepthCanonicalLogBracketBlock (m : ℕ) (s : ℂ) : ℂ :=
  (primeDepthLogLedger ((3 * m + 1) + 1) : ℂ) *
      positiveDirichletValue s (3 * m + 1) -
    2 * ((primeDepthLogLedger ((3 * m + 2) + 1) : ℂ) *
      positiveDirichletValue s (3 * m + 2)) +
    (primeDepthLogLedger ((3 * m + 3) + 1) : ℂ) *
      positiveDirichletValue s (3 * m + 3)

/-- The prime-depth spelling of one logarithmic bracket is exactly the
canonical logarithmic bracket. -/
theorem primeDepthCanonicalLogBracketBlock_eq_canonical
    (m : ℕ) (s : ℂ) :
    primeDepthCanonicalLogBracketBlock m s =
      canonicalLogBracketBlock m s := by
  unfold primeDepthCanonicalLogBracketBlock canonicalLogBracketBlock
  rw [positiveLogDirichletValue_eq_primeDepthLogLedger_mul,
    positiveLogDirichletValue_eq_primeDepthLogLedger_mul,
    positiveLogDirichletValue_eq_primeDepthLogLedger_mul]

/-- Finite C3 log-jet chart written only with prime-camera depth ledgers in
its logarithmic weights. -/
def primeDepthCanonicalLogBracketChart (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, primeDepthCanonicalLogBracketBlock m s

theorem primeDepthCanonicalLogBracketChart_eq_canonical
    (M : ℕ) (s : ℂ) :
    primeDepthCanonicalLogBracketChart M s =
      finiteCanonicalLogBracketChart M s := by
  unfold primeDepthCanonicalLogBracketChart finiteCanonicalLogBracketChart
  apply Finset.sum_congr rfl
  intro m hm
  exact primeDepthCanonicalLogBracketBlock_eq_canonical m s

/-- Omitted C3 log-jet tail with the same prime-depth spelling. -/
def primeDepthC3LogJetCutoffTail (M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, primeDepthCanonicalLogBracketBlock (k + M) s

theorem primeDepthC3LogJetCutoffTail_eq_canonical
    (M : ℕ) (s : ℂ) :
    primeDepthC3LogJetCutoffTail M s =
      canonicalC3LogJetCutoffTail M s := by
  unfold primeDepthC3LogJetCutoffTail canonicalC3LogJetCutoffTail
  apply tsum_congr
  intro k
  exact primeDepthCanonicalLogBracketBlock_eq_canonical (k + M) s

/-- The complete unnormalized C3 logarithmic readout, now reconstructed from
prime-depth data in both its finite head and exact tail. -/
def primeDepthCompletedC3EnrichedTfvdLogJetTailReadout (s : ℂ) : ℂ :=
  primeDepthCanonicalLogBracketChart 1 s +
    primeDepthC3LogJetCutoffTail 1 s

theorem primeDepthCompletedC3EnrichedTfvdLogJetTailReadout_eq_canonical
    (s : ℂ) :
    primeDepthCompletedC3EnrichedTfvdLogJetTailReadout s =
      canonicalCompletedC3EnrichedTfvdLogJetTailReadout s := by
  unfold primeDepthCompletedC3EnrichedTfvdLogJetTailReadout
    canonicalCompletedC3EnrichedTfvdLogJetTailReadout
  rw [primeDepthCanonicalLogBracketChart_eq_canonical,
    primeDepthC3LogJetCutoffTail_eq_canonical,
    (canonicalCompletedC3EnrichedTfvdTransport_components s).2.1]

/-- Normalized C3 logarithmic companion with its material logarithmic channel
spelled through prime depths.  The chart derivative term is retained exactly. -/
def primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
    (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  Complex.I *
    ((primeDepthCompletedC3EnrichedTfvdLogJetTailReadout s *
          cpChartFactor 3 s +
        canonicalCompletedC3EnrichedTfvdValueTailReadout s *
          deriv (cpChartFactor 3) s) /
      cpChartFactor 3 s ^ 2)

theorem primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_canonical
    (z : ℂ) :
    primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z =
      canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z := by
  unfold primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout
  rw [primeDepthCompletedC3EnrichedTfvdLogJetTailReadout_eq_canonical]

/-- Native scalar normalized response whose logarithmic companion is generated
from the prime-depth reconstruction. -/
def primeDepthNativeHeightScalarNormalizedResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
    primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z

/-- Near the centered height, the prime-depth response is exactly the existing
native-scalar normalized response. -/
theorem primeDepthNativeHeightScalarNormalizedResponse_eventuallyEq_native :
    primeDepthNativeHeightScalarNormalizedResponse =ᶠ[nhds 0]
      nativeHeightScalarNormalizedResponse := by
  have hdomain :
      {z : ℂ | operatorHeightParameter z ∈ genuineCriticalStrip} ∈ nhds 0 :=
    (hasDerivAt_operatorHeightParameter 0).continuousAt.preimage_mem_nhds
      (isOpen_genuineCriticalStrip.mem_nhds
        zero_mem_completedNativeHeightDomain)
  filter_upwards [hdomain] with z hz
  unfold primeDepthNativeHeightScalarNormalizedResponse
    nativeHeightScalarNormalizedResponse completedGreenNormalizedResponse
  rw [primeDepthCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_canonical,
    canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
      hz,
    canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
      hz]

/-- Completed response with the archimedean completion kept independent and
the material logarithmic channel presented through prime-camera depths. -/
def primeDepthCompletedNativeNormalizedResponse (z : ℂ) : ℂ :=
  nativeXiCompletionNormalizedResponse z +
    primeDepthNativeHeightScalarNormalizedResponse z

/-- The prime-depth completed response is the canonical completed normalized
response as a germ at the Taylor center. -/
theorem primeDepthCompletedNativeNormalizedResponse_eventuallyEq_completed :
    primeDepthCompletedNativeNormalizedResponse =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  filter_upwards
    [primeDepthNativeHeightScalarNormalizedResponse_eventuallyEq_native,
      completedNativeGreenNormalizedResponse_eventuallyEq_factorResponses]
      with z hprime hcompleted
  unfold primeDepthCompletedNativeNormalizedResponse
  rw [hprime]
  exact hcompleted.symm

/-- Taylor coefficients of the prime-depth completed response. -/
def primeDepthCompletedNativeResponseTaylorCoefficient
    (order : ℕ) : ℂ :=
  iteratedDeriv order primeDepthCompletedNativeNormalizedResponse 0 /
    order.factorial

/-- At every order the prime-depth completed response has the same coefficient
as the canonical completed response. -/
theorem primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed
    (order : ℕ) :
    primeDepthCompletedNativeResponseTaylorCoefficient order =
      completedNativeGreenResponseTaylorCoefficient order := by
  unfold primeDepthCompletedNativeResponseTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    primeDepthCompletedNativeNormalizedResponse_eventuallyEq_completed]

/-- Main bridge: every canonical completed-native logarithmic moment is an odd
Taylor coefficient of the completed response whose material logarithmic
channel is generated by prime-camera depths. -/
theorem canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse
    (n : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment n : ℂ) =
      primeDepthCompletedNativeResponseTaylorCoefficient (2 * n + 1) := by
  rw [primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed]
  exact (completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n).symm

/-- Composition with the existing all-order finite-factor ledger.  The factors
remain arbitrary and the quotient remainder remains explicit; the new content
is that the left side has an exact prime-depth material presentation before
completion. -/
theorem primeDepthResponseTaylorCoefficient_eq_finiteFactors_add_remainder
    {ι : Type*} (S : Finset ι) (a : ι → ℂ) (m : ℕ) :
    primeDepthCompletedNativeResponseTaylorCoefficient (2 * m + 1) =
      (∑ i ∈ S, a i ^ (m + 1)) -
        iteratedDeriv m
          (logDeriv (fun u => completedNativeEvenCharacteristic u /
            ∏ i ∈ S, (1 - a i * u))) 0 / m.factorial := by
  rw [primeDepthCompletedNativeResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  exact AllOrderLogJet.nativeMoment_eq_finiteFactors_add_remainder S a m

end

end CarrySelfAdjointOperator
