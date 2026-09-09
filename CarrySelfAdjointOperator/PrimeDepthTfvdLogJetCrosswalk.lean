import CarrySelfAdjointOperator.C2FiberDepthLogTransport
import CarrySelfAdjointOperator.C2AlignedBoxOddCoreCrosswalk
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.NativeDepthCpLogJetCommutatorCrosswalk
import CarrySelfAdjointOperator.CompletedNativeTfvdAllOrderTaylorCompletion
import CarrySelfAdjointOperator.CompletedNativeTfvdRawAllOrderJetBridge
import CPFormal.Carry.CpMultibaseCameraAtlas
import CPFormal.Carry.PositionalDecomposition

/-!
# Prime-depth reconstruction of the TFVD log channel

The pinned `CPFormal` snapshot does not export the later `primos` declarations
named `primeDepthLogCoordinate` and `primeVerticalScale`.  This file therefore
uses the smallest adapter needed by the current pin: a finite sum of the
already available positional depths over `n.primeFactors`.  The adapter is
proved equal to the ordinary real logarithm, and is then substituted into the
existing native/TFVD states.  No new carrier or analytic generator is
introduced.
-/

open scoped BigOperators Topology lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Carry.Positional
open CPFormal.Carry.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The prime-camera depth ledger in the current pinned APIs. -/
def primeDepthLogLedger (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (positionalDepth p n : ℝ) * Real.log p

/-- On a prime support, positional depth is the factorization exponent. -/
theorem positionalDepth_eq_cameraVertical
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    positionalDepth p n = CPFormal.Carry.Cp.cameraVertical n p := by
  unfold positionalDepth CPFormal.Carry.Cp.cameraVertical
  exact Nat.multiplicity_eq_factorization hp hn

/-- The current pin reconstructs `log n` from prime-camera depths. -/
theorem primeDepthLogLedger_eq_log {n : ℕ} (hn : n ≠ 0) :
    primeDepthLogLedger n = Real.log n := by
  rw [primeDepthLogLedger]
  have hsupp : n.factorization.support = n.primeFactors := by
    rw [Nat.support_factorization]
  calc
    (∑ p ∈ n.primeFactors, (positionalDepth p n : ℝ) * Real.log p) =
        ∑ p ∈ n.factorization.support,
          (n.factorization p : ℝ) * Real.log p := by
      rw [hsupp]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show positionalDepth p n = n.factorization p by
        unfold positionalDepth
        exact Nat.multiplicity_eq_factorization
          (Nat.prime_of_mem_primeFactors hp) hn]
    _ = Real.log n := (CPFormal.Carry.Cp.log_eq_sum_vertical hn).symm

/-- The same ledger written in the factorization-vector coordinates. -/
theorem primeDepthLogLedger_eq_factorizationLedger {n : ℕ} (hn : n ≠ 0) :
    primeDepthLogLedger n =
      ∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ) * Real.log p := by
  rw [primeDepthLogLedger_eq_log hn]
  exact CPFormal.Carry.Cp.log_eq_sum_vertical hn

/-- The depth ledger agrees with the camera-atlas vertical voice. -/
theorem primeDepthLogLedger_eq_cameraVerticalLedger {n : ℕ} (hn : n ≠ 0) :
    primeDepthLogLedger n =
      ∑ p ∈ n.primeFactors,
        (CPFormal.Carry.Cp.cameraVertical n p : ℝ) * Real.log p := by
  rw [primeDepthLogLedger]
  apply Finset.sum_congr rfl
  intro p hp
  rw [positionalDepth_eq_cameraVertical hn
    (Nat.prime_of_mem_primeFactors hp)]

/-- The positive Dirichlet log value with its logarithm reconstructed from
prime-camera depths.  The `n + 1` shift is the one used by the pinned API. -/
theorem positiveLogDirichletValue_eq_primeDepthLogLedger_mul
    (s : ℂ) (n : ℕ) :
    CPFormal.Analytic.Cp.positiveLogDirichletValue s n =
      (primeDepthLogLedger (n + 1) : ℂ) *
        CPFormal.Analytic.Cp.positiveDirichletValue s n := by
  rw [CPFormal.Analytic.Cp.positiveLogDirichletValue]
  rw [primeDepthLogLedger_eq_log (Nat.succ_ne_zero n)]

/-- The native Dirichlet log term has the same prime-depth presentation. -/
theorem natLogDirichletTerm_eq_primeDepthLogLedger_mul
    (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    CPFormal.Analytic.Cp.natLogDirichletTerm s n =
      (primeDepthLogLedger n : ℂ) *
        CPFormal.Analytic.Cp.natDirichletTerm s n := by
  rw [CPFormal.Analytic.Cp.natLogDirichletTerm,
    primeDepthLogLedger_eq_log hn]

/-- The consecutive log slope is obtained by replacing each log factor by
the corresponding prime-depth ledger. -/
theorem positiveLogDirichletGradient_eq_primeDepthSlope
    (s : ℂ) (n : ℕ) :
    CPFormal.Analytic.Cp.positiveLogDirichletGradient s n =
      (primeDepthLogLedger (n + 2) : ℂ) *
          CPFormal.Analytic.Cp.positiveDirichletValue s (n + 1) -
        (primeDepthLogLedger (n + 1) : ℂ) *
          CPFormal.Analytic.Cp.positiveDirichletValue s n := by
  rw [CPFormal.Analytic.Cp.positiveLogDirichletGradient,
    positiveLogDirichletValue_eq_primeDepthLogLedger_mul,
    positiveLogDirichletValue_eq_primeDepthLogLedger_mul]

/-- On the native line, the reconstructed slope is the existing packaged
native log slope. -/
theorem positiveLogDirichletGradient_nativeLine_eq_primeDepthPackagedNativeLogSlope
    (time : ℝ) (n : ℕ) :
    CPFormal.Analytic.Cp.positiveLogDirichletGradient (nativeLine time) n =
      (primeDepthLogLedger (n + 2) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 2)) -
        (primeDepthLogLedger (n + 1) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 1)) := by
  rw [positiveLogDirichletGradient_nativeLine_eq_packagedNativeLogSlope,
    primeDepthLogLedger_eq_log (by omega : n + 2 ≠ 0),
    primeDepthLogLedger_eq_log (by omega : n + 1 ≠ 0)]

/-- The all-order Taylor coefficient of the log channel with the two log
factors written as prime-depth ledgers. -/
theorem nativeLogDirichletSlopeTaylorCoefficient_eq_primeDepthLedger_form
    (order n : ℕ) :
    nativeLogDirichletSlopeTaylorCoefficient order n =
      (primeDepthLogLedger (n + 2) : ℂ) *
          nativeCriticalDirichletAmplitude (n + 2) *
            (-Complex.I * (primeDepthLogLedger (n + 2) : ℂ)) ^ order /
              (order.factorial : ℂ) -
        (primeDepthLogLedger (n + 1) : ℂ) *
          nativeCriticalDirichletAmplitude (n + 1) *
            (-Complex.I * (primeDepthLogLedger (n + 1) : ℂ)) ^ order /
              (order.factorial : ℂ) := by
  unfold nativeLogDirichletSlopeTaylorCoefficient
  rw [primeDepthLogLedger_eq_log (by omega : n + 2 ≠ 0),
    primeDepthLogLedger_eq_log (by omega : n + 1 ≠ 0)]

/-- Finite `CarryVerticalL2` log slope state presented through the depth
ledger.  It has exactly the same carrier and samples as the existing native
state; only the spelling of the real logarithm has changed. -/
def finitePrimeDepthGeneratedLogSlopePrefixState
    (M : ℕ) (time : ℝ) : CPFormal.Analytic.Cp.CarryVerticalL2 :=
  CPFormal.Analytic.Cp.nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M, Finsupp.single n
      ((primeDepthLogLedger (n + 2) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 2)) -
        (primeDepthLogLedger (n + 1) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (n + 1))))

/-- The prime-depth presentation is exactly the already packaged native
log-slope prefix. -/
theorem finitePrimeDepthGeneratedLogSlopePrefixState_eq_nativeLogSlope
    (M : ℕ) (time : ℝ) :
    finitePrimeDepthGeneratedLogSlopePrefixState M time =
      finitePackagedNativeLogSlopePrefixState M time := by
  ext n
  change
    (∑ i ∈ Finset.range M, Finsupp.single i
      ((primeDepthLogLedger (i + 2) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (i + 2)) -
        (primeDepthLogLedger (i + 1) : ℂ) *
          CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
            (FiniteNativeCarryOperator.Operator.nativeState time (i + 1)))) n =
      (∑ i ∈ Finset.range M, Finsupp.single i
        ((Real.log ((i + 2 : ℕ) : ℝ) : ℂ) *
            CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
              (FiniteNativeCarryOperator.Operator.nativeState time (i + 2)) -
          (Real.log ((i + 1 : ℕ) : ℝ) : ℂ) *
            CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
              (FiniteNativeCarryOperator.Operator.nativeState time (i + 1)))) n
  by_cases hn : n < M
  · have h1 : primeDepthLogLedger (n + 2) =
        Real.log ((n + 2 : ℕ) : ℝ) :=
      primeDepthLogLedger_eq_log (by omega)
    have h2 : primeDepthLogLedger (n + 1) =
        Real.log ((n + 1 : ℕ) : ℝ) :=
      primeDepthLogLedger_eq_log (by omega)
    simp [Finset.sum_apply, Finsupp.single_apply, hn, h1, h2]
  · simp [Finset.sum_apply, Finsupp.single_apply, hn]

/-- The same state is the completed C3 log-jet prefix. -/
theorem finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix
    (M : ℕ) (time : ℝ) :
    finitePrimeDepthGeneratedLogSlopePrefixState M time =
      canonicalCompletedC3LogJetPrefixState (nativeLine time) M := by
  exact (finitePrimeDepthGeneratedLogSlopePrefixState_eq_nativeLogSlope M time).trans
    (finitePackagedNativeLogSlopePrefixState_eq_completedTfvdLogJetPrefix M time)

/-- The ordinary channel is retained unchanged while the log channel is
presented by prime-depth data. -/
def finitePrimeDepthGeneratedC3HilbertPrefixState
    (M : ℕ) (time : ℝ) : CanonicalCompletedC3HilbertState :=
  (finitePackagedNativeSlopePrefixState M time,
    finitePrimeDepthGeneratedLogSlopePrefixState M time)

/-- The enriched prime-depth presentation is the existing completed TFVD
Hilbert prefix state. -/
theorem finitePrimeDepthGeneratedC3HilbertPrefixState_eq_completedTfvd
    (M : ℕ) (time : ℝ) :
    finitePrimeDepthGeneratedC3HilbertPrefixState M time =
      canonicalCompletedC3HilbertPrefixState (nativeLine time) M := by
  apply Prod.ext
  · exact finitePackagedNativeSlopePrefixState_eq_completedTfvdOrdinaryPrefix M time
  · exact finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix M time

/-- Any existing scalar or vector readout transports through the exact state
equality.  This is the small congruence principle used for weighted brackets,
Green response and trace maps; it does not duplicate those pipelines. -/
theorem primeDepthLogJetPrefix_readout_eq_canonical
    {β : Type} (readout : CPFormal.Analytic.Cp.CarryVerticalL2 → β)
    (M : ℕ) (time : ℝ) :
    readout (finitePrimeDepthGeneratedLogSlopePrefixState M time) =
      readout (canonicalCompletedC3LogJetPrefixState (nativeLine time) M) := by
  rw [finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix]

/-- The C2 centered logarithm separates the current depth from the prime
ledger of its core. -/
theorem c2Fiber_centeredLog_eq_depth_add_primeCoreLedger
    (m k : ℕ) (hm : 0 < m) (ε : ℝ) :
    Real.log (c2FiberPoint m ε k - ε) =
      (k : ℝ) * Real.log 2 + primeDepthLogLedger m := by
  rw [c2FiberPoint_centered_log m k hm ε,
    primeDepthLogLedger_eq_log (Nat.ne_of_gt hm)]

/-- The unshifted C2 center has the same decomposition. -/
theorem c2Fiber_center_log_eq_depth_add_primeCoreLedger
    (m k : ℕ) (hm : 0 < m) :
    Real.log (((2 ^ k * m : ℕ) : ℝ)) =
      (k : ℝ) * Real.log 2 + primeDepthLogLedger m := by
  simpa [c2FiberPoint] using
    (c2Fiber_centeredLog_eq_depth_add_primeCoreLedger m k hm 0)

/-- The aligned C2 camera center uses its current depth plus the prime ledger
of the odd core. -/
theorem c2AlignedCenter_log_eq_currentDepth_add_primeCoreLedger (j : ℕ) :
    Real.log ((4 * (j + 1) : ℕ) : ℝ) =
      (c2AlignedIndexDepth j : ℝ) * Real.log 2 +
        primeDepthLogLedger (c2AlignedIndexCore j) := by
  rw [c2AlignedCenter_log_eq_fiberDepthLog j,
    primeDepthLogLedger_eq_log (Nat.ne_of_gt (c2AlignedIndexCore_pos j))]

/-- The existing Newton/Green decomposition with the core coefficient written
as the prime-depth seed. -/
theorem c2Fiber_centeredLog_amplitude_eq_green_and_primeDepthSeed
    (m k : ℕ) (hm : 0 < m) (ε : ℝ) :
    Real.log (c2FiberPoint m ε k - ε) * CPFormal.Carry.Cp.criticalAmplitude 2 k =
      Real.log 2 * ProjectiveDepth.newtonJet
        (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 1 k +
      primeDepthLogLedger m * ProjectiveDepth.newtonJet
        (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) 0 k := by
  rw [c2Fiber_centeredLog_amplitude_eq_green_and_seed m k hm ε,
    primeDepthLogLedger_eq_log (Nat.ne_of_gt hm)]

end
end CarrySelfAdjointOperator
