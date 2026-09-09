import CarrySelfAdjointOperator.PrimeDepthTfvdLogJetCrosswalk
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CPFormal.Carry.CpMultibaseCameraAtlasHilbert
import CPFormal.Carry.CpMultibaseCameraAtlas
import CPFormal.Analytic.CpNativeGpreTfvdCanonicalGluing
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic

open scoped BigOperators Topology lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Carry.Cp
open CPFormal.Carry.Positional
open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera

noncomputable section

abbrev CameraLogComplexSpace := ℕ →₀ ℂ

/-- The contribution of each prime camera to the logarithmic ledger of `n`.
The outer index is a camera label; it is not a vertical TFVD coordinate. -/
noncomputable def cameraLogContributionVector (n : ℕ) : CameraLogSpace :=
  Finsupp.onFinset n.factorization.support
    (fun p => (n.factorization p : ℝ) * Real.log p)
    (by
      intro p hp
      by_contra hpmem
      have hzero : n.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp hpmem
      exact hp (by simp [hzero]))

@[simp] theorem cameraLogContributionVector_apply (n p : ℕ) :
    cameraLogContributionVector n p =
      (n.factorization p : ℝ) * Real.log p := by
  rfl

noncomputable def cameraLogContributionSynthesis :
    CameraLogSpace →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : ℕ => (1 : ℝ))

theorem cameraLogContributionSynthesis_apply (x : CameraLogSpace) :
    cameraLogContributionSynthesis x =
      ∑ p ∈ x.support, x p := by
  simp [cameraLogContributionSynthesis, Finsupp.linearCombination_apply,
    Finsupp.sum]

theorem cameraLogContributionSynthesis_eq_primeDepthLogLedger (n : ℕ) :
    cameraLogContributionSynthesis (cameraLogContributionVector n) =
      primeDepthLogLedger n := by
  rw [cameraLogContributionSynthesis, cameraLogContributionVector,
    Finsupp.linearCombination_onFinset]
  simp only [smul_eq_mul]
  rw [primeDepthLogLedger]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show positionalDepth p n = n.factorization p by
    unfold positionalDepth
    exact Nat.multiplicity_eq_factorization
      (Nat.prime_of_mem_primeFactors hp) (by
        by_contra hn
        simp [hn] at hp)]
  ring

theorem cameraLogContributionSynthesis_eq_log {n : ℕ} (hn : n ≠ 0) :
    cameraLogContributionSynthesis (cameraLogContributionVector n) =
      Real.log n := by
  rw [cameraLogContributionSynthesis_eq_primeDepthLogLedger,
    primeDepthLogLedger_eq_log hn]

/-- The same finite-support camera ledger over the complex scalars. -/
noncomputable def cameraLogContributionVectorComplex (n : ℕ) :
    CameraLogComplexSpace :=
  Finsupp.onFinset n.factorization.support
    (fun p => ((n.factorization p : ℝ) * Real.log p : ℂ))
    (by
      intro p hp
      by_contra hpmem
      have hzero : n.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp hpmem
      exact hp (by simp [hzero]))

@[simp] theorem cameraLogContributionVectorComplex_apply (n p : ℕ) :
    cameraLogContributionVectorComplex n p =
      ((n.factorization p : ℝ) * Real.log p : ℂ) := by
  rfl

noncomputable def cameraComplexSynthesis :
    CameraLogComplexSpace →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun _ : ℕ => (1 : ℂ))

theorem cameraComplexSynthesis_apply (x : CameraLogComplexSpace) :
    cameraComplexSynthesis x =
      ∑ p ∈ x.support, x p := by
  simp [cameraComplexSynthesis, Finsupp.linearCombination_apply,
    Finsupp.sum]

theorem cameraComplexSynthesis_cameraLogContributionVectorComplex (n : ℕ) :
    cameraComplexSynthesis (cameraLogContributionVectorComplex n) =
      (primeDepthLogLedger n : ℂ) := by
  rw [cameraComplexSynthesis, cameraLogContributionVectorComplex,
    Finsupp.linearCombination_onFinset]
  simp only [smul_eq_mul]
  rw [primeDepthLogLedger]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [show positionalDepth p n = n.factorization p by
    unfold positionalDepth
    exact Nat.multiplicity_eq_factorization
      (Nat.prime_of_mem_primeFactors hp) (by
        by_contra hn
        simp [hn] at hp)]
  ring

/-- Logarithmic Dirichlet values before the final scalar synthesis. -/
noncomputable def cameraResolvedLogDirichletValue (s : ℂ) (n : ℕ) :
    CameraLogComplexSpace :=
  positiveDirichletValue s n • cameraLogContributionVectorComplex (n + 1)

@[simp] theorem cameraResolvedLogDirichletValue_apply
    (s : ℂ) (n p : ℕ) :
    cameraResolvedLogDirichletValue s n p =
      positiveDirichletValue s n *
        cameraLogContributionVectorComplex (n + 1) p := by
  rfl

theorem cameraComplexSynthesis_cameraResolvedLogDirichletValue
    (s : ℂ) (n : ℕ) :
    cameraComplexSynthesis (cameraResolvedLogDirichletValue s n) =
      positiveLogDirichletValue s n := by
  rw [cameraResolvedLogDirichletValue,
    cameraComplexSynthesis.map_smul,
    cameraComplexSynthesis_cameraLogContributionVectorComplex]
  rw [positiveLogDirichletValue_eq_primeDepthLogLedger_mul]
  ring

/-- Consecutive log slopes with camera voices still separated. -/
noncomputable def cameraResolvedLogDirichletGradient (s : ℂ) (n : ℕ) :
    CameraLogComplexSpace :=
  cameraResolvedLogDirichletValue s (n + 1) -
    cameraResolvedLogDirichletValue s n

@[simp] theorem cameraResolvedLogDirichletGradient_apply
    (s : ℂ) (n p : ℕ) :
    cameraResolvedLogDirichletGradient s n p =
      cameraResolvedLogDirichletValue s (n + 1) p -
        cameraResolvedLogDirichletValue s n p := by
  rfl

theorem cameraComplexSynthesis_cameraResolvedLogDirichletGradient
    (s : ℂ) (n : ℕ) :
    cameraComplexSynthesis (cameraResolvedLogDirichletGradient s n) =
      positiveLogDirichletGradient s n := by
  rw [cameraResolvedLogDirichletGradient,
    map_sub,
    cameraComplexSynthesis_cameraResolvedLogDirichletValue,
    cameraComplexSynthesis_cameraResolvedLogDirichletValue,
    positiveLogDirichletGradient]

/-! The atlas decomposition is retained at the coefficient level. -/

noncomputable def cameraLogVerticalContribution (n p : ℕ) : CameraLogSpace :=
  ((n.factorization p : ℝ) * Real.log p) • cameraAxis p

noncomputable def cameraLogHorizontalContribution (n p : ℕ) : CameraLogSpace :=
  cameraLogContributionVector n - cameraLogVerticalContribution n p

theorem cameraLogVerticalContribution_mem (n p : ℕ) :
    cameraLogVerticalContribution n p ∈ cameraVerticalLine p := by
  apply (cameraVerticalLine p).smul_mem
  · rw [cameraVerticalLine]
    exact Finsupp.single_mem_supported ℝ 1 (by simp)

theorem cameraLogHorizontalContribution_mem (n p : ℕ) :
    cameraLogHorizontalContribution n p ∈ cameraHorizontalSpace p := by
  rw [cameraHorizontalSpace, Finsupp.mem_supported']
  intro q hq
  have hqp : q = p := by simpa using hq
  subst q
  simp [cameraLogHorizontalContribution, cameraLogVerticalContribution,
    cameraLogContributionVector_apply, cameraAxis]

theorem cameraLogContributionVector_eq_vertical_add_horizontal
    (n p : ℕ) :
    cameraLogContributionVector n =
      cameraLogVerticalContribution n p + cameraLogHorizontalContribution n p := by
  simp [cameraLogHorizontalContribution]

theorem cameraLogHorizontalContribution_synthesis_sub (n p : ℕ) :
    cameraLogContributionSynthesis (cameraLogHorizontalContribution n p) =
      primeDepthLogLedger n - (n.factorization p : ℝ) * Real.log p := by
  rw [cameraLogHorizontalContribution, map_sub,
    cameraLogContributionSynthesis_eq_primeDepthLogLedger]
  rw [cameraLogVerticalContribution, cameraLogContributionSynthesis.map_smul]
  have haxis : cameraLogContributionSynthesis (cameraAxis p) = 1 := by
    simp [cameraLogContributionSynthesis, cameraAxis,
      Finsupp.linearCombination_apply]
  rw [haxis]
  ring

theorem cameraAtlas_blind_direction_survives :
    logEvalBlindVector ≠ 0 ∧ logEval logEvalBlindVector = 0 :=
  ⟨logEvalBlindVector_ne_zero, logEval_logEvalBlindVector⟩

/-! ## A finite multichannel carrier

The outer `ℕ` index below is a camera label, while the value of each entry is
the already existing vertical Hilbert state.  This is only an algebraic
finite-support carrier; it does not identify a camera label with a vertical
sample coordinate and it does not add a new completion.
-/

abbrev CameraResolvedCarryVertical := ℕ →₀ CarryVerticalL2

noncomputable def cameraChannelSynthesis :
    CameraResolvedCarryVertical →ₗ[ℂ] CarryVerticalL2 :=
  Finsupp.lsum ℂ (fun _ : ℕ => LinearMap.id)

noncomputable def cameraResolvedLogSlopeChannel
    (M : ℕ) (time : ℝ) (p : ℕ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (∑ n ∈ Finset.range M,
      Finsupp.single n
        ((cameraResolvedLogDirichletGradient (nativeLine time) n) p))

@[simp] theorem cameraResolvedLogSlopeChannel_apply
    (M : ℕ) (time : ℝ) (p r : ℕ) :
    cameraResolvedLogSlopeChannel M time p r =
      ∑ n ∈ Finset.range M,
        if n = r then
          (cameraResolvedLogDirichletGradient (nativeLine time) n) p
        else 0 := by
  change
    (∑ n ∈ Finset.range M,
      Finsupp.single n
        ((cameraResolvedLogDirichletGradient (nativeLine time) n) p)) r = _
  by_cases hr : r < M <;> simp [Finset.sum_apply, Finsupp.single_apply, hr]

noncomputable def cameraResolvedLogSlopeSupport
    (M : ℕ) (time : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range M).biUnion (fun n =>
    (cameraResolvedLogDirichletGradient (nativeLine time) n).support)

noncomputable def finiteCameraResolvedLogSlopePrefixState
    (M : ℕ) (time : ℝ) : CameraResolvedCarryVertical := by
  classical
  exact ∑ p ∈ cameraResolvedLogSlopeSupport M time,
    Finsupp.single p (cameraResolvedLogSlopeChannel M time p)

@[simp] theorem cameraChannelSynthesis_single
    (p : ℕ) (x : CarryVerticalL2) :
    cameraChannelSynthesis (Finsupp.single p x) = x := by
  simp [cameraChannelSynthesis]

theorem finiteCameraResolvedLogSlopePrefixState_synthesis_apply
    (M : ℕ) (time : ℝ) :
    cameraChannelSynthesis (finiteCameraResolvedLogSlopePrefixState M time) =
      ∑ p ∈ cameraResolvedLogSlopeSupport M time,
        cameraResolvedLogSlopeChannel M time p := by
  simp [finiteCameraResolvedLogSlopePrefixState, cameraChannelSynthesis]

theorem finiteCameraResolvedLogSlopePrefixState_synthesis_eq_primeDepth
    (M : ℕ) (time : ℝ) :
    cameraChannelSynthesis (finiteCameraResolvedLogSlopePrefixState M time) =
      finitePrimeDepthGeneratedLogSlopePrefixState M time := by
  classical
  have hsupport (n : ℕ) (hn : n < M) :
      (cameraResolvedLogDirichletGradient (nativeLine time) n).support ⊆
        cameraResolvedLogSlopeSupport M time := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn, hp⟩
  have hsum (n : ℕ) (hn : n < M) :
      (∑ p ∈ cameraResolvedLogSlopeSupport M time,
        (cameraResolvedLogDirichletGradient (nativeLine time) n) p) =
      positiveLogDirichletGradient (nativeLine time) n := by
    let g := cameraResolvedLogDirichletGradient (nativeLine time) n
    calc
      (∑ p ∈ cameraResolvedLogSlopeSupport M time, g p) =
          ∑ p ∈ g.support, g p := by
        symm
        apply Finset.sum_subset (hsupport n hn)
        intro p hp hnot
        exact Finsupp.notMem_support_iff.mp hnot
      _ = cameraComplexSynthesis g :=
        (cameraComplexSynthesis_apply g).symm
      _ = positiveLogDirichletGradient (nativeLine time) n :=
        cameraComplexSynthesis_cameraResolvedLogDirichletGradient
          (nativeLine time) n
  rw [finiteCameraResolvedLogSlopePrefixState_synthesis_apply]
  rw [finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix]
  ext r
  rw [canonicalCompletedC3LogJetPrefixState_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply,
    cameraResolvedLogSlopeChannel_apply]
  rw [Finset.sum_comm]
  by_cases hr : r < M
  · simpa [hr] using hsum r hr
  · simp [hr]

theorem finiteCameraResolvedLogSlopePrefixState_synthesis_eq_completedTfvd
    (M : ℕ) (time : ℝ) :
    cameraChannelSynthesis (finiteCameraResolvedLogSlopePrefixState M time) =
      canonicalCompletedC3LogJetPrefixState (nativeLine time) M := by
  exact (finiteCameraResolvedLogSlopePrefixState_synthesis_eq_primeDepth M time).trans
    (finitePrimeDepthGeneratedLogSlopePrefixState_eq_completedTfvdLogJetPrefix
      M time)

/-! ## Channelwise TFVD maps

The existing finite analysis and reconstruction are linear on the vertical
carrier.  `mapRange.linearMap` applies either one coordinatewise to the outer
camera index, while `lsum` performs the final synthesis. -/

noncomputable def cameraChannelTfvdAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CameraResolvedCarryVertical →ₗ[ℂ]
      (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S) :=
  Finsupp.mapRange.linearMap
    (nativeGpreFiniteTfvdAnalysis q S).toLinearMap

noncomputable def cameraChannelAnalysisSynthesis
    (S : Finset NativeGpreBoundaryContext) :
    (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S) →ₗ[ℂ]
      NativeGpreFiniteTfvdAnalysisCarrier S :=
  Finsupp.lsum ℂ (fun _ : ℕ => LinearMap.id)

noncomputable def cameraChannelTfvdReconstruction
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S) →ₗ[ℂ]
      CameraResolvedCarryVertical :=
  Finsupp.mapRange.linearMap
    (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S).toLinearMap

theorem finsupp_synthesis_mapRange_commutes
    {X Y : Type*} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y]
    (A : X →ₗ[ℂ] Y) (x : ℕ →₀ X) :
    (Finsupp.lsum ℂ
      (fun _ : ℕ => (LinearMap.id : Y →ₗ[ℂ] Y)))
        (Finsupp.mapRange.linearMap A x) =
      A ((Finsupp.lsum ℂ
        (fun _ : ℕ => (LinearMap.id : X →ₗ[ℂ] X))) x) := by
  rw [Finsupp.lsum_apply]
  change
    (Finsupp.mapRange A A.map_zero x).sum (fun _ y => y) =
      A (x.sum (fun _ y => y))
  rw [Finsupp.sum_mapRange_index (by intro a; rfl)]
  simpa using (map_finsuppSum A x (fun _ y => y)).symm

theorem cameraChannelSynthesis_mapRange_commutes
    {Y : Type*} [AddCommMonoid Y] [Module ℂ Y]
    (A : CarryVerticalL2 →ₗ[ℂ] Y) (x : CameraResolvedCarryVertical) :
    (Finsupp.lsum ℂ
      (fun _ : ℕ => (LinearMap.id : Y →ₗ[ℂ] Y)))
        (Finsupp.mapRange.linearMap A x) =
      A (cameraChannelSynthesis x) := by
  simpa [cameraChannelSynthesis] using
    (finsupp_synthesis_mapRange_commutes A x)

theorem cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : CameraResolvedCarryVertical) :
    cameraChannelAnalysisSynthesis S
        (cameraChannelTfvdAnalysis q S x) =
      nativeGpreFiniteTfvdAnalysis q S (cameraChannelSynthesis x) := by
  exact finsupp_synthesis_mapRange_commutes
    (nativeGpreFiniteTfvdAnalysis q S).toLinearMap x

theorem cameraChannelSynthesis_tfvdReconstruction_commutes
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x : ℕ →₀ NativeGpreFiniteTfvdAnalysisCarrier S) :
    cameraChannelSynthesis
        (cameraChannelTfvdReconstruction q hq0 hq1 S x) =
      nativeGpreFiniteTfvdReconstruction q hq0 hq1 S
        (cameraChannelAnalysisSynthesis S x) := by
  exact finsupp_synthesis_mapRange_commutes
    (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S).toLinearMap x

theorem cameraChannelTfvdReconstruction_analysis_synthesis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (x : CameraResolvedCarryVertical) :
    cameraChannelSynthesis
        (cameraChannelTfvdReconstruction q hqpos.le hq1 S
          (cameraChannelTfvdAnalysis q S x)) =
      cameraChannelSynthesis x := by
  rw [cameraChannelSynthesis_tfvdReconstruction_commutes,
    cameraChannelAnalysisSynthesis_tfvdAnalysis_commutes]
  exact nativeGpreFiniteTfvdReconstruction_analysis
    q hqpos hq1 S (cameraChannelSynthesis x)

/-! ## The C2 specialization of the channel ledger -/

theorem c2Core_cameraTwo_coordinate_eq_zero {m : ℕ} (hm : Odd m) :
    cameraLogContributionVector m 2 = 0 := by
  have hnot : ¬ 2 ∣ m := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdiv)
  rw [cameraLogContributionVector_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd hnot]
  simp

theorem c2Center_cameraTwo_logContribution_eq_depth
    (m k : ℕ) (hm : Odd m) :
    cameraLogContributionVector (2 ^ k * m) 2 =
      (k : ℝ) * Real.log 2 := by
  have hnot : ¬ 2 ∣ m := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdiv)
  rw [cameraLogContributionVector_apply]
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num))
    (Nat.ne_of_gt (Odd.pos hm))]
  rw [Nat.Prime.factorization_pow Nat.prime_two]
  simp [Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot]

theorem c2Center_otherCameraLogContribution_synthesis_eq_primeCoreLedger
    (m : ℕ) (hm : Odd m) :
    cameraLogContributionSynthesis (cameraLogHorizontalContribution m 2) =
      primeDepthLogLedger m := by
  have hnot : ¬ 2 ∣ m := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdiv)
  have hzero : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot
  rw [cameraLogHorizontalContribution_synthesis_sub]
  simp [hzero]

theorem c2Fiber_center_log_eq_cameraTwo_add_otherCamera
    (m k : ℕ) (hm : 0 < m) (hmOdd : Odd m) :
    Real.log (((2 ^ k * m : ℕ) : ℝ)) =
      (cameraLogContributionVector (2 ^ k * m) 2) +
        cameraLogContributionSynthesis (cameraLogHorizontalContribution m 2) := by
  rw [c2Center_cameraTwo_logContribution_eq_depth m k hmOdd,
    c2Center_otherCameraLogContribution_synthesis_eq_primeCoreLedger m hmOdd,
    c2Fiber_center_log_eq_depth_add_primeCoreLedger m k hm]

end
end CarrySelfAdjointOperator
