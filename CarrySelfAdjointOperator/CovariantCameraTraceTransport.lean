import CarrySelfAdjointOperator.C3GammaCameraTraceObstruction
import CarrySelfAdjointOperator.CenteredCameraCutoffConvergence

/-!
# Covariant readouts and the independent C3 log-jet trace

The existing return/variance analysis recovers the geometrically fixed value
dual. Applying that same analysis separately to the two already existing
ordinary/log-jet coordinates recovers the completed raw trace at every cutoff.

The ordinary Green port, even after arbitrary post-processing, does not
determine the independent log-jet trace on the ambient enriched carrier.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
open CanonicalC3AllCutoffMixedSourceHilbert Filter

noncomputable section
set_option autoImplicit false

local notation "A₆" => cameraReturnCompression sixCameraGram sixCameraFirstMoment
  (cameraLogSlopeDiagonal sixCamera)
local notation "S₆" => CFC.sqrt sixCameraVariance
local notation "Q₆" =>
  (![(9/139 : ℝ), 9/278, -3/139, 0, -9/278, 1/42] : Fin 6 → ℝ)

/-- Transporting the observer as well as the coefficients preserves the
actual value trace, using both intrinsic positive analysis channels. -/
theorem sixCamera_return_variance_valueTrace (c : Fin 6 → ℝ) :
    (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
        (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ c)) +
      (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
        (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ c)) = c 5 - c 4 := by
  rw [sixCamera_return_variance_source_gram, sixCamera_valueTrace_dual_readout]

/-- Scalar readout of the existing analysis, in both complex quadratures.
The coefficients and metric are unchanged; no spectral state is defined. -/
def sixCameraReturnVarianceTrace (c : Fin 6 → ℂ) : ℂ :=
  ((A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
      (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ fun i => (c i).re)) +
    (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
      (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ fun i => (c i).re)) : ℝ) +
  Complex.I *
    (((A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
        (A₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ fun i => (c i).im)) +
      (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ Q₆)) ⬝ᵥ
        (S₆ *ᵥ (CFC.sqrt sixCameraGram *ᵥ fun i => (c i).im)) : ℝ) : ℂ)

theorem sixCameraReturnVarianceTrace_eq (c : Fin 6 → ℂ) :
    sixCameraReturnVarianceTrace c = c 5 - c 4 := by
  unfold sixCameraReturnVarianceTrace
  rw [sixCamera_return_variance_valueTrace, sixCamera_return_variance_valueTrace]
  apply Complex.ext <;> simp

/-- Literal coefficient packing of the current Green port at one complete
block; this fixes the relation with the source already used by Gamma. -/
theorem sixCameraReturnVarianceTrace_greenPort
    (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    let p := greenPort 3 s state
    sixCameraReturnVarianceTrace ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2] =
      state.1 2 - state.1 1 := by
  dsimp only
  rw [sixCameraReturnVarianceTrace_eq]
  rfl

/-- Apply the same six-camera analysis to each complete block of a supplied
existing vertical coordinate. Ordinary and log-jet inputs remain distinct. -/
def c3ReturnVarianceHeadReadout (M : ℕ) (s : ℂ) (f : CarryVerticalL2) : ℂ :=
  ∑ m ∈ Finset.range M,
    sixCameraReturnVarianceTrace
      ![(((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * f (3*m),
        (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * f (3*m+1),
        (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * f (3*m+2),
        f (3*m), f (3*m+1), f (3*m+2)]

theorem c3ReturnVarianceHeadReadout_eq
    (M : ℕ) (s : ℂ) (f : CarryVerticalL2) :
    c3ReturnVarianceHeadReadout M s f =
      ∑ m ∈ Finset.range M, (f (3*m+2) - f (3*m+1)) := by
  unfold c3ReturnVarianceHeadReadout
  apply Finset.sum_congr rfl
  intro m _
  rw [sixCameraReturnVarianceTrace_eq]
  rfl

theorem c3ReturnVariance_valueHead
    (M : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    1 + c3ReturnVarianceHeadReadout M s state.1 = valueHeadReadout M state := by
  rw [c3ReturnVarianceHeadReadout_eq]
  rfl

theorem c3ReturnVariance_logJetHead
    (M : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    c3ReturnVarianceHeadReadout M s state.2 = logJetHeadReadout M state := by
  rw [c3ReturnVarianceHeadReadout_eq]
  rfl

/-- Complete raw value and companion are recovered in every cutoff by
retaining both source coordinates, both tails, and the original seed. -/
theorem c3CanonicalPrefix_returnVarianceCompletedTrace
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    let state := canonicalCompletedC3HilbertPrefixState s (3*M)
    (Complex.I * (c3ReturnVarianceHeadReadout M s state.2 +
        canonicalC3LogJetCutoffTail M s),
      1 + c3ReturnVarianceHeadReadout M s state.1 +
        realCpBracketCutoffTail 3 M s) =
      (canonicalCompletedC3RawHeightCompanion z,
        canonicalCompletedC3RawHeightValue z) := by
  dsimp only
  rw [c3ReturnVariance_logJetHead, c3ReturnVariance_valueHead]
  exact c3CanonicalPrefix_completedTrace M hz

/-- The ordinary Green port projects away the independently retained log
jet before the faithful six-camera packing is applied. -/
theorem c3GreenPort_add_logJet
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState)
    (jet : CarryVerticalL2) :
    greenPort N s (state + (0, jet)) = greenPort N s state := by
  simp [greenPort]

theorem c3ValueHead_add_logJet
    (M : ℕ) (state : CanonicalCompletedC3HilbertState) (jet : CarryVerticalL2) :
    valueHeadReadout M (state + (0, jet)) = valueHeadReadout M state := by
  simp [valueHeadReadout]

theorem c3LogJetHead_add_lastLogJet
    (M : ℕ) (hM : 0 < M) (state : CanonicalCompletedC3HilbertState) (a : ℂ) :
    logJetHeadReadout M (state + (0, lp.single 2 2 a)) =
      logJetHeadReadout M state + a := by
  have h1 (m : ℕ) : (lp.single 2 2 a : CarryVerticalL2) (3*m+1) = 0 := by
    apply lp.single_apply_ne
    omega
  have h2 (m : ℕ) : (lp.single 2 2 a : CarryVerticalL2) (3*m+2) =
      if m = 0 then a else 0 := by
    by_cases hm : m = 0
    · subst m
      simp
    · rw [lp.single_apply_ne]
      · simp [hm]
      · omega
  unfold logJetHeadReadout
  simp only [Prod.snd_add, lp.coeFn_add, Pi.add_apply]
  simp_rw [h1, h2]
  simp_rw [show ∀ x y t : ℂ, (x+t)-(y+0) = (x-y)+t by intros; ring]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_range.mpr hM]

/-- First surviving trace term for a pure log-jet pulse, with arbitrary
retained value/log tails. -/
theorem c3CompletedTrace_add_lastLogJet
    (M : ℕ) (hM : 0 < M) (state : CanonicalCompletedC3HilbertState)
    (a valueTail logTail : ℂ) :
    (Complex.I * (logJetHeadReadout M (state + (0, lp.single 2 2 a)) + logTail),
      valueHeadReadout M (state + (0, lp.single 2 2 a)) + valueTail) =
      (Complex.I * (logJetHeadReadout M state + logTail),
        valueHeadReadout M state + valueTail) + (Complex.I * a, 0) := by
  rw [c3LogJetHead_add_lastLogJet M hM, c3ValueHead_add_logJet]
  apply Prod.ext <;> dsimp <;> ring

/-- No post-processing of the current ordinary source recovers the
independent completed companion on the ambient enriched carrier.
This includes whitening, centering and any fixed Gamma evaluation. -/
theorem not_c3CompletedCompanion_factors_through_processed_source
    {D : Type*} (T : RealifiedCameraComplexification → D)
    (s : ℂ) (M : ℕ) (hM : 0 < M) (logTail : ℂ) :
    ¬ ∃ B : D → ℂ, ∀ state : CanonicalCompletedC3HilbertState,
      Complex.I * (logJetHeadReadout M state + logTail) =
        B (T (canonicalC3SixCameraSourceMap (greenPort 3 s state))) := by
  rintro ⟨B, hB⟩
  have h0 := hB 0
  have h1 := hB ((0 : CanonicalCompletedC3HilbertState) + (0, lp.single 2 2 1))
  rw [c3LogJetHead_add_lastLogJet M hM, c3GreenPort_add_logJet, ← h0] at h1
  have hI : Complex.I = 0 := by linear_combination h1
  exact Complex.I_ne_zero hI

/-- Both cross terms of the polarized boundary variation survive.
The log-jet/log-jet pulse term is zero because the value is unchanged. -/
theorem c3CompletedTrace_lastLogJet_boundaryDifference
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (x y : CanonicalCompletedC3HilbertState)
    (a b vx vy jx jy : ℂ) :
    (Complex.I * (logJetHeadReadout M (x + (0, lp.single 2 2 a)) + jx) *
          conj (valueHeadReadout N (y + (0, lp.single 2 2 b)) + vy) -
        (valueHeadReadout M (x + (0, lp.single 2 2 a)) + vx) *
          conj (Complex.I * (logJetHeadReadout N (y + (0, lp.single 2 2 b)) + jy))) -
      (Complex.I * (logJetHeadReadout M x + jx) *
          conj (valueHeadReadout N y + vy) -
        (valueHeadReadout M x + vx) *
          conj (Complex.I * (logJetHeadReadout N y + jy))) =
      Complex.I * a * conj (valueHeadReadout N y + vy) +
        Complex.I * (valueHeadReadout M x + vx) * conj b := by
  rw [c3LogJetHead_add_lastLogJet M hM, c3LogJetHead_add_lastLogJet N hN,
    c3ValueHead_add_logJet, c3ValueHead_add_logJet]
  simp only [map_mul, map_add, Complex.conj_I]
  ring

/-- On the canonical curve the retained log jet is determined by the
derivative of the value readout. The ambient non-factorization theorem
does not discard this additional dependence on the parameter. -/
theorem hasDerivAt_c3ReturnVariance_valueHead_eq_neg_logJet
    (M : ℕ) (s : ℂ) :
    HasDerivAt
      (fun u : ℂ => 1 + c3ReturnVarianceHeadReadout M u
        (canonicalCompletedC3HilbertPrefixState u (3*M)).1)
      (-c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).2) s := by
  have hfun : (fun u : ℂ => 1 + c3ReturnVarianceHeadReadout M u
      (canonicalCompletedC3HilbertPrefixState u (3*M)).1) =
      finiteBracketedDirichletChart 3 M := by
    funext u
    rw [c3ReturnVariance_valueHead, canonicalC3AllCutoffValueHeadReadout_prefix_eq]
  rw [hfun, c3ReturnVariance_logJetHead,
    canonicalC3AllCutoffLogJetHeadReadout_prefix_eq]
  exact hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s

/-- The same derivative identification includes the exact differentiated
tail. No limit or new moment recurrence is inserted. -/
theorem hasDerivAt_c3ReturnVariance_completedValue_eq_neg_logJet
    (M : ℕ) {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    HasDerivAt
      (fun u : ℂ => 1 + c3ReturnVarianceHeadReadout M u
        (canonicalCompletedC3HilbertPrefixState u (3*M)).1 +
          realCpBracketCutoffTail 3 M u)
      (-(c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).2 +
          canonicalC3LogJetCutoffTail M s)) s := by
  exact ((hasDerivAt_c3ReturnVariance_valueHead_eq_neg_logJet M s).add
    (hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M hs)).congr_deriv (by ring)

/-- The analysis readout returns exactly the already existing completed
bracket TFVD pair, before chart and archimedean dressing. -/
theorem c3ReturnVariance_completedReadouts_eq_bracketTfvd
    (M : ℕ) (s : ℂ) :
    (1 + c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).1 +
          realCpBracketCutoffTail 3 M s,
      c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).2 +
          canonicalC3LogJetCutoffTail M s) =
      ((canonicalC3BracketTfvdCompletionState M s).valueReadout,
        (canonicalC3BracketTfvdCompletionState M s).logJetReadout) := by
  rw [c3ReturnVariance_valueHead, c3ReturnVariance_logJetHead,
    canonicalC3AllCutoffValueHeadReadout_prefix_eq,
    canonicalC3AllCutoffLogJetHeadReadout_prefix_eq]
  have h := canonicalC3BracketTfvdCompletionState_transport_components M s
  change (_, _) =
    ((canonicalC3BracketTfvdCompletionState M s).transport.valueReadout +
      realCpBracketCutoffTail 3 M s,
     (canonicalC3BracketTfvdCompletionState M s).transport.logJetReadout +
      canonicalC3LogJetCutoffTail M s)
  rw [h.1, h.2.1]

/-- A finite, exact witness: a unit log-jet pulse has the identical ordinary
source but changes the companion by I. This concerns ambient states,
not two points of the canonical analytic curve. -/
theorem c3LogJetPulse_sameSource_differentCompanion (s : ℂ) :
    canonicalC3SixCameraSourceMap
        (greenPort 3 s ((0 : CanonicalCompletedC3HilbertState) +
          (0, lp.single 2 2 1))) =
      canonicalC3SixCameraSourceMap (greenPort 3 s 0) ∧
    Complex.I * logJetHeadReadout 1
        ((0 : CanonicalCompletedC3HilbertState) + (0, lp.single 2 2 1)) -
      Complex.I * logJetHeadReadout 1 0 = Complex.I := by
  constructor
  · rw [c3GreenPort_add_logJet]
  · rw [c3LogJetHead_add_lastLogJet 1 (by omega)]
    ring

/-- Reuse the existing chart and completion dressing after the two
analysis readouts have been recovered. This reaches the same (F,-F')
pair, without asserting any Gram identification. -/
theorem c3ReturnVariance_dressedTrace_eq_F_negFprime
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    let state := canonicalCompletedC3HilbertPrefixState s (3*M)
    let r : ℂ × ℂ :=
      (1 + c3ReturnVarianceHeadReadout M s state.1 + realCpBracketCutoffTail 3 M s,
        c3ReturnVarianceHeadReadout M s state.2 + canonicalC3LogJetCutoffTail M s)
    (nativeXiCompletionFactor z * (r.1 / cpChartFactor 3 s),
      nativeXiCompletionBoundaryCompanion z * (r.1 / cpChartFactor 3 s) +
        nativeXiCompletionFactor z *
          (Complex.I * ((r.2 * cpChartFactor 3 s +
            r.1 * deriv (cpChartFactor 3) s) / cpChartFactor 3 s ^ 2))) =
      (completedNativeOperatorCharacteristic z,
        -deriv completedNativeOperatorCharacteristic z) := by
  let s := operatorHeightParameter z
  let dress : ℂ × ℂ → ℂ × ℂ := fun r =>
    (nativeXiCompletionFactor z * (r.1 / cpChartFactor 3 s),
      nativeXiCompletionBoundaryCompanion z * (r.1 / cpChartFactor 3 s) +
        nativeXiCompletionFactor z *
          (Complex.I * ((r.2 * cpChartFactor 3 s +
            r.1 * deriv (cpChartFactor 3) s) / cpChartFactor 3 s ^ 2)))
  change dress
    (1 + c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).1 +
          realCpBracketCutoffTail 3 M s,
      c3ReturnVarianceHeadReadout M s
        (canonicalCompletedC3HilbertPrefixState s (3*M)).2 +
          canonicalC3LogJetCutoffTail M s) = _
  rw [c3ReturnVariance_completedReadouts_eq_bracketTfvd]
  exact canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz

/-- The same witness reaches the existing Gamma field at any independently
chosen nonreal resolvent parameter. No new field or spectral parameter is
introduced, and the companion difference remains exactly I. -/
theorem c3LogJetPulse_sameGamma_differentCompanion
    (s lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryGammaSource lambda hlambda
        (canonicalC3SixCameraSourceMap
          (greenPort 3 s ((0 : CanonicalCompletedC3HilbertState) +
            (0, lp.single 2 2 1)))) =
      carryGammaSource lambda hlambda
        (canonicalC3SixCameraSourceMap (greenPort 3 s 0)) ∧
    Complex.I * logJetHeadReadout 1
        ((0 : CanonicalCompletedC3HilbertState) + (0, lp.single 2 2 1)) -
      Complex.I * logJetHeadReadout 1 0 = Complex.I := by
  have h := c3LogJetPulse_sameSource_differentCompanion s
  exact ⟨congrArg (carryGammaSource lambda hlambda) h.1, h.2⟩

/-- Even a parameter-dependent choice of complex linear isometry cannot
repair the diagonal of the current Gamma Gram. The original local mismatch
is reused, with its full source and normalization unchanged. -/
theorem canonicalC3Gamma_isometricTransport_ne_native_diagonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    ∀ᶠ t : ℝ in nhds 0, ∀ hz : (Complex.I * (t : ℂ)).im ≠ 0,
      ∀ U : CarryGammaComplexNaimark →ₗᵢ[ℂ] E,
        inner ℂ
            (U (canonicalCompletedC3NormalizedPolarizedGammaState
              (Complex.I * (t : ℂ)) hz))
            (U (canonicalCompletedC3NormalizedPolarizedGammaState
              (Complex.I * (t : ℂ)) hz)) ≠
          canonicalCompletedNativePolarizedDslopeKernel
            (Complex.I * (t : ℂ)) (Complex.I * (t : ℂ)) := by
  filter_upwards [canonicalC3NormalizedGamma_ne_native_near_imaginary_center] with t ht
  intro hz U
  rw [U.inner_map_map,
    ← canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_inner]
  exact ht hz

end
end CarrySelfAdjointOperator
