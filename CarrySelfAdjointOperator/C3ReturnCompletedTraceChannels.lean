import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import CarrySelfAdjointOperator.C3MixedReturnTraceObstruction

/-!
# The completed trace channels seen and missed by camera return

This module audits the existing source and trace maps. The diagnostic pulses
are vectors in the existing ordinary/log-jet carrier, not replacement sources
for a native moment construction. Canonical head and tail identities are reused.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
open CanonicalC3AllCutoffMixedSourceHilbert

noncomputable section
set_option autoImplicit false

/-- Every block-initial coordinate is absent from the actual value head. -/
theorem c3ValueHead_add_blockInitial
    (M k : ℕ) (state : CanonicalCompletedC3HilbertState) (a b : ℂ) :
    valueHeadReadout M (state + (lp.single 2 (3 * k) a, lp.single 2 (3 * k) b)) =
      valueHeadReadout M state := by
  unfold valueHeadReadout
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have h1 : 3 * k ≠ 3 * m + 1 := by omega
  have h2 : 3 * k ≠ 3 * m + 2 := by omega
  simp [h1, h2]

/-- The same missing coordinate occurs in the independently retained log jet. -/
theorem c3LogJetHead_add_blockInitial
    (M k : ℕ) (state : CanonicalCompletedC3HilbertState) (a b : ℂ) :
    logJetHeadReadout M (state + (lp.single 2 (3 * k) a, lp.single 2 (3 * k) b)) =
      logJetHeadReadout M state := by
  unfold logJetHeadReadout
  apply Finset.sum_congr rfl
  intro m _
  have h1 : 3 * k ≠ 3 * m + 1 := by omega
  have h2 : 3 * k ≠ 3 * m + 2 := by omega
  simp [h1, h2]

/-- At one complete C3 block, the ordinary trace sees the last two gradients. -/
theorem c3ValueHead_one (state : CanonicalCompletedC3HilbertState) :
    valueHeadReadout 1 state = 1 + state.1 2 - state.1 1 := by
  simp [valueHeadReadout]
  ring

theorem c3LogJetHead_one (state : CanonicalCompletedC3HilbertState) :
    logJetHeadReadout 1 state = state.2 2 - state.2 1 := by
  simp [logJetHeadReadout]

/-- The faithful six-camera packing of this same Green port reads only g_1. -/
theorem c3GreenPort_returnReadout
    (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    sixCameraReturnReadout (canonicalC3SixCameraSourceMap (greenPort 3 s state)) =
      ((Real.sqrt 278 / 3 : ℝ) : ℂ) * state.1 1 := by
  rw [sixCameraReturnReadout_sourceMap]
  rfl

/-- Exact bridge to the actual canonical source, with no relabeling of resultants. -/
theorem c3GreenPort_canonicalPrefix_source (z : ℂ) :
    canonicalC3SixCameraSourceMap
        (greenPort 3 (operatorHeightParameter z)
          (canonicalCompletedC3HilbertPrefixState (operatorHeightParameter z) 3)) =
      canonicalCompletedC3SixCameraSource z := by
  rw [canonicalC3AllCutoffGreenPort_prefix_eq]
  unfold canonicalCompletedC3SixCameraSource
  rw [canonicalCompletedOperatorC3State_eq_greenBoundaryPair]

/-- A last-coordinate pulse is visible to the value trace at every nonempty cutoff. -/
theorem c3ValueHead_add_lastPulse
    (M : ℕ) (hM : 0 < M) (state : CanonicalCompletedC3HilbertState) (a : ℂ) :
    valueHeadReadout M (state + (lp.single 2 2 a, 0)) =
      valueHeadReadout M state + a := by
  have h1 (m : ℕ) : (lp.single 2 2 a : CarryVerticalL2) (3 * m + 1) = 0 := by
    apply lp.single_apply_ne
    omega
  have h2 (m : ℕ) : (lp.single 2 2 a : CarryVerticalL2) (3 * m + 2) =
      if m = 0 then a else 0 := by
    by_cases hm : m = 0
    · subst m
      simp
    · rw [lp.single_apply_ne]
      · simp [hm]
      · omega
  unfold valueHeadReadout
  simp only [Prod.fst_add, lp.coeFn_add, Pi.add_apply]
  simp_rw [h1, h2]
  simp_rw [show ∀ x y t : ℂ, (x + t) - (y + 0) = (x - y) + t by intros; ring]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_range.mpr hM]
  ring

/-- The log jet is not replaced when varying the ordinary last coordinate. -/
theorem c3LogJetHead_add_ordinaryPulse
    (M n : ℕ) (state : CanonicalCompletedC3HilbertState) (a : ℂ) :
    logJetHeadReadout M (state + (lp.single 2 n a, 0)) =
      logJetHeadReadout M state := by
  simp [logJetHeadReadout]

/-- Both pulses changing g_0 or g_2 have zero mixed return readout. -/
theorem c3GreenPort_returnReadout_add_pulse
    (s : ℂ) (state : CanonicalCompletedC3HilbertState)
    (n : ℕ) (hn : n ≠ 1) (a b : ℂ) :
    sixCameraReturnReadout (canonicalC3SixCameraSourceMap
        (greenPort 3 s (state + (lp.single 2 n a, lp.single 2 n b)))) =
      sixCameraReturnReadout (canonicalC3SixCameraSourceMap (greenPort 3 s state)) := by
  rw [c3GreenPort_returnReadout, c3GreenPort_returnReadout]
  simp [hn]

/-- No function of the mixed return can reconstruct even the value head,
including any fixed exact tail. This is an ambient statement, not a
counterexample to scalar camera universality on the canonical family. -/
theorem not_c3CompletedValue_factors_through_mixedReturn
    (s : ℂ) (M : ℕ) (hM : 0 < M) (valueTail : ℂ) :
    ¬ ∃ B : ℂ → ℂ, ∀ state : CanonicalCompletedC3HilbertState,
      valueHeadReadout M state + valueTail =
        B (sixCameraReturnReadout
          (canonicalC3SixCameraSourceMap (greenPort 3 s state))) := by
  rintro ⟨B, hB⟩
  have h0 := hB 0
  have h1 := hB ((0 : CanonicalCompletedC3HilbertState) + (lp.single 2 2 1, 0))
  rw [c3ValueHead_add_lastPulse M hM] at h1
  have hread := c3GreenPort_returnReadout_add_pulse s 0 2 (by omega) 1 0
  simp only [lp.single_zero] at hread
  rw [hread, ← h0] at h1
  have : (1 : ℂ) = 0 := by linear_combination h1
  exact one_ne_zero this

/-- Matrix coordinates of a real ordinary pulse in the last C3 coordinate:
camera 4 carries its radial leg and camera 7 its horizontal leg. -/
theorem c3GreenPort_lastPulse_coordinates (s : ℂ) (a : ℝ) :
    greenPort 3 s ((lp.single 2 2 (a : ℂ), 0) : CanonicalCompletedC3HilbertState) =
      (WithLp.toLp 2 ![0, 0,
          (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * a],
       WithLp.toLp 2 ![0, 0, (a : ℂ)]) := by
  apply Prod.ext
  all_goals
    ext i
    fin_cases i <;> simp [greenPort, lp.single_apply, Pi.single_apply]

/-- The complete A-return, not only its scalar projection, misses this pulse.
Whitening uses the existing G and no fitted scale. -/
theorem c3LastPulse_returnCompression_zero (s : ℂ) (a : ℝ) :
    cameraReturnCompression sixCameraGram sixCameraFirstMoment
        (cameraLogSlopeDiagonal sixCamera) *ᵥ
      (CFC.sqrt sixCameraGram *ᵥ
        ![0, 0, (3 : ℝ) ^ (-criticalDisplacement s.re) * a, 0, 0, a]) = 0 := by
  apply sixCameraReturnCompression_annihilates_cameraSixZero
  simp


/-- The exact trace difference after joining arbitrary retained tails. -/
theorem c3CompletedTrace_add_lastPulse
    (M : ℕ) (hM : 0 < M) (state : CanonicalCompletedC3HilbertState)
    (a valueTail logTail : ℂ) :
    (Complex.I * (logJetHeadReadout M (state + (lp.single 2 2 a, 0)) + logTail),
      valueHeadReadout M (state + (lp.single 2 2 a, 0)) + valueTail) =
    (Complex.I * (logJetHeadReadout M state + logTail),
      valueHeadReadout M state + valueTail) + (0, a) := by
  rw [c3ValueHead_add_lastPulse M hM, c3LogJetHead_add_ordinaryPulse]
  apply Prod.ext
  · simp
  · dsimp
    ring

/-- The original four-channel completion is read from the existing
ordinary/log-jet prefix. This is a reuse of the two cutoff identities. -/
theorem c3CanonicalPrefix_completedTrace
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (Complex.I * (logJetHeadReadout M
        (canonicalCompletedC3HilbertPrefixState (operatorHeightParameter z) (3 * M)) +
        canonicalC3LogJetCutoffTail M (operatorHeightParameter z)),
      valueHeadReadout M
        (canonicalCompletedC3HilbertPrefixState (operatorHeightParameter z) (3 * M)) +
        realCpBracketCutoffTail 3 M (operatorHeightParameter z)) =
    (canonicalCompletedC3RawHeightCompanion z, canonicalCompletedC3RawHeightValue z) := by
  rw [canonicalC3AllCutoffValueHeadReadout_prefix_eq,
    canonicalC3AllCutoffLogJetHeadReadout_prefix_eq]
  exact Prod.ext
    (canonicalCompletedC3AllCutoffOnePointState_completedCompanion_eq M hz)
    (canonicalCompletedC3AllCutoffOnePointState_completedValue_eq M hz)

/-- Varying the first ordinary and log-jet coordinates changes no completed
scalar trace, at any cutoff. Tails remain explicit and unchanged. -/
theorem c3CanonicalPrefix_initialPulse_completedTrace
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) (a b : ℂ) :
    let state := canonicalCompletedC3HilbertPrefixState (operatorHeightParameter z) (3 * M)
    (Complex.I * (logJetHeadReadout M (state + (lp.single 2 0 a, lp.single 2 0 b)) +
        canonicalC3LogJetCutoffTail M (operatorHeightParameter z)),
      valueHeadReadout M (state + (lp.single 2 0 a, lp.single 2 0 b)) +
        realCpBracketCutoffTail 3 M (operatorHeightParameter z)) =
    (canonicalCompletedC3RawHeightCompanion z, canonicalCompletedC3RawHeightValue z) := by
  dsimp only
  rw [c3ValueHead_add_blockInitial M 0, c3LogJetHead_add_blockInitial M 0]
  exact c3CanonicalPrefix_completedTrace M hz

/-- The actual canonical one-block value has a non-return channel g_2 and
the exact tail. The coefficient of return is fixed by the original Gram. -/
theorem c3CanonicalRawValue_eq_return_add_cameraSeven_tail
    {z : ℂ} (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightValue z =
      1 - ((3 / Real.sqrt 278 : ℝ) : ℂ) *
        sixCameraReturnReadout (canonicalCompletedC3SixCameraSource z) +
      positiveDirichletGradient (operatorHeightParameter z) 2 +
      realCpBracketCutoffTail 3 1 (operatorHeightParameter z) := by
  have ht := congrArg Prod.snd (c3CanonicalPrefix_completedTrace 1 hz)
  dsimp only [Prod.snd] at ht
  rw [← ht, c3ValueHead_one, sixCameraReturnReadout_canonicalSource]
  simp only [canonicalCompletedC3HilbertPrefixState,
    canonicalCompletedC3DirichletGradientPrefixState_apply]
  simp only [if_pos (show 2 < 3 * 1 by decide), if_pos (show 1 < 3 * 1 by decide)]
  have hs : Real.sqrt 278 ≠ 0 := by positivity
  have hc : ((3 / Real.sqrt 278 : ℝ) : ℂ) * ((Real.sqrt 278 / 3 : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [← mul_assoc, hc]
  ring

/-- The first surviving boundary terms for two ordinary last-coordinate
variations. They include both cross terms; the pulse-pulse term is exactly
zero because their companion coordinates are zero. -/
theorem c3CompletedTrace_lastPulse_boundaryDifference
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (x y : CanonicalCompletedC3HilbertState)
    (a b vTailX lTailX vTailY lTailY : ℂ) :
    let tx := (Complex.I * (logJetHeadReadout M x + lTailX),
      valueHeadReadout M x + vTailX)
    let ty := (Complex.I * (logJetHeadReadout N y + lTailY),
      valueHeadReadout N y + vTailY)
    NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ)
      (Complex.I * (logJetHeadReadout M (x + (lp.single 2 2 a, 0)) + lTailX),
        valueHeadReadout M (x + (lp.single 2 2 a, 0)) + vTailX)
      (Complex.I * (logJetHeadReadout N (y + (lp.single 2 2 b, 0)) + lTailY),
        valueHeadReadout N (y + (lp.single 2 2 b, 0)) + vTailY) -
      NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ) tx ty =
      conj a * ty.1 - conj tx.1 * b := by
  dsimp only
  rw [c3CompletedTrace_add_lastPulse M hM,
    c3CompletedTrace_add_lastPulse N hN]
  simp [NativeCarrySpectralWeyl.Boundary.greenForm, RCLike.inner_apply,
    map_add, map_mul]
  ring


/-- No finite multiplicative bound transports this return energy into even
the ordinary one-block trace variation on real Green-port coefficients. -/
theorem not_c3TraceVariation_bounded_by_returnEnergy (s : ℂ) :
    ¬ ∃ C : ℝ, ∀ x : Fin 3 → ℝ,
      (x 2 - x 1) ^ 2 ≤ C *
        ∑ i : Fin 6,
          (cameraReturnCompression sixCameraGram sixCameraFirstMoment
            (cameraLogSlopeDiagonal sixCamera) *ᵥ
              (CFC.sqrt sixCameraGram *ᵥ
                ![(3 : ℝ) ^ (-criticalDisplacement s.re) * x 0,
                  (3 : ℝ) ^ (-criticalDisplacement s.re) * x 1,
                  (3 : ℝ) ^ (-criticalDisplacement s.re) * x 2,
                  x 0, x 1, x 2])) i ^ 2 := by
  rintro ⟨C, hC⟩
  let x : Fin 3 → ℝ := ![0, 0, 1]
  have hx0 : x 0 = 0 := rfl
  have hx1 : x 1 = 0 := rfl
  have hx2 : x 2 = 1 := rfl
  have h := hC x
  have hzero := c3LastPulse_returnCompression_zero s 1
  simp only [hx0, hx1, hx2, mul_zero, mul_one, sub_zero, one_pow] at h
  simp only [mul_one] at hzero
  rw [hzero] at h
  norm_num at h

/-- The g_0 pulse retains its ordinary/radial Green relation. Its six-camera
image has the same horizontal camera-5 coordinate as the original source. -/
theorem c3GreenPort_initialPulse_coordinates (s a : ℂ) :
    greenPort 3 s ((lp.single 2 0 a, 0) : CanonicalCompletedC3HilbertState) =
      (WithLp.toLp 2 ![
          (((3 : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) * a, 0, 0],
       WithLp.toLp 2 ![a, 0, 0]) := by
  apply Prod.ext
  all_goals
    ext i
    fin_cases i <;> simp [greenPort, lp.single_apply, Pi.single_apply]

/-- A nonzero initial pulse, invisible to both heads, has positive energy
under the very same injective Gamma used in the canonical sewing. -/
theorem c3InitialPulse_gamma_energy_pos
    (z : ℂ) (hz : z.im ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    0 < ‖carryGammaComplexState z hz
      (canonicalC3SixCameraSourceMap
        (greenPort 3 (operatorHeightParameter z)
          ((lp.single 2 0 a, 0) : CanonicalCompletedC3HilbertState)))‖ ^ 2 := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro h
  change (carryGammaSource z hz _ : WithLp 2 (NaimarkSpace × NaimarkSpace)) = 0 at h
  have hsource : canonicalC3SixCameraSourceMap
      (greenPort 3 (operatorHeightParameter z)
        ((lp.single 2 0 a, 0) : CanonicalCompletedC3HilbertState)) = 0 := by
    apply carryGammaSource_injective z hz
    simpa only [map_zero] using h
  have hp : greenPort 3 (operatorHeightParameter z)
      ((lp.single 2 0 a, 0) : CanonicalCompletedC3HilbertState) = 0 :=
    canonicalC3SixCameraSourceMap_injective (by simpa using hsource)
  have hc := congrArg (fun x : FiniteC3GreenPortCarrier 3 => x.2 0) hp
  simpa [greenPort] using ha hc

/-- This nonzero test is an actual initial coefficient of the canonical
family, rather than an assumed scalar or a fitted normalization. -/
theorem c3CanonicalInitialPulse_gamma_energy_pos
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    0 < ‖carryGammaComplexState z hz
      (canonicalC3SixCameraSourceMap
        (greenPort 3 (operatorHeightParameter z)
          ((lp.single 2 0 (positiveDirichletGradient (operatorHeightParameter z) 0), 0) :
            CanonicalCompletedC3HilbertState)))‖ ^ 2 := by
  apply c3InitialPulse_gamma_energy_pos
  exact positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip hs 0


/-- A diagnostic removal of the actual g_2 coefficient: return is unchanged
but the completed trace changes by a provably nonzero amount. The modified
vector is not asserted to be another canonical state. -/
theorem c3CanonicalCameraSeven_traceMismatch
    (M : ℕ) (hM : 0 < M) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    let s := operatorHeightParameter z
    let state := canonicalCompletedC3HilbertPrefixState s (3 * M)
    let modified := state + (lp.single 2 2 (-positiveDirichletGradient s 2), 0)
    sixCameraReturnReadout (canonicalC3SixCameraSourceMap (greenPort 3 s modified)) =
      sixCameraReturnReadout (canonicalC3SixCameraSourceMap (greenPort 3 s state)) ∧
    (Complex.I * (logJetHeadReadout M modified + canonicalC3LogJetCutoffTail M s),
      valueHeadReadout M modified + realCpBracketCutoffTail 3 M s) =
      (canonicalCompletedC3RawHeightCompanion z,
        canonicalCompletedC3RawHeightValue z - positiveDirichletGradient s 2) ∧
    canonicalCompletedC3RawHeightValue z - positiveDirichletGradient s 2 ≠
      canonicalCompletedC3RawHeightValue z := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lp.single_zero] using
      c3GreenPort_returnReadout_add_pulse (operatorHeightParameter z)
        (canonicalCompletedC3HilbertPrefixState (operatorHeightParameter z) (3 * M))
        2 (by omega) (-positiveDirichletGradient (operatorHeightParameter z) 2) 0
  · rw [c3CompletedTrace_add_lastPulse M hM, c3CanonicalPrefix_completedTrace M hz]
    simp [sub_eq_add_neg]
  · intro h
    exact positiveDirichletGradient_ne_zero_of_mem_genuineCriticalStrip hz 2
      (sub_eq_self.mp h)

end
end CarrySelfAdjointOperator
