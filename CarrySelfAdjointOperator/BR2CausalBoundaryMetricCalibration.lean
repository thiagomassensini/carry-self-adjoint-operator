import CarrySelfAdjointOperator.BR2CausalGreenResponseTransport
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration

/-!
# Native mass calibration with arbitrary causal boundary return

The existing BR2 response solves the prescribed three-cell source equation.
The return map changes both boundary seeds while leaving that equation fixed.
Here a single center coordinate bounds the norm of every solution, including
all response/return cross terms. At the canonical C3 ratio this already
exceeds the zeroth native moment. This concerns literal incidence responses
in the existing vertical metric, not a different native source or readout.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera NativeCarrySpectralWeyl.Camera
open scoped lp

noncomputable section
set_option autoImplicit false

/-- One interior bracket coordinate is bounded by the full state norm. -/
theorem carryWeightedVerticalCenteredBracket_norm_apply_le
    (q : ℝ) (hq : 0 < q) (x : CarryVerticalL2) (n : ℕ) :
    ‖carryWeightedVerticalCenteredBracket q x (n + 1)‖ ≤
      (q⁻¹ + 2 + q) * ‖x‖ := by
  rw [carryWeightedVerticalCenteredBracket_succ]
  calc
    ‖(q : ℂ)⁻¹ * x (n + 2) - 2 * x (n + 1) + (q : ℂ) * x n‖ ≤
        ‖(q : ℂ)⁻¹ * x (n + 2)‖ + ‖2 * x (n + 1)‖ + ‖(q : ℂ) * x n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = q⁻¹ * ‖x (n + 2)‖ + 2 * ‖x (n + 1)‖ + q * ‖x n‖ := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    _ ≤ q⁻¹ * ‖x‖ + 2 * ‖x‖ + q * ‖x‖ := by
      gcongr <;> exact lp.norm_apply_le_norm (by norm_num) x _
    _ = _ := by ring

/-- A deliberately coarse bound, derived from the fixed carry amplitude. -/
theorem canonicalBR2CarryAmplitudeRatio_three_bracket_bound :
    (canonicalBR2CarryAmplitudeRatio 3)⁻¹ + 2 +
      canonicalBR2CarryAmplitudeRatio 3 ≤ 5 := by
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hq := canonicalBR2CarryAmplitudeRatio_lt_one hbase
  have hinv : (canonicalBR2CarryAmplitudeRatio 3)⁻¹ ≤ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    simp only [canonicalBR2CarryAmplitudeRatio, primeCarryAmplitudeRatio, inv_inv,
      Nat.cast_ofNat]
    nlinarith
  linarith

/-- The exclusive center coefficient alone gives a boundary-independent floor. -/
theorem br2C3CenterPivot_norm_ge_two_fifths
    (index : ℕ) (x : CarryVerticalL2)
    (hpivot : carryWeightedVerticalCenteredBracket
      (canonicalBR2CarryAmplitudeRatio 3) x (alignedCenter 3 index) = (-2 : ℂ)) :
    (2 / 5 : ℝ) ≤ ‖x‖ := by
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hcenter : alignedCenter 3 index = (3 * index + 2) + 1 := by
    simp [alignedCenter]
    omega
  have hn := carryWeightedVerticalCenteredBracket_norm_apply_le
    (canonicalBR2CarryAmplitudeRatio 3) (canonicalBR2CarryAmplitudeRatio_pos hbase)
    x (3 * index + 2)
  rw [← hcenter, hpivot] at hn
  norm_num at hn
  have hb := mul_le_mul_of_nonneg_right
    canonicalBR2CarryAmplitudeRatio_three_bracket_bound (norm_nonneg x)
  linarith

/-- Any solution of the literal C3 source equation has this norm floor. -/
theorem br2C3SourceSolution_norm_ge_two_fifths
    (index : ℕ) (x : CarryVerticalL2)
    (hsource : carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio 3) x =
      br2CameraBracketVerticalState 3 1 index) :
    (2 / 5 : ℝ) ≤ ‖x‖ := by
  apply br2C3CenterPivot_norm_ge_two_fifths index x
  rw [hsource, br2CameraBracketVerticalState_apply_alignedCenter
    (by norm_num) (by norm_num [mem_radiusSet_iff])]
  simp

/-- The first uncancelled source coordinate for any correctly calibrated
zeroth native jet. This is a necessary condition, not a supplied realization. -/
theorem nativeMassCalibratedState_br2C3CenterSourceDefect_ne_zero
    (index : ℕ) (x : CarryVerticalL2)
    (hmass : ‖x‖ ^ 2 = canonicalCompletedNativeLogDerivativeMoment 0) :
    carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio 3) x (alignedCenter 3 index) + 2 ≠ 0 := by
  intro hzero
  have hpivot : carryWeightedVerticalCenteredBracket
      (canonicalBR2CarryAmplitudeRatio 3) x (alignedCenter 3 index) = (-2 : ℂ) :=
    eq_neg_of_add_eq_zero_left hzero
  have hx := br2C3CenterPivot_norm_ge_two_fifths index x hpivot
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith [sq_nonneg (‖x‖ - 2 / 5)]

/-- The first native mass already disagrees with every solution of the
literal C3 source equation, uniformly in all boundary choices. -/
theorem br2C3SourceSolution_nativeMassDefect_gt
    (index : ℕ) (x : CarryVerticalL2)
    (hsource : carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio 3) x =
      br2CameraBracketVerticalState 3 1 index) :
    (39 / 400 : ℝ) <
      ‖x‖ ^ 2 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hx := br2C3SourceSolution_norm_ge_two_fifths index x hsource
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith [sq_nonneg (‖x‖ - 2 / 5)]

/-- The existing response plus its full two-seed return cannot calibrate
the central native Gram entry. The norm is taken after adding the vectors. -/
theorem canonicalBR2C3CausalResponseWithBoundary_nativeMassDefect_gt
    (index : ℕ) (boundary : ℂ × ℂ) :
    (39 / 400 : ℝ) <
      ‖br2CameraBracketCausalGreenResponseWithBoundary
        (canonicalBR2CarryAmplitudeRatio 3)
        (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported])).le
        (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported]))
        3 1 index boundary‖ ^ 2 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  apply br2C3SourceSolution_nativeMassDefect_gt index
  exact carryWeightedVerticalCenteredBracket_br2CausalGreenResponseWithBoundary
    (canonicalBR2CarryAmplitudeRatio 3)
    (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported]))
    (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported]))
    (by norm_num [IsSupported]) (by norm_num [mem_radiusSet_iff]) index boundary

/-- Both BR2 readouts cannot be supplied for the literal C3 response family
with arbitrary order-dependent boundary seeds in its current Hilbert metric. -/
theorem not_nonempty_canonicalBR2C3BoundaryResponse_momentCertificate
    (incidence : BR2CameraIncidence) (boundary : (ℕ ⊕ ℕ) → ℂ × ℂ) :
    ¬ Nonempty (BR2CenterLegGreenMomentCertificate incidence
      canonicalCompletedNativeLogDerivativeMoment
      (fun i => br2CameraBracketCausalGreenResponseWithBoundary
        (canonicalBR2CarryAmplitudeRatio 3)
        (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported])).le
        (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported]))
        3 1 (parityJetNumber i) (boundary i))) := by
  rintro ⟨certificate⟩
  have hgram := certificate.toComplexMomentKernel (Sum.inl 0) (Sum.inl 0)
  have hreal := congrArg (RCLike.re : ℂ → ℝ) hgram
  rw [inner_self_eq_norm_sq] at hreal
  simp only [greenWronskianMomentKernel, parityJetNumber, Nat.add_zero,
    Nat.mul_zero] at hreal
  change canonicalCompletedNativeLogDerivativeMoment 0 = _ at hreal
  have hgap := canonicalBR2C3CausalResponseWithBoundary_nativeMassDefect_gt
    0 (boundary (Sum.inl 0))
  linarith

end
end CarrySelfAdjointOperator
