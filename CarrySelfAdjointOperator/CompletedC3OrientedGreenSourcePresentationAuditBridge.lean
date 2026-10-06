import CarrySelfAdjointOperator.CompletedC3ConcreteRealAxisKernelCarrier
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSourceTrace
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity

/-!
# Audit of the existing oriented source and its Hilbert presentation

Retain the full weighted TFVD boundary through the existing bounded Green
synthesis. Repackaging the recovered ordinary/log-jet pair and the retained
real residual into the already available complex Hilbert presentation gives
exactly the old concrete state, not a new division-free Green witness.
No metric, source or scalar kernel is defined from a target coefficient.
-/

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open scoped lp
noncomputable section
set_option autoImplicit false

/-- Both weighted boundary coordinates survive raw Green analysis and its
existing bounded synthesis. No boundary coordinate is added here. -/
theorem canonicalCompletedGreenFrameSynthesis_preserves_weightedTrace
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalTrace q
      (canonicalCompletedGreenFrameSynthesis
        (canonicalCompletedGreenFrameAnalysisCLM x)) =
      carryWeightedVerticalTrace q x := by
  rw [canonicalCompletedGreenFrameSynthesis_analysis]

/-- The complete TFVD reconstruction of the recovered source includes the
boundary return, not only the curvature/Green leg. -/
theorem canonicalCompletedGreenFrameSynthesis_weightedTfvd_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    let y := canonicalCompletedGreenFrameSynthesis
      (canonicalCompletedGreenFrameAnalysisCLM x)
    carryVerticalL2WeightedGreen q (carryWeightedVerticalCenteredBracket q y) n +
      carryWeightedVerticalReturn q hqpos.le hq1 (carryWeightedVerticalTrace q y) n =
      x n := by
  dsimp only
  rw [canonicalCompletedGreenFrameSynthesis_analysis]
  exact carryWeightedVerticalTfvd_apply q hqpos hq1 x n

/-- Audit presentation using only the existing synthesis, Parseval analysis,
real residual complexification and standard orthogonal product. It is not
asserted to be isometric on the raw coefficient carrier. -/
def canonicalCompletedC3OrientedRecoveredHilbertPresentation
    (source : CanonicalCompletedC3OrientedGreenFrameCarrier) :
    CanonicalCompletedC3RealAxisPositiveCarrier :=
  let recovered := canonicalCompletedC3GreenFramePairSynthesis source.1
  WithLp.toLp 2
    (canonicalCompletedGreenFrameParsevalAnalysis recovered.1,
      WithLp.toLp 2
        (canonicalCompletedGreenFrameParsevalAnalysis recovered.2,
          RealHilbertComplexification.mk
            (WithLp.toLp 2 source.2 : CanonicalCompletedC3RealAxisResidualHilbert) 0))

/-- On the actual completed real-axis source, this natural presentation is
literally the already existing positive state. No sewing gate is used. -/
theorem canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing
    (z : ℂ) :
    canonicalCompletedC3OrientedRecoveredHilbertPresentation
      (canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z) =
      canonicalCompletedC3RealAxisPositiveState z := by
  unfold canonicalCompletedC3OrientedRecoveredHilbertPresentation
    canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex
    canonicalCompletedC3RealAxisOrientedGreenFrameState
    canonicalCompletedC3OrientedGreenFrameState
  rw [canonicalCompletedC3GreenFramePairSynthesis_intertwiner]
  rfl

/-- Applying the unchanged completed normalization factor does not escape
the old concrete candidate. This is an equality of states, not a new
positive-kernel or division-free assertion. -/
theorem canonicalCompletedC3OrientedRecoveredHilbertPresentation_dressed_eq_existing
    (z : ℂ) :
    (((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z) •
      canonicalCompletedC3OrientedRecoveredHilbertPresentation
        (canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z) =
      canonicalCompletedC3ConcreteRealAxisGreenState z := by
  rw [canonicalCompletedC3OrientedRecoveredHilbertPresentation_eq_existing]
  rfl

/-- The complex wrapper is only a real-axis wrapper; it retains no imaginary
parameter dependence. It cannot be treated as an audited holomorphic source
extension merely from its type. -/
theorem canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq
    {z w : ℂ} (h : z.re = w.re) :
    canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex z =
      canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex w := by
  unfold canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex
  rw [h]

/-- At zero cutoff the oriented prefix has zero ordinary/log-jet and residual
channels. Completion of the scalar trace lives in the separate exact tails. -/
theorem canonicalCompletedC3OrientedGreenFramePrefixState_zero
    (s : ℂ) : canonicalCompletedC3OrientedGreenFramePrefixState 0 s = 0 := by
  apply Prod.ext
  · rw [canonicalCompletedC3OrientedGreenFramePrefixState_fst]
    have hp : canonicalCompletedC3HilbertPrefixState s (3 * 0) = 0 := by
      apply Prod.ext <;> ext n <;> simp [canonicalCompletedC3HilbertPrefixState]
    rw [hp, map_zero]
    rfl
  · rw [canonicalCompletedC3OrientedGreenFramePrefixState_snd]
    simp [finiteReflectedGradientPairing]

/-- The completed trace at this same cutoff is nonzero at the center. Thus
the zero prefix cannot substitute for the tail-completed trace source. -/
theorem canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero :
    (canonicalC3BracketTfvdCompletedTracePair 0 0).1 ≠ 0 := by
  rw [canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime 0
    zero_mem_completedNativeHeightDomain]
  exact completedNativeOperatorCharacteristic_zero_ne_zero

/-- The radial complex samples all have the same real-axis wrapped source.
This is a scope check, not a holomorphic extension of that source. -/
theorem canonicalCompletedC3OrientedRealAxisWrapper_radial_eq_center
    (k n : ℕ) :
    canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex
      (canonicalCompletedC3RadialTiltPoint k n) =
      canonicalCompletedC3RealAxisOrientedGreenFrameStateComplex 0 := by
  apply canonicalCompletedC3OrientedRealAxisWrapper_eq_of_re_eq
  have hstep : canonicalGreenJetStep k =
      ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    rw [← canonicalGreenJetRealStep_coe]
    rfl
  rw [canonicalCompletedC3RadialTiltPoint, canonicalCompletedC3RadialTiltStep, hstep]
  simp

/-- No homogeneous linear readout on the oriented prefixes alone can supply
all cutoff-independent completed values. The zero-cutoff witness isolates
the absent completion coordinates rather than rejecting the completed source. -/
theorem no_linear_orientedPrefix_completedValue_readout
    (L : CanonicalCompletedC3OrientedGreenFrameCarrier →ₗ[ℝ] ℂ) :
    ¬ ∀ M : ℕ,
      L (canonicalCompletedC3OrientedGreenFramePrefixState M
        (operatorHeightParameter 0)) =
      (canonicalC3BracketTfvdCompletedTracePair M 0).1 := by
  intro h
  have hzero := h 0
  rw [canonicalCompletedC3OrientedGreenFramePrefixState_zero, map_zero] at hzero
  exact canonicalC3BracketTfvdCompletedTracePair_zero_value_ne_zero hzero.symm

/-- The current ordinary product norm is the maximum norm. It fails the
parallelogram identity already on two independent Green-frame channels;
therefore it is not an existing Hilbert metric on this carrier. -/
theorem canonicalCompletedC3OrientedGreenFrameCarrier_not_parallelogram :
    ¬ ∀ u v : CanonicalCompletedC3OrientedGreenFrameCarrier,
      ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  let a : CarryVerticalL2 := lp.single 2 0 (1 : ℂ)
  have ha : a ≠ 0 := by
    intro h
    have hc := congrArg (fun x : CarryVerticalL2 => x 0) h
    simp [a, lp.single_apply] at hc
  let x := canonicalCompletedGreenFrameAnalysisCLM a
  have hx : x ≠ 0 := by
    intro h
    apply ha
    apply canonicalCompletedGreenFrameAnalysisCLM_injective
    simpa [x] using h
  let u : CanonicalCompletedC3OrientedGreenFrameCarrier := ((x, 0), 0)
  let v : CanonicalCompletedC3OrientedGreenFrameCarrier := ((0, x), 0)
  intro h
  have hp := h u v
  simp [u, v, Prod.norm_def] at hp
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  nlinarith

end
end CarrySelfAdjointOperator
