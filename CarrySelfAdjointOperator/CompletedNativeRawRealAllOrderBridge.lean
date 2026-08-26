import CarrySelfAdjointOperator.CompletedNativeAllOrderCameraBridge
import CarrySelfAdjointOperator.BR2RadialNormalizedComplexJetNoGo
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Raw real-axis all-order bridge for the completed native state

The normalized completed C3 state contains a radial phase and therefore does
not support complex Taylor jets at the center.  This file keeps that phase at
the final readout.  On the real native-height axis the phase is exactly one,
so the retained C3 readout agrees globally, in every real derivative order,
with its raw holomorphic factor.

The same module also upgrades the existing arbitrary-order camera tail bound
to actual convergence of every fixed finite-cutoff jet to the completed
bracket jet.  Thus the cutoff completion and the corrected all-order readout
are connected without division at a zero and without a new hypothesis.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open Filter

noncomputable section

/-! ## All-order passage from finite cameras to the completed bracket -/

/-- The explicit arbitrary-order tail scale tends to zero for every fixed
derivative order. -/
theorem higherDerivativeTailScale_tendsto_zero (order : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ =>
        Real.log x ^ (order : ℝ) / x ^ ((3 : ℝ) / 2))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop
      (order : ℝ) (by norm_num : (0 : ℝ) < 3 / 2)).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with cutoff hcutoff
  have hcutoffNonneg : 0 ≤ (cutoff : ℝ) := by positivity
  simp only [Function.comp_apply]
  rw [Real.rpow_natCast]
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
    Real.rpow_neg hcutoffNonneg]
  simp only [div_eq_mul_inv]
  ring

/-- Every fixed complex camera jet converges to the corresponding completed
bracket jet as the literal cutoff tends to infinity. -/
theorem iteratedDeriv_finiteBracketCharacteristic_nativeLine_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) (order : ℕ) (time : ℝ) :
    Tendsto
      (fun cutoff : ℕ =>
        iteratedDeriv order
          (finiteBracketCharacteristic camera cutoff) (nativeLine time))
      atTop
      (nhds
        (iteratedDeriv order
          (bracketCharacteristic camera) (nativeLine time))) := by
  have herror : Tendsto
      (fun cutoff : ℕ =>
        iteratedDeriv order
            (bracketCharacteristic camera) (nativeLine time) -
          iteratedDeriv order
            (finiteBracketCharacteristic camera cutoff) (nativeLine time))
      atTop (nhds 0) :=
    (iteratedDeriv_bracketCharacteristic_nativeLine_tail_isBigO
      hcamera order time).trans_tendsto
        (higherDerivativeTailScale_tendsto_zero order)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev, norm_zero] using herror.norm

/-- The same all-order convergence holds after restricting every camera to
the real native-height parameter. -/
theorem iteratedDeriv_finiteBracketCharacteristic_along_nativeLine_tendsto
    {camera : ℕ} (hcamera : 2 ≤ camera) (order : ℕ) (time : ℝ) :
    Tendsto
      (fun cutoff : ℕ =>
        iteratedDeriv order
          (fun u : ℝ =>
            finiteBracketCharacteristic camera cutoff (nativeLine u)) time)
      atTop
      (nhds
        (iteratedDeriv order
          (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) time)) := by
  have herror : Tendsto
      (fun cutoff : ℕ =>
        iteratedDeriv order
            (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) time -
          iteratedDeriv order
            (fun u : ℝ =>
              finiteBracketCharacteristic camera cutoff (nativeLine u)) time)
      atTop (nhds 0) :=
    (iteratedDeriv_along_nativeLine_tail_isBigO
      hcamera order time).trans_tendsto
        (higherDerivativeTailScale_tendsto_zero order)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev, norm_zero] using herror.norm

/-! ## Corrected real-axis readout with delayed radial phase -/

/-- The retained normalized C3 coordinate, restricted to the real
native-height axis. -/
def canonicalCompletedNativeC3NormalizedFirstRealReadout
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (time : ℝ) : ℂ :=
  completedNativeC3FirstZeroReadout Hxi
    (normalizedCompletedGreenState
      completedNativeOperatorCharacteristic
      (completedNativeC3ProductLedgerState xiState) (time : ℂ))

/-- The raw holomorphic C3 factor, restricted to the same real axis. -/
def canonicalCompletedNativeC3RawFirstRealReadout (time : ℝ) : ℂ :=
  br2C3HolomorphicFactor (time : ℂ)

/-- The raw first Green coordinate read from the bracket--TFVD completion
carrier itself.  We use cutoff `M + 1`, so the zeroth coordinate is present
without an external positivity hypothesis on `M`. -/
def canonicalC3BracketTfvdRawFirstRealReadout
    (M : ℕ) (time : ℝ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ) * nativeHeightScalar (time : ℂ))⁻¹ *
    ((canonicalC3BracketTfvdCompletionState (M + 1)
      (operatorHeightParameter (time : ℂ))).greenPort).2
        ⟨0, by omega⟩

/-- The TFVD carrier's raw zeroth Green coordinate is exactly the raw
holomorphic C3 factor, independently of the cutoff. -/
theorem canonicalC3BracketTfvdRawFirstRealReadout_eq_raw
    (M : ℕ) (time : ℝ) :
    canonicalC3BracketTfvdRawFirstRealReadout M time =
      canonicalCompletedNativeC3RawFirstRealReadout time := by
  unfold canonicalC3BracketTfvdRawFirstRealReadout
    canonicalCompletedNativeC3RawFirstRealReadout br2C3HolomorphicFactor
  rw [canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket,
    NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair_snd_apply]

/-- On the full real native-height axis, not merely near the center, the
normalized retained coordinate equals the raw holomorphic factor.  The
archimedean completion factor is nonzero throughout this axis; native zeros
are handled without division by splitting the zero case. -/
theorem canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_raw
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (time : ℝ) :
    canonicalCompletedNativeC3NormalizedFirstRealReadout xiState time =
      canonicalCompletedNativeC3RawFirstRealReadout time := by
  have hstrip : operatorHeightParameter (time : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hxi : nativeXiCompletionFactor (time : ℂ) ≠ 0 :=
    nativeXiCompletionFactor_ne_zero hstrip
  rw [canonicalCompletedNativeC3NormalizedFirstRealReadout,
    canonicalCompletedNativeC3RawFirstRealReadout,
    completedNativeC3FirstZeroReadout_normalizedState,
    phaseNormalizedC3Gradient_operatorHeight_eq_radialPhase_mul]
  unfold br2C3HolomorphicFactor completedNativeOperatorCharacteristic
  have hphase : br2RadialPhase (time : ℂ) = 1 := by
    simp [br2RadialPhase, br2RadialExponent]
  rw [hphase, one_mul]
  unfold nativeHeightScalar
  by_cases hnative : nativeScalar (operatorHeightParameter (time : ℂ)) = 0
  · simp [hnative]
  · field_simp [hxi, hnative]

/-- The normalized completed coordinate and the bracket--TFVD Green port are
the same scalar projection at every cutoff and every real height. -/
theorem canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_bracketTfvd
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (M : ℕ) (time : ℝ) :
    canonicalCompletedNativeC3NormalizedFirstRealReadout xiState time =
      canonicalC3BracketTfvdRawFirstRealReadout M time := by
  rw [canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_raw,
    canonicalC3BracketTfvdRawFirstRealReadout_eq_raw]

/-- On the same real-axis carrier, the completed TFVD trace projection is
exactly `(F,-F')`. -/
theorem canonicalC3BracketTfvdCompletedTracePair_real_eq_F_negFprime
    (M : ℕ) (time : ℝ) :
    canonicalC3BracketTfvdCompletedTracePair (M + 1) (time : ℂ) =
      (completedNativeOperatorCharacteristic (time : ℂ),
        -deriv completedNativeOperatorCharacteristic (time : ℂ)) := by
  apply canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime
  constructor <;> norm_num [operatorHeightParameter]

/-- The two-point Wronskian read from the same bracket--TFVD carrier is the
completed Wronskian of `(F,-F')` at arbitrary real heights. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_real_eq_completed
    (M : ℕ) (time₁ time₂ : ℝ) :
    canonicalC3BracketTfvdCompletedWronskianReadout
        (M + 1) (time₁ : ℂ) (time₂ : ℂ) =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u)
        (time₁ : ℂ) (time₂ : ℂ) := by
  apply canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
  · constructor <;> norm_num [operatorHeightParameter]
  · constructor <;> norm_num [operatorHeightParameter]

/-- One concrete bracket--TFVD completion state therefore carries both the
raw Green projection and the completed `(F,-F')` trace, with no cutoff or
zero-set hypothesis. -/
theorem canonicalCompletedNativeC3RealReadouts_sameBracketTfvdCarrier
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (M : ℕ) (time : ℝ) :
    canonicalCompletedNativeC3NormalizedFirstRealReadout xiState time =
        canonicalC3BracketTfvdRawFirstRealReadout M time ∧
      canonicalC3BracketTfvdCompletedTracePair (M + 1) (time : ℂ) =
        (completedNativeOperatorCharacteristic (time : ℂ),
          -deriv completedNativeOperatorCharacteristic (time : ℂ)) :=
  ⟨canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_bracketTfvd
      xiState M time,
    canonicalC3BracketTfvdCompletedTracePair_real_eq_F_negFprime M time⟩

/-- On the real axis the radial phase is exactly one, so the normalized and
raw retained C3 readouts agree in a neighborhood of the Taylor center. -/
theorem canonicalCompletedNativeC3NormalizedFirstRealReadout_eventuallyEq_raw
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) :
    canonicalCompletedNativeC3NormalizedFirstRealReadout xiState =ᶠ[nhds 0]
      canonicalCompletedNativeC3RawFirstRealReadout := by
  exact Eventually.of_forall
    (canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_raw xiState)

/-- Every real Taylor derivative of the retained normalized coordinate is the
corresponding derivative of the raw holomorphic C3 factor.  The phase has not
been differentiated or discarded; it is trivial only after the real-axis
readout is fixed. -/
theorem iteratedDeriv_canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_raw
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (order : ℕ) :
    iteratedDeriv order
        (canonicalCompletedNativeC3NormalizedFirstRealReadout xiState) 0 =
      iteratedDeriv order canonicalCompletedNativeC3RawFirstRealReadout 0 := by
  exact Filter.EventuallyEq.iteratedDeriv_eq order
    (canonicalCompletedNativeC3NormalizedFirstRealReadout_eventuallyEq_raw
      xiState)

/-- At every cutoff and every order, the real jet of the normalized completed
coordinate is the jet of the Green projection from the same bracket--TFVD
carrier. -/
theorem iteratedDeriv_canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_bracketTfvd
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (M order : ℕ) :
    iteratedDeriv order
        (canonicalCompletedNativeC3NormalizedFirstRealReadout xiState) 0 =
      iteratedDeriv order
        (canonicalC3BracketTfvdRawFirstRealReadout M) 0 := by
  apply Filter.EventuallyEq.iteratedDeriv_eq order
  exact Eventually.of_forall
    (canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_bracketTfvd
      xiState M)

/-- Factorial-normalized all-order real jet of the retained completed C3
coordinate. -/
def canonicalCompletedNativeC3NormalizedFirstRealTaylorJet
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (order : ℕ) : ℂ :=
  ((order.factorial : ℂ)⁻¹) *
    iteratedDeriv order
      (canonicalCompletedNativeC3NormalizedFirstRealReadout xiState) 0

/-- Factorial-normalized real jet of the raw holomorphic C3 factor. -/
def canonicalCompletedNativeC3RawFirstRealTaylorJet (order : ℕ) : ℂ :=
  ((order.factorial : ℂ)⁻¹) *
    iteratedDeriv order canonicalCompletedNativeC3RawFirstRealReadout 0

/-- The corrected completed all-order C3 jet is exactly the raw holomorphic
jet after the common real-axis readout. -/
theorem canonicalCompletedNativeC3NormalizedFirstRealTaylorJet_eq_raw
    {Hxi : Type*} [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (order : ℕ) :
    canonicalCompletedNativeC3NormalizedFirstRealTaylorJet xiState order =
      canonicalCompletedNativeC3RawFirstRealTaylorJet order := by
  rw [canonicalCompletedNativeC3NormalizedFirstRealTaylorJet,
    canonicalCompletedNativeC3RawFirstRealTaylorJet,
    iteratedDeriv_canonicalCompletedNativeC3NormalizedFirstRealReadout_eq_raw]

end

end CarrySelfAdjointOperator
