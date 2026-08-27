import CarrySelfAdjointOperator.CompletedC3GreenFrameStructuralReadoutBridge
import CarrySelfAdjointOperator.RealLinearPMapComplexification
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Concrete real-axis carrier for the completed C3 kernel

The completed C3/TFVD state already contains an ordinary vertical channel, a
logarithmic vertical channel, and the retained precompression residual.  This
file places those three one-point channels in one complex Hilbert carrier:

* ordinary and log-jet states are transported by the canonical Parseval
  Green-frame analysis;
* the real residual is embedded in its canonical Hilbert complexification;
* the completed characteristic supplies exactly the `sqrt 2 * F` factor
  removed by `normalizedCompletedGreenState`.

Thus the remaining positive sewing statement no longer quantifies over an
arbitrary Hilbert space or an arbitrary state.  It is one equality between the
already constructed channel-complete C3 readout and the Gram product of this
concrete one-point carrier.
-/

open scoped ComplexOrder InnerProductSpace RealInnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

noncomputable section

/-! ## Concrete one-point positive carrier -/

/-- Hilbert presentation of the two retained real precompression channels. -/
abbrev CanonicalCompletedC3RealAxisResidualHilbert :=
  WithLp 2 NativeGpreTfvdCompletedPrecompressionSource

/-- The ordinary Parseval Green-frame channel, the log-jet Parseval
Green-frame channel, and the complexified TFVD residual remain orthogonal
coordinates of one fixed carrier. -/
abbrev CanonicalCompletedC3RealAxisPositiveCarrier :=
  WithLp 2
    (CanonicalCompletedGreenFrameCarrier ×
      WithLp 2
        (CanonicalCompletedGreenFrameCarrier ×
          RealHilbertComplexification
            CanonicalCompletedC3RealAxisResidualHilbert))

/-- Completed ordinary TFVD state at the centered-height parameter attached
to a real-axis argument. -/
def canonicalCompletedC3RealAxisOrdinaryState (z : ℂ) : CarryVerticalL2 :=
  (canonicalCompletedC3HilbertState
    (operatorHeightParameter (z.re : ℂ))
    (ofReal_mem_completedNativeHeightDomain z.re).1).1

/-- Completed logarithmic TFVD state at the same centered-height parameter. -/
def canonicalCompletedC3RealAxisLogJetState (z : ℂ) : CarryVerticalL2 :=
  (canonicalCompletedC3HilbertState
    (operatorHeightParameter (z.re : ℂ))
    (ofReal_mem_completedNativeHeightDomain z.re).1).2

/-- Retained real precompression residual at the same one-point parameter. -/
def canonicalCompletedC3RealAxisResidualState
    (z : ℂ) : CanonicalCompletedC3RealAxisResidualHilbert :=
  WithLp.toLp 2
    (infiniteReflectedGreenEnergy (operatorHeightParameter (z.re : ℂ)) •
      completedTfvdResidualGenerator)

/-- Canonical real-to-complex embedding of the retained residual. -/
def canonicalCompletedC3RealAxisComplexResidualState
    (z : ℂ) :
    RealHilbertComplexification CanonicalCompletedC3RealAxisResidualHilbert :=
  RealHilbertComplexification.mk
    (canonicalCompletedC3RealAxisResidualState z) 0

/-- Concrete positive one-point state.  No pair `(z,w)` is used in its
definition, and no scalar C3 channel has been added before entering the
orthogonal carrier. -/
def canonicalCompletedC3RealAxisPositiveState
    (z : ℂ) : CanonicalCompletedC3RealAxisPositiveCarrier :=
  WithLp.toLp 2
    (canonicalCompletedGreenFrameParsevalAnalysis
        (canonicalCompletedC3RealAxisOrdinaryState z),
      WithLp.toLp 2
        (canonicalCompletedGreenFrameParsevalAnalysis
            (canonicalCompletedC3RealAxisLogJetState z),
          canonicalCompletedC3RealAxisComplexResidualState z))

namespace CanonicalCompletedC3RealAxisPositiveCarrier

def ordinary (state : CanonicalCompletedC3RealAxisPositiveCarrier) :
    CanonicalCompletedGreenFrameCarrier :=
  (WithLp.ofLp state).1

def logJet (state : CanonicalCompletedC3RealAxisPositiveCarrier) :
    CanonicalCompletedGreenFrameCarrier :=
  (WithLp.ofLp (WithLp.ofLp state).2).1

def residual (state : CanonicalCompletedC3RealAxisPositiveCarrier) :
    RealHilbertComplexification CanonicalCompletedC3RealAxisResidualHilbert :=
  (WithLp.ofLp (WithLp.ofLp state).2).2

end CanonicalCompletedC3RealAxisPositiveCarrier

@[simp] theorem canonicalCompletedC3RealAxisPositiveState_ordinary
    (z : ℂ) :
    (canonicalCompletedC3RealAxisPositiveState z).ordinary =
      canonicalCompletedGreenFrameParsevalAnalysis
        (canonicalCompletedC3RealAxisOrdinaryState z) :=
  rfl

@[simp] theorem canonicalCompletedC3RealAxisPositiveState_logJet
    (z : ℂ) :
    (canonicalCompletedC3RealAxisPositiveState z).logJet =
      canonicalCompletedGreenFrameParsevalAnalysis
        (canonicalCompletedC3RealAxisLogJetState z) :=
  rfl

@[simp] theorem canonicalCompletedC3RealAxisPositiveState_residual
    (z : ℂ) :
    (canonicalCompletedC3RealAxisPositiveState z).residual =
      canonicalCompletedC3RealAxisComplexResidualState z :=
  rfl

/-- The positive product retains ordinary, log-jet, and residual energies as
three separate summands. -/
theorem canonicalCompletedC3RealAxisPositiveState_inner_eq_channelSum
    (z w : ℂ) :
    inner ℂ
        (canonicalCompletedC3RealAxisPositiveState z)
        (canonicalCompletedC3RealAxisPositiveState w) =
      inner ℂ
          (canonicalCompletedC3RealAxisPositiveState z).ordinary
          (canonicalCompletedC3RealAxisPositiveState w).ordinary +
        inner ℂ
          (canonicalCompletedC3RealAxisPositiveState z).logJet
          (canonicalCompletedC3RealAxisPositiveState w).logJet +
        inner ℂ
          (canonicalCompletedC3RealAxisPositiveState z).residual
          (canonicalCompletedC3RealAxisPositiveState w).residual := by
  unfold CanonicalCompletedC3RealAxisPositiveCarrier.ordinary
    CanonicalCompletedC3RealAxisPositiveCarrier.logJet
    CanonicalCompletedC3RealAxisPositiveCarrier.residual
  let stateZ := canonicalCompletedC3RealAxisPositiveState z
  let stateW := canonicalCompletedC3RealAxisPositiveState w
  change inner ℂ stateZ stateW = _
  rw [WithLp.prod_inner_apply stateZ stateW,
    WithLp.prod_inner_apply (WithLp.ofLp stateZ).2 (WithLp.ofLp stateW).2]
  ring

/-- The ordinary Parseval coordinate retains the four concrete Green-frame
channels: seed, residual, depth-one Green, and bulk Green. -/
theorem canonicalCompletedC3RealAxisPositiveState_ordinary_inner_eq_channelSum
    (z w : ℂ) :
    let stateZ := (canonicalCompletedC3RealAxisPositiveState z).ordinary
    let stateW := (canonicalCompletedC3RealAxisPositiveState w).ordinary
    inner ℂ stateZ stateW =
      inner ℂ stateZ.fst.fst.fst stateW.fst.fst.fst +
        inner ℂ stateZ.fst.fst.snd stateW.fst.fst.snd +
        inner ℂ stateZ.fst.snd stateW.fst.snd +
        inner ℂ stateZ.snd stateW.snd := by
  dsimp only
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rfl

/-- The log-jet Parseval coordinate retains the same four concrete
Green-frame channels independently of the ordinary coordinate. -/
theorem canonicalCompletedC3RealAxisPositiveState_logJet_inner_eq_channelSum
    (z w : ℂ) :
    let stateZ := (canonicalCompletedC3RealAxisPositiveState z).logJet
    let stateW := (canonicalCompletedC3RealAxisPositiveState w).logJet
    inner ℂ stateZ stateW =
      inner ℂ stateZ.fst.fst.fst stateW.fst.fst.fst +
        inner ℂ stateZ.fst.fst.snd stateW.fst.fst.snd +
        inner ℂ stateZ.fst.snd stateW.fst.snd +
        inner ℂ stateZ.snd stateW.snd := by
  dsimp only
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rfl

/-- Positive kernel carried by the concrete ordinary/log-jet/residual state. -/
def canonicalCompletedC3RealAxisPositiveKernel (z w : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3RealAxisPositiveState z)
    (canonicalCompletedC3RealAxisPositiveState w)

/-- The concrete Gram is exactly the orthogonal sum of the three completed
TFVD source products.  Parseval analysis changes only the presentation of
the ordinary and log-jet channels, while complexification embeds the real
residual without adding an imaginary coordinate. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_eq_sourceChannelSum
    (z w : ℂ) :
    canonicalCompletedC3RealAxisPositiveKernel z w =
      inner ℂ
          (canonicalCompletedC3RealAxisOrdinaryState z)
          (canonicalCompletedC3RealAxisOrdinaryState w) +
        inner ℂ
          (canonicalCompletedC3RealAxisLogJetState z)
          (canonicalCompletedC3RealAxisLogJetState w) +
        ((inner ℝ
          (canonicalCompletedC3RealAxisResidualState z)
          (canonicalCompletedC3RealAxisResidualState w) : ℝ) : ℂ) := by
  rw [canonicalCompletedC3RealAxisPositiveKernel,
    canonicalCompletedC3RealAxisPositiveState_inner_eq_channelSum,
    canonicalCompletedC3RealAxisPositiveState_ordinary,
    canonicalCompletedC3RealAxisPositiveState_ordinary,
    canonicalCompletedC3RealAxisPositiveState_logJet,
    canonicalCompletedC3RealAxisPositiveState_logJet,
    canonicalCompletedGreenFrameParsevalAnalysis_inner,
    canonicalCompletedGreenFrameParsevalAnalysis_inner]
  simp [canonicalCompletedC3RealAxisComplexResidualState,
    RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner]

/-- Every finite section of the concrete channel-complete kernel is positive
semidefinite before any scalar sewing statement is used. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_posSemidef
    {ι : Type*} [Finite ι] (point : ι → ℂ) :
    (Matrix.of fun i j ↦
      canonicalCompletedC3RealAxisPositiveKernel
        (point i) (point j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i ↦
    canonicalCompletedC3RealAxisPositiveState (point i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- The concrete kernel keeps its diagonal as the squared norm of the full
ordinary/log-jet/residual state. -/
theorem canonicalCompletedC3RealAxisPositiveKernel_self (z : ℂ) :
    canonicalCompletedC3RealAxisPositiveKernel z z =
      ((‖canonicalCompletedC3RealAxisPositiveState z‖ ^ 2 : ℝ) : ℂ) := by
  simp [canonicalCompletedC3RealAxisPositiveKernel,
    inner_self_eq_norm_sq_to_K]

/-! ## Exact normalization and the concrete sewing gate -/

/-- Unnormalized one-point state carrying the exact scalar factor removed by
the completed Green normalization. -/
def canonicalCompletedC3ConcreteRealAxisGreenState
    (z : ℂ) : CanonicalCompletedC3RealAxisPositiveCarrier :=
  (((Real.sqrt 2 : ℝ) : ℂ) *
      completedNativeOperatorCharacteristic z) •
    canonicalCompletedC3RealAxisPositiveState z

/-- Away from a completed-characteristic zero, normalization recovers the
concrete positive one-point state exactly. -/
theorem normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq
    (z : ℂ) (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    normalizedCompletedGreenState
        completedNativeOperatorCharacteristic
        canonicalCompletedC3ConcreteRealAxisGreenState z =
      canonicalCompletedC3RealAxisPositiveState z := by
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  unfold normalizedCompletedGreenState
    canonicalCompletedC3ConcreteRealAxisGreenState
  exact inv_smul_smul₀ (mul_ne_zero hsqrt hzF)
    (canonicalCompletedC3RealAxisPositiveState z)

/-- Concrete, channel-complete positive sewing statement.  Its left side is
the oriented C3 ledger after the final normalization; its right side is the
ordinary/log-jet/residual Gram of two one-point states. -/
def CanonicalCompletedC3ConcreteRealAxisPositiveSewing : Prop :=
  ∀ (M : ℕ) (x z : ℝ),
    completedNativeOperatorCharacteristic (x : ℂ) ≠ 0 →
    completedNativeOperatorCharacteristic (z : ℂ) ≠ 0 →
    canonicalCompletedC3AllCutoffOrientedRealKernelReadout M x z =
      inner ℂ
        (canonicalCompletedC3RealAxisPositiveState (x : ℂ))
        (canonicalCompletedC3RealAxisPositiveState (z : ℂ))

/-- The abstract real-axis kernel interface for the explicit state above is
equivalent to the one concrete C3 sewing equality.  No arbitrary state,
carrier, defect, or kernel remains in this equivalence. -/
theorem
    canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_realAxisKernel :
    CanonicalCompletedC3ConcreteRealAxisPositiveSewing ↔
      HasCompletedNativeRealAxisNormalizedGreenKernel
        canonicalCompletedC3ConcreteRealAxisGreenState := by
  constructor
  · intro hsewing x z hxF hzF
    rw [normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq
        (x : ℂ) hxF,
      normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq
        (z : ℂ) hzF]
    rw [← canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
      0 x z hxF hzF]
    exact (hsewing 0 x z hxF hzF).symm
  · intro hkernel M x z hxF hzF
    rw [canonicalCompletedC3AllCutoffOrientedRealKernelReadout_eq_dslope
      M x z hxF hzF]
    rw [← normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq
        (x : ℂ) hxF,
      ← normalizedCanonicalCompletedC3ConcreteRealAxisGreenState_eq
        (z : ℂ) hzF]
    exact (hkernel x z hxF hzF).symm

/-- Once the concrete sewing equality is proved, the actual explicit state
is the required real-axis normalized Green-kernel inhabitant. -/
theorem hasCompletedNativeRealAxisNormalizedGreenKernel_of_concreteC3Sewing
    (hsewing : CanonicalCompletedC3ConcreteRealAxisPositiveSewing) :
    HasCompletedNativeRealAxisNormalizedGreenKernel
      canonicalCompletedC3ConcreteRealAxisGreenState :=
  canonicalCompletedC3ConcreteRealAxisPositiveSewing_iff_realAxisKernel.mp
    hsewing

end

end CarrySelfAdjointOperator
