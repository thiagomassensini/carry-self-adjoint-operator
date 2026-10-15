import CarrySelfAdjointOperator.NativeRealFirstQuadratureNaturality
import CarrySelfAdjointOperator.NativePrimeCarryKernelCalibration

/-! The EXISTING prime-carry contraction, lifted on two real quadratures.
Its complementary form retains the metric and rotation-associated pairing.
No physical source family or equality with the native Green kernel is assumed. -/
namespace CarrySelfAdjointOperator.RealFirstNative
open scoped InnerProductSpace RealInnerProductSpace
open CPFormal.Analytic.Cp RealQuadrature SourceKernelCalibration
noncomputable section
set_option autoImplicit false

def primeContractionLinear : NativeGpreTowerHilbert →ₗ[ℝ] PrimeCarryDefectGlobalHilbert where
  toFun := nativeGprePrimeCarryDefectState
  map_add' x y := by
    apply lp.ext
    funext p
    simp only [nativeGprePrimeCarryDefectState_apply, nativeGprePrimeCarryDefectCoordinate,
      inner_add_right, add_smul, lp.coeFn_add, Pi.add_apply]
  map_smul' a x := by
    apply lp.ext
    funext p
    simp only [nativeGprePrimeCarryDefectState_apply, nativeGprePrimeCarryDefectCoordinate,
      real_inner_smul_right, mul_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

def towerComplement (x y : Space NativeGpreTowerHilbert) : ℝ :=
  inner ℝ x y - inner ℝ (lift primeContractionLinear x) (lift primeContractionLinear y)

theorem towerComplement_eq_original_quadratures (x y : Space NativeGpreTowerHilbert) :
    towerComplement x y = complementKernel x.fst y.fst + complementKernel x.snd y.snd := by
  change (inner ℝ x.fst y.fst + inner ℝ x.snd y.snd) -
    (inner ℝ (nativeGprePrimeCarryDefectState x.fst) (nativeGprePrimeCarryDefectState y.fst) +
      inner ℝ (nativeGprePrimeCarryDefectState x.snd) (nativeGprePrimeCarryDefectState y.snd)) = _
  unfold complementKernel
  ring

theorem towerComplement_coercive (x : Space NativeGpreTowerHilbert) :
    (1 / 12 : ℝ) * ‖x‖ ^ 2 ≤ towerComplement x x := by
  rw [towerComplement_eq_original_quadratures, WithLp.prod_norm_sq_eq_of_L2]
  have hx := complementKernel_coercive x.fst
  have hy := complementKernel_coercive x.snd
  linarith

/-- Posterior complex form reconstructs both independent polarized entries. -/
theorem towerComplement_pack_pairing (x y : Space NativeGpreTowerHilbert) :
    inner ℂ (pack x) (pack y) -
        inner ℂ (pack (lift primeContractionLinear x)) (pack (lift primeContractionLinear y)) =
      (towerComplement x y : ℂ) + Complex.I * (towerComplement (J x) y : ℂ) := by
  rw [pack_inner, pack_inner]
  simp only [towerComplement, lift_J]
  push_cast
  ring

/-- At the center the SAME 1/12 estimate applies to the full two-quadrature
norm. It does not select a source or impose the desired central equality. -/
theorem towerComplement_central_calibration (x : Space NativeGpreTowerHilbert)
    (h : towerComplement x x = canonicalCompletedNativeLogDerivativeMoment 0) :
    ‖x‖ ^ 2 ≤ 12 * canonicalCompletedNativeLogDerivativeMoment 0 ∧ ‖x‖ ^ 2 < 3 / 4 := by
  have hc := towerComplement_coercive x
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  rw [h] at hc
  constructor <;> nlinarith

end
end CarrySelfAdjointOperator.RealFirstNative
