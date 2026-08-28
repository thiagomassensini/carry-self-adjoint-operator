import CarrySelfAdjointOperator.CanonicalC3SymplecticNaimarkBridge
import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import CarrySelfAdjointOperator.CompletedC3PolarizedCameraCrossResidual
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Corrected symplectic C3 Gamma state

The literal six-camera source retains every coordinate, but it does not
intertwine the intrinsic C3 Green form.  This file feeds the already-proved
symplectic C3 packing into the same global logarithmic Gamma field.

The resulting state is unconditional, nonzero on the open strip, and has the
standard positive two-parameter Gamma Gram.  Independently, both quadratures
of its static camera readout reconstruct the intrinsic complex C3 Green form
exactly.  No completed Wronskian sewing is asserted here.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace
  RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The completed C3 port packed by the Green-compatible symplectic map. -/
def canonicalCompletedC3SymplecticGammaCameraSource
    (z : ℂ) : CarryGammaComplexCamera :=
  canonicalC3SymplecticCameraPacking (canonicalCompletedOperatorC3State z)

/-- Symplectic packing retains the complete C3 port on the open strip. -/
theorem canonicalCompletedC3SymplecticGammaCameraSource_ne_zero
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3SymplecticGammaCameraSource z ≠ 0 := by
  intro hzero
  apply canonicalEnrichedC3SourcePort_ne_zero hzStrip
  apply canonicalC3SymplecticCameraPacking_injective
  have hpacked :
      canonicalC3SymplecticCameraPacking
          (canonicalCompletedOperatorC3State z) =
        canonicalC3SymplecticCameraPacking 0 := by
    calc
      canonicalC3SymplecticCameraPacking
          (canonicalCompletedOperatorC3State z) = 0 := hzero
      _ = canonicalC3SymplecticCameraPacking 0 := (map_zero _).symm
  simpa [canonicalCompletedOperatorC3State] using hpacked

/-- Gamma response of the corrected complete C3 source. -/
def canonicalCompletedC3SymplecticGammaState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  carryGammaComplexState z hz
    (canonicalCompletedC3SymplecticGammaCameraSource z)

/-- The corrected Gamma response is nonzero throughout the off-axis strip. -/
theorem canonicalCompletedC3SymplecticGammaState_ne_zero
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3SymplecticGammaState z hz ≠ 0 := by
  intro hstate
  apply canonicalCompletedC3SymplecticGammaCameraSource_ne_zero hzStrip
  apply carryGammaSource_injective z hz
  have hgamma :
      carryGammaSource z hz
          (canonicalCompletedC3SymplecticGammaCameraSource z) =
        carryGammaSource z hz 0 := by
    change carryGammaSource z hz
      (canonicalCompletedC3SymplecticGammaCameraSource z) = 0 at hstate
    calc
      carryGammaSource z hz
          (canonicalCompletedC3SymplecticGammaCameraSource z) = 0 := hstate
      _ = carryGammaSource z hz 0 := (map_zero _).symm
  exact hgamma

/-- Positive two-parameter kernel of the corrected Gamma responses. -/
def canonicalCompletedC3SymplecticGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ
    (canonicalCompletedC3SymplecticGammaState z hz)
    (canonicalCompletedC3SymplecticGammaState w hw)

/-- Complete Cauchy boundary readout of the corrected source family. -/
def canonicalCompletedC3SymplecticGammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  carryGammaPolarizedBoundaryReadout
    canonicalCompletedC3SymplecticGammaCameraSource z w hz hw

/-- The corrected boundary readout is exactly spectral separation times its
positive Gamma Gram. -/
theorem canonicalCompletedC3SymplecticGammaBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw =
      (w - conj z) *
        canonicalCompletedC3SymplecticGammaKernel z w hz hw := by
  exact carryGammaPolarizedBoundaryReadout_eq_inner
    canonicalCompletedC3SymplecticGammaCameraSource z w hz hw

/-- The diagonal corrected Gamma kernel is a squared norm. -/
theorem canonicalCompletedC3SymplecticGammaKernel_diagonal_eq_norm_sq
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3SymplecticGammaKernel z z hz hz =
      ((‖canonicalCompletedC3SymplecticGammaState z hz‖ : ℝ) : ℂ) ^ 2 := by
  simp [canonicalCompletedC3SymplecticGammaKernel,
    inner_self_eq_norm_sq_to_K]

/-- Every finite corrected Gamma section is positive semidefinite. -/
theorem canonicalCompletedC3SymplecticGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hoffAxis : ∀ i, (point i).im ≠ 0) :
    (Matrix.of fun i j =>
      canonicalCompletedC3SymplecticGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3SymplecticGammaState
      (point i) (hoffAxis i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- The corrected camera source promotes to the corrected Naimark state
already used by the static Green bridge. -/
theorem realifiedNaimarkPort_canonicalCompletedC3SymplecticGammaCameraSource
    (z : ℂ) :
    realifiedNaimarkPort
        (canonicalCompletedC3SymplecticGammaCameraSource z) =
      canonicalCompletedC3SymplecticNaimarkState z := by
  rfl

/-- Lossless two-quadrature static Green readout of the corrected camera
sources.  The quarter-turned second source is packed before scalarization. -/
def canonicalCompletedC3SymplecticCameraComplexGreenReadout
    (z w : ℂ) : ℂ :=
  (NativeCarryC3Crosswalk.realifiedGreenSkew
      (canonicalCompletedC3SymplecticGammaCameraSource z)
      (canonicalCompletedC3SymplecticGammaCameraSource w) : ℂ) -
    Complex.I *
      (NativeCarryC3Crosswalk.realifiedGreenSkew
        (canonicalCompletedC3SymplecticGammaCameraSource z)
        (canonicalC3SymplecticCameraPacking
          (Complex.I • canonicalCompletedOperatorC3State w)) : ℂ)

/-- The corrected camera packing reconstructs the intrinsic complex C3 Green
form exactly; this is the non-circular static square beneath the Gamma field. -/
theorem canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_greenForm
    (z w : ℂ) :
    canonicalCompletedC3SymplecticCameraComplexGreenReadout z w =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedOperatorC3State z)
        (canonicalCompletedOperatorC3State w) := by
  unfold canonicalCompletedC3SymplecticCameraComplexGreenReadout
    canonicalCompletedC3SymplecticGammaCameraSource
  rw [realifiedGreenSkew_canonicalC3SymplecticCameraPacking,
    realifiedGreenSkew_canonicalC3SymplecticCameraPacking,
    greenForm_smul_right]
  apply Complex.ext <;> simp

/-- In the Hermitian orientation used by the completed kernel, the corrected
camera readout is the existing simultaneous six-camera symplectic readout. -/
theorem canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_sixCamera
    (z w : ℂ) :
    canonicalCompletedC3SymplecticCameraComplexGreenReadout w (conj z) =
      canonicalCompletedC3SixCameraSymplecticGreenReadout
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  unfold canonicalCompletedC3SymplecticCameraComplexGreenReadout
    canonicalCompletedC3SymplecticGammaCameraSource
    canonicalCompletedC3SixCameraSymplecticGreenReadout
    canonicalC3SixCameraSymplecticComplexReadout
    canonicalC3SymplecticNaimarkRealization
    canonicalCompletedOperatorC3State
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    operatorHeightParameter_conj_eq_reflectedParameter,
    NativeCarryC3Crosswalk.realifiedGreenSkew_realifiedNaimarkPort]

/-- Exact location of the remaining scalar work below the Gamma field: the
raw completed Wronskian is the corrected static camera Green readout plus the
already-defined structural and head--tail channels. -/
theorem canonicalCompletedC3RawHeightMixedWronskian_eq_symplecticCamera_add_channels
    {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawHeightMixedWronskian z w =
      canonicalCompletedC3SymplecticCameraComplexGreenReadout w (conj z) +
        canonicalC3FiniteMixedHeightStructuralDefect 1
          (operatorHeightParameter z) (operatorHeightParameter w) +
        canonicalC3MixedHeightTailCompletionDefect 1 z w := by
  have h :=
    canonicalCompletedC3RawHeightMixedWronskian_eq_sixCameraGreen_add_channels
      hz hw
  rw [← canonicalCompletedC3SymplecticCameraComplexGreenReadout_eq_sixCamera]
    at h
  simpa [centeredHeightParameter, operatorHeightParameter] using h

/-- The first concrete mismatch under the corrected Gamma construction.  It
is exactly the Cauchy-to-static Green difference together with the existing
structural and head--tail channels; no unnamed defect is introduced. -/
theorem canonicalCompletedC3SymplecticGammaBoundary_sub_rawWronskian
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3RawHeightMixedWronskian w z =
      (canonicalCompletedC3SymplecticGammaBoundaryReadout z w hz hw -
          canonicalCompletedC3SymplecticCameraComplexGreenReadout z (conj w)) -
        canonicalC3FiniteMixedHeightStructuralDefect 1
          (operatorHeightParameter w) (operatorHeightParameter z) -
        canonicalC3MixedHeightTailCompletionDefect 1 w z := by
  rw [canonicalCompletedC3RawHeightMixedWronskian_eq_symplecticCamera_add_channels
    hwStrip hzStrip]
  ring

end

end CarrySelfAdjointOperator
