import CarrySelfAdjointOperator.CompletedC3NaimarkCoisometricBlock
import Mathlib.Tactic

/-!
# Coisometric C3 boundary and Wronskian interface

The intrinsic completed source is now available canonically as the Naimark
coisometric readout of the ambient source.  This module removes the former
bounded-form and source-convergence parameters from the public boundary and
Wronskian interface.  The complementary Naimark channel remains explicit and
is proved orthogonal to the scalar response-source skew; it is not discarded
as a vector.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open Filter
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Canonical intrinsic boundary -/

/-- Intrinsic boundary skew using the canonical coisometric source directly,
with no Riesz-bound witness in its type. -/
def canonicalCompletedC3CoisometricCompressedBoundaryReadout
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter z) hz))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CoisometricCompressedSourceLimit w hw)) -
    inner ℂ
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3CoisometricCompressedSourceLimit z hz))
      (canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState (operatorHeightParameter w) hw))

/-- The new readout is exactly the old Riesz-parametrized readout at the
canonical coisometric bound. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_compressed
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw =
      canonicalCompletedC3CompressedBoundaryReadout z w hz hw
        (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hz)
        (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hw) := by
  unfold canonicalCompletedC3CoisometricCompressedBoundaryReadout
    canonicalCompletedC3CompressedBoundaryReadout
  rw [canonicalCompletedC3CompressedHilbertSource_coisometric_eq,
    canonicalCompletedC3CompressedHilbertSource_coisometric_eq]

/-- The finite compressed source converges to the canonically instantiated
Riesz vector, without accepting convergence as an argument. -/
theorem canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z : ℂ) (hz : 0 < (operatorHeightParameter z).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hz
        (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hz))) := by
  rw [canonicalCompletedC3CompressedHilbertSource_coisometric_eq]
  exact
    canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource_tendsto_coisometric
      hbase z hz

/-- Finite boundary skews converge to the canonical coisometric readout. -/
theorem canonicalCompletedC3FiniteCompressedBoundaryReadout_tendsto_coisometric
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    Tendsto
      (fun cutoff : ℕ =>
        canonicalCompletedC3FiniteCompressedBoundaryReadout
          hbase cutoff z w)
      atTop
      (nhds (canonicalCompletedC3CoisometricCompressedBoundaryReadout
        z w hz hw)) := by
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_compressed]
  exact canonicalCompletedC3FiniteCompressedBoundaryReadout_tendsto
    hbase z w hz hw
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hz)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hw)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase z hz)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase w hw)

/-- Exact completed Green identity for the canonical intrinsic source. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw =
      (w - conj z) *
        inner ℂ
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter z) hz))
          (canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter w) hw)) := by
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_compressed]
  exact canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    hbase z w hz hw
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hz)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hw)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase z hz)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase w hw)

/-! ## Explicit port and retained escape -/

/-- Ambient port contribution of the canonical coisometric source. -/
def canonicalCompletedC3CoisometricAmbientPortBoundaryReadout
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState (operatorHeightParameter z) hz))
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort
          (canonicalCompletedC3CoisometricCompressedSourceLimit w hw))) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (realifiedNaimarkPort
          (canonicalCompletedC3CoisometricCompressedSourceLimit z hz)))
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState (operatorHeightParameter w) hw))

/-- Ambient escape contribution retained by the lossless Naimark block. -/
def canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState (operatorHeightParameter z) hz))
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3CoisometricNaimarkLeakLimit w hw)) -
    inner ℂ
      (canonicalCompletedC3GammaNaimarkView
        (canonicalCompletedC3CoisometricNaimarkLeakLimit z hz))
      (canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState (operatorHeightParameter w) hw))

/-- Full ambient boundary splits exactly into its canonical port and escape
channels before any scalar orthogonality is used. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricPort_add_leak
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout z w hz hw =
      canonicalCompletedC3CoisometricAmbientPortBoundaryReadout z w hz hw +
        canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout z w hz hw := by
  unfold canonicalCompletedC3AmbientBoundaryReadout
    canonicalCompletedC3CoisometricAmbientPortBoundaryReadout
    canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout
  rw [canonicalCompletedC3AmbientInducedSourceLimit_eq_coisometricPort_add_leak
      z hz,
    canonicalCompletedC3AmbientInducedSourceLimit_eq_coisometricPort_add_leak
      w hw,
    canonicalCompletedC3GammaNaimarkView_add,
    canonicalCompletedC3GammaNaimarkView_add,
    inner_add_right, inner_add_left]
  ring

/-- The retained escape vector is orthogonal to this scalar readout.  This
does not assert that the escape vector itself vanishes. -/
theorem canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout_eq_zero
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout z w hz hw = 0 := by
  have hzAdjoint :=
    realifiedNaimarkAdjoint_canonicalCompletedC3CoisometricNaimarkLeakLimit z hz
  have hwAdjoint :=
    realifiedNaimarkAdjoint_canonicalCompletedC3CoisometricNaimarkLeakLimit w hw
  have hfirst :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter z) hz))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3CoisometricNaimarkLeakLimit w hw)) = 0 := by
    change
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedNaimarkPort
              (completedC3SymplecticCameraState
                (operatorHeightParameter z) hz)))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3CoisometricNaimarkLeakLimit w hw)) = 0
    rw [inner_complex_gammaNaimarkView_port_eq_adjoint, hwAdjoint]
    simp
  have hportSecond :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter w) hw))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3CoisometricNaimarkLeakLimit z hz)) = 0 := by
    change
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedNaimarkPort
              (completedC3SymplecticCameraState
                (operatorHeightParameter w) hw)))
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3CoisometricNaimarkLeakLimit z hz)) = 0
    rw [inner_complex_gammaNaimarkView_port_eq_adjoint, hzAdjoint]
    simp
  have hsecond :
      inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (canonicalCompletedC3CoisometricNaimarkLeakLimit z hz))
          (canonicalCompletedC3GammaNaimarkView
            (completedC3SymplecticNaimarkState
              (operatorHeightParameter w) hw)) = 0 :=
    inner_eq_zero_symm.mp hportSecond
  unfold canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout
  rw [hfirst, hsecond, sub_self]

/-- The coisometric ambient port is literally the intrinsic boundary. -/
theorem canonicalCompletedC3CoisometricAmbientPortBoundaryReadout_eq_compressed
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricAmbientPortBoundaryReadout z w hz hw =
      canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw := by
  unfold canonicalCompletedC3CoisometricAmbientPortBoundaryReadout
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
    completedC3SymplecticNaimarkState
  rw [inner_complex_gammaNaimarkView_port_port,
    inner_complex_gammaNaimarkView_port_port]

/-- Canonical boundary square with no boundedness or convergence parameters. -/
theorem canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout z w hz hw =
      canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricPort_add_leak,
    canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout_eq_zero,
    add_zero,
    canonicalCompletedC3CoisometricAmbientPortBoundaryReadout_eq_compressed]

/-! ## Canonical Wronskian channel interface -/

/-- Explicit unreflected Gram formula for the canonical boundary. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_explicitRawGammaGram
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw =
      (w - conj z) *
        canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter z) (operatorHeightParameter w) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter z) (operatorHeightParameter w)
          hz hw).re : ℂ) := by
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel,
    inner_completedC3SymplecticCameraState_eq_compressedCoefficient]
  ring

/-- Canonical boundary/Wronskian sewing is exactly the positive response
kernel identity; no source-realization parameter remains. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_wronskian_iff_kernel
    (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z ↔
      (w - conj z) *
          inner ℂ
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                (operatorHeightParameter z) hz))
            (canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                (operatorHeightParameter w) hw)) =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel]

/-- The complete crossed-chart discrepancy, now stated without auxiliary
source witnesses. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_crossedChart_sub_wronskian
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        (canonicalCompletedC3CoisometricCompressedBoundaryReadout
            z w hzStrip.1 hwStrip.1 -
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z) =
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          ((w - conj z) *
            canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter w) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter w)
              hzStrip.1 hwStrip.1).re : ℂ)) -
        mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
              z w hzStrip hwStrip +
            canonicalCompletedC3AllOrderStructuralChannelLimit
              z w hzStrip hwStrip) -
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  rw [mul_sub,
    canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_explicitRawGammaGram,
    completedFNegFPrimeWronskian_crossedChart_eq_static_add_channels
      z w hzStrip hwStrip]
  ring

/-- Exact channel equation equivalent to canonical boundary/Wronskian
sewing, with every source-completion obligation already discharged. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_eq_wronskian_iff_channels
    (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z w hzStrip.1 hwStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z ↔
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          ((w - conj z) *
            canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter w) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter w)
              hzStrip.1 hwStrip.1).re : ℂ)) =
        mixedHermitianWeight nativeXiCompletionFactor w z *
            (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
                z w hzStrip hwStrip +
              canonicalCompletedC3AllOrderStructuralChannelLimit
                z w hzStrip hwStrip) +
          canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_compressed]
  exact canonicalCompletedC3CompressedBoundaryReadout_eq_wronskian_iff_channels
    hbase z w hzStrip hwStrip
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded
        z hzStrip.1)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded
        w hwStrip.1)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase z hzStrip.1)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase w hwStrip.1)

/-! ## Diagonal audit -/

/-- The canonical intrinsic boundary remains nonzero off the real height
axis; removing source parameters does not alter the confinement-strength
diagonal obstruction. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_ne_zero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
        z z hzStrip.1 hzStrip.1 ≠ 0 := by
  rw [← canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed]
  exact canonicalCompletedC3AmbientBoundaryReadout_diagonal_ne_zero hz hzStrip

/-- At an off-axis characteristic zero, canonical positive boundary sewing
to the scalar Wronskian is impossible. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_ne_wronskian_of_characteristicZero
    {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 ≠
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z := by
  rw [show completedGreenWronskian
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion z z = 0 by
    simp [completedGreenWronskian, hzero]]
  exact canonicalCompletedC3CoisometricBoundaryReadout_diagonal_ne_zero
    hz hzStrip

end

end CarrySelfAdjointOperator
