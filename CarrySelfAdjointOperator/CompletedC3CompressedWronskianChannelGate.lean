import CarrySelfAdjointOperator.CompletedC3CompressedBoundaryReadout
import Mathlib.Tactic

/-!
# Compressed C3 boundary versus the completed Wronskian channels

The closed compressed realization produces a direct Hilbert product of two
camera states.  The completed Wronskian ledger instead uses the reflected
static Green pairing, followed by the structural and crossed chart channels.
This module expands both sides far enough to compare those concrete objects
without introducing a new sewing hypothesis.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The permanent camera synthesis retains the real part of the original
complex `l2` inner product. -/
theorem inner_completedC3LegCameraState_eq_re_inner
    (x y : CarryVerticalL2) :
    inner Real (completedC3LegCameraState x) (completedC3LegCameraState y) =
      (inner Complex x y).re := by
  unfold completedC3LegCameraState
  rw [LinearIsometry.inner_map_map]
  change (∑' n : Nat, inner Real (x n) (y n)) =
    (∑' n : Nat, inner Complex (x n) (y n)).re
  rw [Complex.re_tsum (lp.summable_inner x y)]
  apply tsum_congr
  intro n
  exact real_inner_eq_re_inner Complex (x n) (y n)

/-- Scalar coefficient produced by taking the ordinary complex Hilbert
product of two completed symplectic camera states. -/
def canonicalCompletedC3CompressedGramCoefficient (z w : Complex) : Complex :=
  (((completedC3RadialRealCoefficient z *
      completedC3RadialRealCoefficient w + 1 : Real) : Complex)) +
    Complex.I *
      (((completedC3RadialRealCoefficient w -
        completedC3RadialRealCoefficient z : Real) : Complex))

theorem inner_canonicalCompletedC3GammaCameraView_re
    (u v : RealifiedCameraComplexification) :
    (inner Complex
      (canonicalCompletedC3GammaCameraView u)
      (canonicalCompletedC3GammaCameraView v)).re =
      inner Real u.fst v.fst + inner Real u.snd v.snd := by
  rw [RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner_re]
  rfl

theorem inner_canonicalCompletedC3GammaCameraView_im
    (u v : RealifiedCameraComplexification) :
    (inner Complex
      (canonicalCompletedC3GammaCameraView u)
      (canonicalCompletedC3GammaCameraView v)).im =
      inner Real u.fst v.snd - inner Real u.snd v.fst := by
  rw [RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner_im]
  rfl

/-- Exact expansion of the direct compressed camera Gram.  Unlike the static
Green channel, this product uses the unreflected pair and only the real part
of its ordinary-gradient Gram. -/
theorem inner_completedC3SymplecticCameraState_eq_compressedCoefficient
    (z w : Complex) (hz : 0 < z.re) (hw : 0 < w.re) :
    inner Complex
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState z hz))
        (canonicalCompletedC3GammaCameraView
          (completedC3SymplecticCameraState w hw)) =
      canonicalCompletedC3CompressedGramCoefficient z w *
        ((canonicalCompletedC3RawGammaGram z w hz hw).re : Complex) := by
  apply Complex.ext
  · rw [inner_canonicalCompletedC3GammaCameraView_re]
    unfold completedC3SymplecticCameraState
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, inner_neg_left,
      inner_neg_right, real_inner_smul_left, real_inner_smul_right,
      neg_neg]
    rw [inner_completedC3LegCameraState_eq_re_inner]
    unfold canonicalCompletedC3RawGammaGram
      canonicalCompletedC3CompressedGramCoefficient
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul]
    norm_num
    ring
  · rw [inner_canonicalCompletedC3GammaCameraView_im]
    unfold completedC3SymplecticCameraState
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, inner_neg_left,
      inner_neg_right, real_inner_smul_left, real_inner_smul_right]
    rw [inner_completedC3LegCameraState_eq_re_inner]
    unfold canonicalCompletedC3RawGammaGram
      canonicalCompletedC3CompressedGramCoefficient
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul]
    norm_num
    ring

/-- The completed compressed boundary readout in fully expanded radial-Gram
coordinates. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_eq_explicitRawGammaGram
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hz : 0 < (operatorHeightParameter z).re)
    (hw : 0 < (operatorHeightParameter w).re)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hz)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hw)
    (hsourceZ : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource z hz hboundZ)))
    (hsourceW : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource w hw hboundW))) :
    canonicalCompletedC3CompressedBoundaryReadout
        z w hz hw hboundZ hboundW =
      (w - conj z) *
        canonicalCompletedC3CompressedGramCoefficient
          (operatorHeightParameter z) (operatorHeightParameter w) *
        ((canonicalCompletedC3RawGammaGram
          (operatorHeightParameter z) (operatorHeightParameter w)
          hz hw).re : Complex) := by
  rw [canonicalCompletedC3CompressedBoundaryReadout_eq_kernel
    hbase z w hz hw hboundZ hboundW hsourceZ hsourceW,
    inner_completedC3SymplecticCameraState_eq_compressedCoefficient]
  ring

/-- The completed static Green channel in the Wronskian orientation has its
own distinct coefficient and reflected ordinary-gradient Gram. -/
theorem canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_explicit
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
        z w hzStrip hwStrip =
      canonicalC3MixedRadialCoefficient
          (operatorHeightParameter w) (operatorHeightParameter z) *
        canonicalCompletedC3RawGammaGram
          (operatorHeightParameter z)
          (reflectedParameter (operatorHeightParameter w))
          hzStrip.1
          (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2) := by
  rfl

/-- The reflected ordinary-gradient Gram used by the static Green channel is
reconstructed pointwise from the ordinary and log-jet coordinates at the
unreflected source. -/
theorem canonicalCompletedC3RawGammaGram_reflected_eq_logJetReconstruction
    (z w : Complex) (hz : 0 < z.re)
    (hwReflected : 0 < (reflectedParameter w).re) :
    canonicalCompletedC3RawGammaGram
        z (reflectedParameter w) hz hwReflected =
      ∑' n : Nat,
        conj (positiveDirichletGradient z n) *
          sameEdgeRecoveredReflectedGradient n
            (positiveDirichletGradient w n)
            (positiveLogDirichletGradient w n) := by
  unfold canonicalCompletedC3RawGammaGram
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [sameEdgeRecoveredReflectedGradient_canonical]
  simp [RCLike.inner_apply]
  ring

/-- Completed reflected gradient reconstructed from the ordinary and log-jet
channels at the unreflected parameter. -/
def canonicalCompletedC3RecoveredReflectedGradientState
    (s : Complex) (hsReflected : 0 < (reflectedParameter s).re) :
    CarryVerticalL2 :=
  ⟨fun n : Nat =>
      sameEdgeRecoveredReflectedGradient n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n),
    by
      change Memℓp (fun n : Nat =>
        sameEdgeRecoveredReflectedGradient n
          (positiveDirichletGradient s n)
          (positiveLogDirichletGradient s n)) 2
      simpa only [sameEdgeRecoveredReflectedGradient_canonical] using
        positiveDirichletGradient_memℓp_two hsReflected⟩

@[simp] theorem canonicalCompletedC3RecoveredReflectedGradientState_apply
    (s : Complex) (hsReflected : 0 < (reflectedParameter s).re) (n : Nat) :
    canonicalCompletedC3RecoveredReflectedGradientState s hsReflected n =
      sameEdgeRecoveredReflectedGradient n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n) :=
  rfl

/-- The reconstructed state is exactly the ordinary completed state at the
reflected parameter. -/
theorem canonicalCompletedC3RecoveredReflectedGradientState_eq
    (s : Complex) (hsReflected : 0 < (reflectedParameter s).re) :
    canonicalCompletedC3RecoveredReflectedGradientState s hsReflected =
      canonicalCompletedC3DirichletGradientState
        (reflectedParameter s) hsReflected := by
  apply lp.ext
  funext n
  rw [canonicalCompletedC3RecoveredReflectedGradientState_apply,
    canonicalCompletedC3DirichletGradientState_apply,
    sameEdgeRecoveredReflectedGradient_canonical]

/-- State-level form of the reflected Green channel: the second vector is
obtained by the exact same-edge ordinary/log-jet reconstruction. -/
theorem canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_recoveredStateInner
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
        z w hzStrip hwStrip =
      canonicalC3MixedRadialCoefficient
          (operatorHeightParameter w) (operatorHeightParameter z) *
        inner Complex
          (canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter z) hzStrip.1)
          (canonicalCompletedC3RecoveredReflectedGradientState
            (operatorHeightParameter w)
            (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2)) := by
  rw [canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_explicit,
    canonicalCompletedC3RecoveredReflectedGradientState_eq]
  rfl

/-- Hence the static reflected Green term is already an explicit readout of
the enriched ordinary/log-jet source. -/
theorem canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_logJetReconstruction
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
        z w hzStrip hwStrip =
      canonicalC3MixedRadialCoefficient
          (operatorHeightParameter w) (operatorHeightParameter z) *
        ∑' n : Nat,
          conj (positiveDirichletGradient
              (operatorHeightParameter z) n) *
            sameEdgeRecoveredReflectedGradient n
              (positiveDirichletGradient
                (operatorHeightParameter w) n)
              (positiveLogDirichletGradient
                (operatorHeightParameter w) n) := by
  rw [canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_explicit,
    canonicalCompletedC3RawGammaGram_reflected_eq_logJetReconstruction]

/-- Exact first comparison square.  It exposes the direct/unreflected real
Gram on the compressed side and the reflected complex Gram on the static
Green side. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_sub_staticGreen_eq
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hwStrip.1)
    (hsourceZ : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzStrip.1 hboundZ)))
    (hsourceW : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwStrip.1 hboundW))) :
    canonicalCompletedC3CompressedBoundaryReadout
          z w hzStrip.1 hwStrip.1 hboundZ hboundW -
        canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
          z w hzStrip hwStrip =
      (w - conj z) *
          canonicalCompletedC3CompressedGramCoefficient
            (operatorHeightParameter z) (operatorHeightParameter w) *
          ((canonicalCompletedC3RawGammaGram
            (operatorHeightParameter z) (operatorHeightParameter w)
            hzStrip.1 hwStrip.1).re : Complex) -
        canonicalC3MixedRadialCoefficient
            (operatorHeightParameter w) (operatorHeightParameter z) *
          canonicalCompletedC3RawGammaGram
            (operatorHeightParameter z)
            (reflectedParameter (operatorHeightParameter w))
            hzStrip.1
            (by simpa [reflectedParameter] using sub_pos.mpr hwStrip.2) := by
  rw [canonicalCompletedC3CompressedBoundaryReadout_eq_explicitRawGammaGram
    hbase z w hzStrip.1 hwStrip.1 hboundZ hboundW hsourceZ hsourceW,
    canonicalCompletedC3AllOrderStaticSymplecticGreenReadout_eq_explicit]

/-- Head--tail completion and the crossed product rule express the completed
Wronskian through the static reflected Green channel, its structural limit,
and the archimedean/chart channel. -/
theorem completedFNegFPrimeWronskian_crossedChart_eq_static_add_channels
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z =
      mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
              z w hzStrip hwStrip +
            canonicalCompletedC3AllOrderStructuralChannelLimit
              z w hzStrip hwStrip) +
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  have hcompanion : completedNativeOperatorBoundaryCompanion =
      (fun u : Complex => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  rw [hcompanion]
  rw [completedFNegFPrimeWronskian_crossedChartIdentity hwStrip hzStrip]
  unfold canonicalCompletedC3AllOrderStructuralChannelLimit
  ring

theorem mixedHermitianWeight_canonicalC3ChartFactorHeight_ne_zero
    {z w : Complex}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z ≠ 0 := by
  unfold mixedHermitianWeight
  apply mul_ne_zero
  · exact canonicalC3ChartFactorHeight_ne_zero hwStrip
  · simpa using canonicalC3ChartFactorHeight_ne_zero hzStrip

/-- Final channelwise comparison of the closed compressed boundary with the
completed Wronskian.  Every discrepancy is now a named existing channel or
one explicit direct-versus-reflected Gram difference. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_crossedChart_sub_wronskian
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hwStrip.1)
    (hsourceZ : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzStrip.1 hboundZ)))
    (hsourceW : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwStrip.1 hboundW))) :
    mixedHermitianWeight canonicalC3ChartFactorHeight w z *
        (canonicalCompletedC3CompressedBoundaryReadout
            z w hzStrip.1 hwStrip.1 hboundZ hboundW -
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z) =
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          ((w - conj z) *
            canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter w) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter w)
              hzStrip.1 hwStrip.1).re : Complex)) -
        mixedHermitianWeight nativeXiCompletionFactor w z *
          (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
              z w hzStrip hwStrip +
            canonicalCompletedC3AllOrderStructuralChannelLimit
              z w hzStrip hwStrip) -
        canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  rw [mul_sub,
    canonicalCompletedC3CompressedBoundaryReadout_eq_explicitRawGammaGram
      hbase z w hzStrip.1 hwStrip.1 hboundZ hboundW hsourceZ hsourceW,
    completedFNegFPrimeWronskian_crossedChart_eq_static_add_channels
      z w hzStrip hwStrip]
  ring

/-- Consequently the desired boundary/Wronskian sewing is equivalent to one
fully explicit channel equation.  The chart weight is cancelled only after
its nonvanishing has been proved on the strip. -/
theorem canonicalCompletedC3CompressedBoundaryReadout_eq_wronskian_iff_channels
    {base : Nat} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (z w : Complex)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hboundZ : CanonicalCompletedC3CompressedSourceFormBounded z hzStrip.1)
    (hboundW : CanonicalCompletedC3CompressedSourceFormBounded w hwStrip.1)
    (hsourceZ : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff z)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        z hzStrip.1 hboundZ)))
    (hsourceW : Filter.Tendsto
      (fun cutoff : Nat =>
        canonicalCompletedC3CausalResponseBoundaryFiniteCompressedSource
          hbase cutoff w)
      Filter.atTop
      (nhds (canonicalCompletedC3CompressedHilbertSource
        w hwStrip.1 hboundW))) :
    canonicalCompletedC3CompressedBoundaryReadout
          z w hzStrip.1 hwStrip.1 hboundZ hboundW =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z ↔
      mixedHermitianWeight canonicalC3ChartFactorHeight w z *
          ((w - conj z) *
            canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter w) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter w)
              hzStrip.1 hwStrip.1).re : Complex)) =
        mixedHermitianWeight nativeXiCompletionFactor w z *
            (canonicalCompletedC3AllOrderStaticSymplecticGreenReadout
                z w hzStrip hwStrip +
              canonicalCompletedC3AllOrderStructuralChannelLimit
                z w hzStrip hwStrip) +
          canonicalCompletedC3ArchimedeanChartMixedChannel w z := by
  let chartWeight :=
    mixedHermitianWeight canonicalC3ChartFactorHeight w z
  have hchartWeight : chartWeight ≠ 0 :=
    mixedHermitianWeight_canonicalC3ChartFactorHeight_ne_zero
      hzStrip hwStrip
  have hboundary :=
    canonicalCompletedC3CompressedBoundaryReadout_eq_explicitRawGammaGram
      hbase z w hzStrip.1 hwStrip.1 hboundZ hboundW hsourceZ hsourceW
  have hwronskian :=
    completedFNegFPrimeWronskian_crossedChart_eq_static_add_channels
      z w hzStrip hwStrip
  constructor
  · intro hsewing
    calc
      chartWeight *
          ((w - conj z) *
            canonicalCompletedC3CompressedGramCoefficient
              (operatorHeightParameter z) (operatorHeightParameter w) *
            ((canonicalCompletedC3RawGammaGram
              (operatorHeightParameter z) (operatorHeightParameter w)
              hzStrip.1 hwStrip.1).re : Complex)) =
          chartWeight * canonicalCompletedC3CompressedBoundaryReadout
            z w hzStrip.1 hwStrip.1 hboundZ hboundW :=
        congrArg (chartWeight * ·) hboundary.symm
      _ = chartWeight * completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z :=
        congrArg (chartWeight * ·) hsewing
      _ = _ := hwronskian
  · intro hchannels
    apply mul_left_cancel₀ hchartWeight
    rw [hboundary]
    exact hchannels.trans hwronskian.symm

end

end CarrySelfAdjointOperator
