import CarrySelfAdjointOperator.CompletedC3CoisometricBoundaryWronskian
import CarrySelfAdjointOperator.CompletedNativeGlobalRadialEnergyLedger
import Mathlib.Tactic

/-!
# Coisometric Wronskian projection gate

The canonical Naimark coisometry removes the auxiliary source bounds and
convergence witnesses from the completed compressed boundary. This module
performs the same substitution in the remaining Wronskian correction ledger.

On the diagonal, the three response/source correction channels reduce to one
exact projection balance. The balance retains the internal camera-port cross
term and the complementary resolvent escape norm; neither is discarded by
`U U*`.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-! ## Canonically instantiated correction channels -/

/-- Resolved correction internal to the camera port, with the source bound
fixed by the canonical coisometric realization. -/
def canonicalCompletedC3CoisometricPortResolvedBoundaryCorrection
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3CompressedTfvdPortResolvedCorrectionBoundaryReadout
    z w hz hw hzHalf hwHalf
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hzHalf)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hwHalf)

/-- Resolved correction returned through the complementary Naimark channel. -/
def canonicalCompletedC3CoisometricLeakResolvedBoundaryCorrection
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3AmbientLeakResolvedCorrectionBoundaryReadout
    z w hz hw hzHalf hwHalf
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hzHalf)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hwHalf)

/-- Source correction visible in the intrinsic camera port. -/
def canonicalCompletedC3CoisometricPortSourceBoundaryCorrection
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3CompressedTfvdPortSourceCorrectionBoundaryReadout
    z w hzHalf hwHalf
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hzHalf)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hwHalf)

/-- The three correction channels separating the coisometric compressed
boundary from the canonical positive Gamma boundary. -/
def canonicalCompletedC3CoisometricThreeBoundaryCorrections
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3CoisometricPortResolvedBoundaryCorrection
      z w hz hw hzHalf hwHalf +
    canonicalCompletedC3CoisometricLeakResolvedBoundaryCorrection
      z w hz hw hzHalf hwHalf +
    canonicalCompletedC3CoisometricPortSourceBoundaryCorrection
      z w hzHalf hwHalf

/-- The full four-channel discrepancy also retains the independent positive
Gamma-versus-Wronskian boundary defect. -/
def canonicalCompletedC3CoisometricWronskianFourChannelDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
    canonicalCompletedC3CoisometricThreeBoundaryCorrections
      z w hz hw hzHalf hwHalf

/-! ## Exact coisometric substitutions -/

/-- The canonically instantiated three-channel correction is exactly the
coisometric compressed boundary minus the positive Gamma boundary. -/
theorem canonicalCompletedC3CoisometricThreeBoundaryCorrections_eq_sub_gamma
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3CoisometricThreeBoundaryCorrections
        z w hz hw hzHalf hwHalf =
      canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z w hzHalf hwHalf -
        canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw := by
  let hbase : FiniteNativeCarryOperator.Camera.IsSupported 3 := by
    norm_num [FiniteNativeCarryOperator.Camera.IsSupported]
  have h := canonicalCompletedC3CompressedBoundary_sub_gamma_eq_threeCorrections
    hbase z w hz hw hzHalf hwHalf
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded z hzHalf)
      (canonicalCompletedC3CoisometricCompressedSourceFormBounded w hwHalf)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase z hzHalf)
      (canonicalCompletedC3FiniteCompressedSource_tendsto_coisometricRiesz
        hbase w hwHalf)
  unfold canonicalCompletedC3CoisometricThreeBoundaryCorrections
    canonicalCompletedC3CoisometricPortResolvedBoundaryCorrection
    canonicalCompletedC3CoisometricLeakResolvedBoundaryCorrection
    canonicalCompletedC3CoisometricPortSourceBoundaryCorrection
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_compressed]
  exact h.symm

/-- Every source and completion witness has disappeared: the four-channel
defect is literally the canonical coisometric boundary minus the completed
`(F,-F')` Wronskian. -/
theorem canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricWronskianFourChannelDefect
        z w hz hw hzStrip.1 hwStrip.1 =
      canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z w hzStrip.1 hwStrip.1 -
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  unfold canonicalCompletedC3CoisometricWronskianFourChannelDefect
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_eq_sub_gamma]
  unfold canonicalCompletedC3RawGammaWronskianDefect
  ring

/-- Canonical boundary/Wronskian sewing is now exactly the vanishing of the
four concrete correction channels. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_eq_wronskian_iff_fourChannels
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z w hzStrip.1 hwStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z ↔
      canonicalCompletedC3CoisometricWronskianFourChannelDefect
          z w hz hw hzStrip.1 hwStrip.1 = 0 := by
  rw [canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub
    z w hz hw hzStrip hwStrip]
  exact sub_eq_zero.symm

/-! ## Diagonal projection balance -/

/-- Difference of the two response energies written entirely in the
orthogonal `U U*` decomposition. The only indefinite term left is the
pairing internal to the camera port. -/
theorem canonicalCompletedC3Ambient_sub_gamma_energy_eq_projectionBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
        ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 =
      2 * (inner ℂ
          (canonicalCompletedC3ProjectedGammaPortState z hz)
          (canonicalCompletedC3AmbientPortDifferenceState
            z hz hzHalf)).re +
        ‖canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf‖ ^ 2 -
        ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 := by
  have hambient :
      canonicalCompletedC3AmbientResponseState z hzHalf =
        canonicalCompletedC3ProjectedGammaPortState z hz +
          canonicalCompletedC3AmbientPortDifferenceState z hz hzHalf := by
    unfold canonicalCompletedC3AmbientPortDifferenceState
    abel
  have hgamma := canonicalCompletedC3PolarizedGammaState_eq_port_add_escape z hz
  rw [hambient, hgamma, norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ),
    inner_canonicalCompletedC3ProjectedGammaPort_escape_eq_zero]
  simp only [map_zero, RCLike.re_eq_complex_re]
  ring

/-- On the diagonal, the three canonical correction channels are precisely
the spectral separation times the projection balance. -/
theorem canonicalCompletedC3CoisometricThreeBoundaryCorrections_diagonal
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CoisometricThreeBoundaryCorrections
        z z hz hz hzHalf hzHalf =
      Complex.I *
        ((2 * z.im *
          (2 * (inner ℂ
              (canonicalCompletedC3ProjectedGammaPortState z hz)
              (canonicalCompletedC3AmbientPortDifferenceState
                z hz hzHalf)).re +
            ‖canonicalCompletedC3AmbientPortDifferenceState
              z hz hzHalf‖ ^ 2 -
            ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2) : ℝ) : ℂ) := by
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_eq_sub_gamma]
  rw [← canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed]
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
      z z hz hz hzHalf hzHalf,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3PolarizedGammaKernel
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    (canonicalCompletedC3PolarizedGammaState z hz)]
  change
    (z - conj z) *
          inner ℂ
            (canonicalCompletedC3AmbientResponseState z hzHalf)
            (canonicalCompletedC3AmbientResponseState z hzHalf) -
        (z - conj z) *
          ((‖canonicalCompletedC3PolarizedGammaState z hz‖ : ℂ) ^ 2) = _
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    (canonicalCompletedC3AmbientResponseState z hzHalf)]
  have henergy :=
    canonicalCompletedC3Ambient_sub_gamma_energy_eq_projectionBalance
      z hz hzHalf
  have henergyComplex :
      ((‖canonicalCompletedC3AmbientResponseState z hzHalf‖ : ℂ) ^ 2) -
          ((‖canonicalCompletedC3PolarizedGammaState z hz‖ : ℂ) ^ 2) =
        ((2 * (inner ℂ
              (canonicalCompletedC3ProjectedGammaPortState z hz)
              (canonicalCompletedC3AmbientPortDifferenceState
                z hz hzHalf)).re +
            ‖canonicalCompletedC3AmbientPortDifferenceState
              z hz hzHalf‖ ^ 2 -
            ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ((‖canonicalCompletedC3AmbientResponseState z hzHalf‖ : ℂ) ^ 2) -
            ((‖canonicalCompletedC3PolarizedGammaState z hz‖ : ℂ) ^ 2) =
          ((‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 : ℝ) : ℂ) -
            ((‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 : ℝ) : ℂ) :=
        congrArg₂ (fun a b : ℂ => a - b)
          (Complex.ofReal_pow
            ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ 2).symm
          (Complex.ofReal_pow
            ‖canonicalCompletedC3PolarizedGammaState z hz‖ 2).symm
      _ = ((‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 -
            ‖canonicalCompletedC3PolarizedGammaState z hz‖ ^ 2 : ℝ) : ℂ) := by
        norm_cast
      _ = _ := congrArg (fun r : ℝ => (r : ℂ)) henergy
  rw [← mul_sub]
  have hseparation :
      z - conj z = Complex.I * (((2 * z.im : ℝ) : ℂ)) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  calc
    (z - conj z) *
          (((‖canonicalCompletedC3AmbientResponseState z hzHalf‖ : ℂ) ^ 2) -
            ((‖canonicalCompletedC3PolarizedGammaState z hz‖ : ℂ) ^ 2)) =
        (z - conj z) *
          ((2 * (inner ℂ
                (canonicalCompletedC3ProjectedGammaPortState z hz)
                (canonicalCompletedC3AmbientPortDifferenceState
                  z hz hzHalf)).re +
              ‖canonicalCompletedC3AmbientPortDifferenceState
                z hz hzHalf‖ ^ 2 -
              ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2 : ℝ) : ℂ) :=
      congrArg (fun q : ℂ => (z - conj z) * q) henergyComplex
    _ = _ := by
      rw [hseparation]
      push_cast
      ring

/-- The same diagonal correction, expressed through the cancellation balance
already isolated by the completed Gamma/correction factorization. -/
theorem canonicalCompletedC3CoisometricThreeBoundaryCorrections_diagonal_eq_gammaCorrectionBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CoisometricThreeBoundaryCorrections
        z z hz hz hzHalf hzHalf =
      Complex.I *
        (((2 * canonicalCompletedC3GammaCorrectionBalance
          z hz hzHalf : ℝ) : ℂ)) := by
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_diagonal,
    canonicalCompletedC3GammaCorrectionBalance_eq_energyDifference,
    canonicalCompletedC3Ambient_sub_gamma_energy_eq_projectionBalance]
  push_cast
  ring

/-- The diagonal sewing gate after the coisometric substitution. The raw
Gamma/Wronskian defect must cancel one explicit projection balance; no
abstract defect or omitted channel remains. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_projectionBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3RawGammaWronskianDefect z z hz hz +
          Complex.I *
            ((2 * z.im *
              (2 * (inner ℂ
                  (canonicalCompletedC3ProjectedGammaPortState z hz)
                  (canonicalCompletedC3AmbientPortDifferenceState
                    z hz hzStrip.1)).re +
                ‖canonicalCompletedC3AmbientPortDifferenceState
                  z hz hzStrip.1‖ ^ 2 -
                ‖canonicalCompletedC3GammaPortEscapeState z hz‖ ^ 2) : ℝ) : ℂ) =
        0 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_eq_wronskian_iff_fourChannels
    z z hz hz hzStrip hzStrip]
  unfold canonicalCompletedC3CoisometricWronskianFourChannelDefect
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_diagonal]

/-- Canonical form of the remaining diagonal sewing equation. The raw
Gamma--Wronskian channel must cancel twice the already existing completed
Gamma correction balance; coisometry introduces no additional witness. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gammaCorrectionBalance
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3RawGammaWronskianDefect z z hz hz +
          Complex.I *
            (((2 * canonicalCompletedC3GammaCorrectionBalance
              z hz hzStrip.1 : ℝ) : ℂ)) =
        0 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_eq_wronskian_iff_fourChannels
    z z hz hz hzStrip hzStrip]
  unfold canonicalCompletedC3CoisometricWronskianFourChannelDefect
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_diagonal_eq_gammaCorrectionBalance]

end

end CarrySelfAdjointOperator
