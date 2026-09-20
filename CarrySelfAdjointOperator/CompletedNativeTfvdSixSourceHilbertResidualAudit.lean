import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceChiralDefect
import CarrySelfAdjointOperator.CompletedC3CausalChiralPolarizedAudit
import CarrySelfAdjointOperator.CompletedC3ExistingDressedStateAudit
import CarrySelfAdjointOperator.CompletedNativeReturnMetricReadoutCrosswalk
import CarrySelfAdjointOperator.SixCameraGlobalNaimarkHaloDecomposition
import Mathlib.Tactic

/-!
# Hilbert-residual audit for the six-source chiral defect

This file does **not** assert positivity of the completed-native Pick defect.
Its purpose is narrower: it puts the nearest already-existing Hilbert
constructions on the same finite radial index set and records their exact
residuals.

In particular, the normalized coisometric state is an honest Hilbert state,
but it is not the Cauchy input state whose chiral-multiplier image defines
the Pick defect.  After polarization its difference from positive Wronskian
chirality retains a separable square-root ambient weight and a spectral-
separation `dslope` term.  This is an explicit candidate residual, rather
than an unproved identification with the Pick kernel.

The two other tempting Naimark/return candidates are kept type-honest:

* the response-port escape is identically zero;
* the Green return metric is the Gram of the original completed Green state;
* the six-camera halo is a real six-coordinate variance decomposition.

None of those statements is converted here into a contractivity or moment
criterion.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The polarized coisometric candidate on the actual radial index set -/

/-- Finite Gram matrix of the pre-existing normalized coisometric state,
sampled at the same shifted radial points as the completed-native Pick
matrix.  It is an honest Hilbert Gram, but it deliberately remains distinct
from the Cauchy-input/multiplier-output defect. -/
def canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
    (M k N : ℕ)
    (hstrip : ∀ i : Fin N,
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
        genuineCriticalStrip) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3NormalizedCoisometricChiralKernel M
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (hstrip i).1 (hstrip j).1

/-- The coisometric radial sample is positive semidefinite for the literal
Hilbert-space reason: it is a finite Gram matrix.  This fact concerns the
candidate carrier only and is not a positivity theorem for the Pick defect. -/
theorem canonicalCompletedNativeRadialCoisometricChiralSampleMatrix_posSemidef
    (M k N : ℕ)
    (hstrip : ∀ i : Fin N,
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
        genuineCriticalStrip) :
    (canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
      M k N hstrip).PosSemidef := by
  unfold canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
  exact canonicalCompletedC3NormalizedCoisometricChiralKernel_posSemidef M
    (fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i)
    (fun i => (hstrip i).1)

/-- Exact residual of the coisometric Gram after subtracting positive
Wronskian chirality.  The first summand has the separable square-root
normalization inherited from the ambient Hilbert channel; the second is the
nonseparable spectral-separation multiple of the native divided slope.
Thus this formula exposes the remaining mismatch without identifying either
side with the Pick defect. -/
theorem canonicalCompletedNativeRadialCoisometricChiralSample_sub_positive_apply
    (M k N : ℕ)
    (hstrip : ∀ i : Fin N,
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
        genuineCriticalStrip)
    (hF : ∀ i : Fin N,
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
        M k N hstrip i j -
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j) =
      (((Real.sqrt (2 * (canonicalCompletedC3RadialTiltPoint k i).im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * (canonicalCompletedC3RadialTiltPoint k j).im) : ℝ) : ℂ)) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (hstrip i).1 (hstrip j).1 +
      Complex.I *
          (canonicalCompletedC3RadialTiltPoint k j -
            conj (canonicalCompletedC3RadialTiltPoint k i)) *
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j) := by
  unfold canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
  exact canonicalCompletedC3NormalizedCoisometricChiralKernel_sub_positive_eq
    M (hstrip i) (hstrip j) (hF i) (hF j)
      (sub_ne_zero.mp (canonicalCompletedC3RadialTilt_separation_ne_zero
        k i j))

/-- The one-point test for the coisometric candidate is already a genuine
sewing condition: diagonal agreement with positive chirality is equivalent
to the ambient response kernel being the native divided slope.  Positivity
of the coisometric Gram does not prove that equality. -/
theorem canonicalCompletedNativeRadialCoisometricChiralSample_diagonal_eq_positive_iff
    (M k N : ℕ)
    (hstrip : ∀ i : Fin N,
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
        genuineCriticalStrip)
    (hF : ∀ i : Fin N,
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i : Fin N) :
    canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
        M k N hstrip i i =
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k i) ↔
      canonicalCompletedC3NormalizedAmbientResponseKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k i)
          (hstrip i).1 (hstrip i).1 =
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k i) := by
  unfold canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
  exact canonicalCompletedC3NormalizedCoisometricChiralKernel_diagonal_eq_positive_iff
    M (hstrip i) (hF i)
      (canonicalCompletedC3RadialTiltPoint_im_pos k i)

/-- Even on the actual first two shifted radial points, the separable
square-root weight belonging to the coisometric Gram is not the
quarter-turned spectral separation.  This is the earliest off-diagonal
normalization failure of that direct-sum candidate; it is independent of
any Pick-positivity, moment, or zero-set assertion. -/
theorem canonicalCompletedC3RadialCoisometricSqrtWeight_twoPoint_ne_separation
    (k : ℕ) :
    (((Real.sqrt
          (2 * (canonicalCompletedC3RadialTiltPoint k 0).im) : ℝ) : ℂ) *
        ((Real.sqrt
          (2 * (canonicalCompletedC3RadialTiltPoint k 1).im) : ℝ) : ℂ)) ≠
      -Complex.I *
        (canonicalCompletedC3RadialTiltPoint k 1 -
          conj (canonicalCompletedC3RadialTiltPoint k 0)) := by
  intro h
  have hreal := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.I_re, neg_zero, Complex.neg_im, Complex.I_im,
    neg_one_mul, zero_mul, Complex.sub_re, Complex.conj_re] at hreal
  simp only [sub_zero, zero_sub, Complex.sub_im, Complex.conj_im] at hreal
  rw [canonicalCompletedC3RadialTiltPoint_im,
    canonicalCompletedC3RadialTiltPoint_im] at hreal
  norm_num at hreal
  have hb : Real.sqrt ((k : ℝ) + 1) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity)
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hb, hk] at hreal
  have hsqrtTwo : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by positivity)
  have hsqrtK : (Real.sqrt ((k : ℝ) + 1)) ^ 2 = (k : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  have hcube : (Real.sqrt 2) ^ 3 = 3 := by
    apply mul_left_cancel₀ hk
    calc
      ((k : ℝ) + 1) * (Real.sqrt 2) ^ 3 =
          (Real.sqrt 2) ^ 3 * ((k : ℝ) + 1) := by ring
      _ = (Real.sqrt ((k : ℝ) + 1)) ^ 2 * (2 + 1) := hreal
      _ = ((k : ℝ) + 1) * 3 := by rw [hsqrtK]; ring
  have hcubeSq := congrArg (fun x : ℝ => x ^ 2) hcube
  have hleft : ((Real.sqrt 2) ^ 3) ^ 2 = 8 := by
    calc
      ((Real.sqrt 2) ^ 3) ^ 2 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
      _ = 8 := by rw [hsqrtTwo]; norm_num
  rw [hleft] at hcubeSq
  norm_num at hcubeSq

/-- Three-point form of the exact coisometric residual.  This is a
componentwise microscope for the first finite level that can carry a genuine
three-by-three Pick obstruction; it leaves the residual visible rather than
silently replacing it by a determinant or a moment criterion. -/
theorem canonicalCompletedNativeRadialCoisometricChiralThreePoint_residual_apply
    (M k : ℕ)
    (hstrip : ∀ i : Fin 3,
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
        genuineCriticalStrip)
    (hF : ∀ i : Fin 3,
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin 3) :
    canonicalCompletedNativeRadialCoisometricChiralSampleMatrix
        M k 3 hstrip i j -
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j) =
      (((Real.sqrt (2 * (canonicalCompletedC3RadialTiltPoint k i).im) : ℝ) : ℂ) *
          ((Real.sqrt (2 * (canonicalCompletedC3RadialTiltPoint k j).im) : ℝ) : ℂ)) *
        canonicalCompletedC3NormalizedAmbientResponseKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (hstrip i).1 (hstrip j).1 +
      Complex.I *
          (canonicalCompletedC3RadialTiltPoint k j -
            conj (canonicalCompletedC3RadialTiltPoint k i)) *
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j) :=
  canonicalCompletedNativeRadialCoisometricChiralSample_sub_positive_apply
    M k 3 hstrip hF i j

/-! ## Candidate classification facts already available at vector level -/

/-- The most direct response-Naimark escape candidate is zero before any
finite sampling.  Consequently it cannot provide a nontrivial residual
family by itself. -/
theorem canonicalCompletedNative_responseNaimarkEscape_eq_zero (z : ℂ) :
    canonicalCompletedC3RealAxisResponseNaimarkEscapeState z = 0 :=
  canonicalCompletedC3RealAxisResponseNaimarkEscapeState_eq_zero z

/-- The native Green return readout is an ordinary positive Gram, but its
vectors are completed Green-frame states.  This keeps its carrier separate
from the radial Cauchy input and multiplier output used by the Pick defect. -/
theorem canonicalCompletedNative_returnMetricKernel_eq_state_inner
    (x y : GreenFrame.Concrete.State) :
    canonicalNativeGreenFrameReturnKernel x y = inner ℂ x y :=
  canonicalNativeGreenFrameReturnKernel_eq_state_inner x y

/-- Exact scalar residual of the ordinary Green return-metric candidate at
the center.  It is strictly positive, so this return construction is not a
sewing of its central graph kernel to the native zeroth moment. -/
theorem canonicalCompletedNative_returnMetricCentralDelta_pos :
    0 < canonicalNativeReturnMetricCentralDefect :=
  canonicalNativeReturnMetricCentralDefect_pos

/-- The preceding failed return residual is literally ordinary reflected
Green energy minus the native zeroth logarithmic moment. -/
theorem canonicalCompletedNative_returnMetricCentralDelta_eq :
    canonicalNativeReturnMetricCentralDefect =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) -
        canonicalCompletedNativeLogDerivativeMoment 0 :=
  canonicalNativeReturnMetricCentralDefect_eq_energy_sub_native

/-- The global six-camera halo plus global escape realizes the *real*
six-camera variance.  Its coefficient space is `Fin 6 → ℝ`, so this is a
separate camera-variance Gram decomposition rather than a radial complex
Pick-residual family. -/
theorem canonicalCompletedNative_sixCameraVariance_eq_halo_add_escape
    (u v : Fin 6 → ℝ) :
    u ⬝ᵥ (NativeCarrySpectralWeyl.Finite.sixCameraVariance *ᵥ v) =
      inner ℝ
          (sixCameraGlobalCoherentHaloProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
          (sixCameraGlobalCoherentHaloProjection
            (sixCameraWhitenedCenteredLogNaimarkSynthesis v)) +
        inner ℝ
          (globalNaimarkCameraEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis u))
          (globalNaimarkCameraEscape
            (sixCameraWhitenedCenteredLogNaimarkSynthesis v)) :=
  sixCameraVariance_eq_globalHaloGram_add_globalNaimarkEscapeGram u v

end

end CarrySelfAdjointOperator
