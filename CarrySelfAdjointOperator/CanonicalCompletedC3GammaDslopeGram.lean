import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import CarrySelfAdjointOperator.CanonicalC3GammaStateIdentity
import CarrySelfAdjointOperator.CompletedGreenRealKernelClosure
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Canonical completed C3 gamma Gram and the dslope comparison

The completed TFVD ledger supplies a parameter-dependent six-camera source.
This file feeds that concrete source into the polarized gamma identity without
freezing it or projecting any quadrature.  The resulting vectors all live in
one complex Hilbert realization of the global Naimark space.

The positive gamma kernel is therefore unconditional.  Its comparison with
the completed-native `dslope` is recorded as an exact numerator equivalence:
the two kernels agree precisely when the complete Cauchy boundary readout is
the normalized-response numerator.  This formulation neither assumes that
identity nor replaces the source-varying boundary form by a fixed-source
scalar response.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Concrete completed TFVD/C3 gamma vector in the common complex Naimark
Hilbert space.  Both real quadratures of the six-camera source are retained. -/
def canonicalCompletedC3PolarizedGammaState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  carryGammaComplexState z hz (canonicalCompletedC3SixCameraSource z)

/-- Positive two-parameter Gram kernel of the concrete completed C3 gamma
states. -/
def canonicalCompletedC3PolarizedGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ
    (canonicalCompletedC3PolarizedGammaState z hz)
    (canonicalCompletedC3PolarizedGammaState w hw)

/-- Complete source-varying Cauchy boundary readout for the same two concrete
completed C3 states. -/
def canonicalCompletedC3PolarizedGammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  carryGammaPolarizedBoundaryReadout
    canonicalCompletedC3SixCameraSource z w hz hw

/-- The concrete boundary readout is the spectral separation multiplying the
positive Gram of the same completed TFVD/C3 states. -/
theorem canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      (w - conj z) *
        canonicalCompletedC3PolarizedGammaKernel z w hz hw := by
  exact carryGammaPolarizedBoundaryReadout_eq_inner
    canonicalCompletedC3SixCameraSource z w hz hw

/-- The diagonal of the concrete gamma kernel is exactly a squared norm. -/
theorem canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaKernel z z hz hz =
      ((‖canonicalCompletedC3PolarizedGammaState z hz‖ : ℝ) : ℂ) ^ 2 := by
  simp [canonicalCompletedC3PolarizedGammaKernel,
    inner_self_eq_norm_sq_to_K]

/-- In particular the real diagonal of the full, unprojected gamma kernel is
nonnegative. -/
theorem canonicalCompletedC3PolarizedGammaKernel_diagonal_nonneg
    (z : ℂ) (hz : z.im ≠ 0) :
    0 ≤ (canonicalCompletedC3PolarizedGammaKernel z z hz hz).re := by
  rw [canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- Every finite section of the full source-varying C3 gamma kernel is
positive semidefinite because it is literally a Gram matrix in the one common
Naimark Hilbert space. -/
theorem canonicalCompletedC3PolarizedGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hoffAxis : ∀ i, (point i).im ≠ 0) :
    (Matrix.of fun i j =>
      canonicalCompletedC3PolarizedGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3PolarizedGammaState (point i) (hoffAxis i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- The private canonical gamma vector is literally the public gamma vector
constructed from the completed TFVD ledger in centered-height coordinates. -/
theorem canonicalCompletedC3PolarizedGammaState_centeredHeightParameter
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3PolarizedGammaState
        (centeredHeightParameter s)
        (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff) =
      NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff := by
  unfold canonicalCompletedC3PolarizedGammaState carryGammaComplexState
  rw [canonicalCompletedC3SixCameraSource_centeredHeightParameter]
  simp only [NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState,
    carryComplexTimeOfParameter_eq_centeredHeightParameter]

/-- Hermitian-polarized form of the completed-native scalar `dslope`.  The
conjugated first argument gives the same separation `w - conj z` as the gamma
Green identity. -/
def canonicalCompletedNativePolarizedDslopeKernel (z w : ℂ) : ℂ :=
  dslope
    (completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion)
    (conj z) w

/-- Exact final comparison: the concrete positive gamma kernel equals the
completed-native polarized `dslope` exactly when their division-free
numerators agree.  Thus no channel is discarded and no division is taken
near a collision. -/
theorem canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hseparation : w - conj z ≠ 0) :
    canonicalCompletedC3PolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        (w - conj z) *
          canonicalCompletedNativePolarizedDslopeKernel z w := by
  exact carryGammaComplex_inner_eq_kernel_iff_boundaryReadout_eq
    canonicalCompletedC3SixCameraSource
    canonicalCompletedNativePolarizedDslopeKernel
    z w hz hw hseparation

end

end CarrySelfAdjointOperator
