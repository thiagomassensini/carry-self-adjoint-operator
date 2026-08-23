import CarrySelfAdjointOperator.UnconditionalLimitConfinementProbe
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Canonical C3 gamma-energy normalization

The remaining completed scalarization compares the xi-completed scalar
Wronskian with the real Cauchy skew of the canonical completed C3 source.
The operatorial side of that comparison is already forced by the source
relation:

`CauchySkew(z,u) = -Im(z) * GammaEnergy(z,u)`.

This file isolates the exact complex normalization

`-2 i * CauchySkew = (z - conj z) * GammaEnergy`

and then identifies the private totalized gamma state, in centered-height
coordinates, with the public gamma state constructed from the uncollapsed
completed TFVD ledger.  Thus no Naimark, Cauchy, source, sign, or factor-two
ambiguity remains inside the scalar seam.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Positive real gamma energy of a selected all-bases source.  The totalized
state makes the definition available on the real axis as well, where it is
zero by construction. -/
def completedGammaEnergy
    (source : ℂ → RealifiedCameraComplexification) (z : ℂ) : ℝ :=
  ‖totalCarryGammaState source z‖ ^ 2

/-- The real Cauchy skew has exactly the complex normalization required by a
diagonal Green Wronskian.  This theorem contains the complete operatorial
content of the right-hand side of the remaining scalarization seam. -/
theorem neg_two_i_mul_completedGammaCauchySkew_eq_centeredFactor_mul_energy
    (source : ℂ → RealifiedCameraComplexification)
    (z : ℂ) (hz : z.im ≠ 0) :
    (-(2 : ℂ) * Complex.I) *
        (completedGammaCauchySkew source z hz : ℂ) =
      (z - (starRingEnd ℂ) z) *
        (completedGammaEnergy source z : ℂ) := by
  unfold completedGammaCauchySkew completedGammaEnergy
  rw [NativeCarryC3Crosswalk.carryGammaSource_cauchy_skew_energy]
  rw [totalCarryGammaState_of_im_ne_zero source hz]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  apply Complex.ext <;> simp <;> ring

/-- Energy-form spelling of the completed scalarization. -/
def HasCanonicalCompletedNativeGammaEnergyScalarization
    (source : ℂ → RealifiedCameraComplexification) : Prop :=
  ∀ (z : ℂ) (hz : z.im ≠ 0),
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      (z - (starRingEnd ℂ) z) *
        (completedGammaEnergy source z : ℂ)

/-- The Cauchy-skew seam and the gamma-energy seam are literally equivalent.
No positivity, zero, or confinement hypothesis is used in this conversion. -/
theorem canonicalCompletedNativeGammaCauchyScalarization_iff_energy
    (source : ℂ → RealifiedCameraComplexification) :
    HasCanonicalCompletedNativeGammaCauchyScalarization source ↔
      HasCanonicalCompletedNativeGammaEnergyScalarization source := by
  constructor
  · intro hscalar z hz
    rw [hscalar z hz]
    exact
      neg_two_i_mul_completedGammaCauchySkew_eq_centeredFactor_mul_energy
        source z hz
  · intro henergy z hz
    rw [henergy z hz]
    exact
      (neg_two_i_mul_completedGammaCauchySkew_eq_centeredFactor_mul_energy
        source z hz).symm

/-- Canonical completed C3 gamma energy. -/
def canonicalCompletedC3GammaEnergy (z : ℂ) : ℝ :=
  completedGammaEnergy canonicalCompletedC3SixCameraSource z

/-- The canonical energy is strictly positive at every nonreal centered
parameter whose spectral parameter lies in the open Genuine strip. -/
theorem canonicalCompletedC3GammaEnergy_pos
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    0 < canonicalCompletedC3GammaEnergy z := by
  unfold canonicalCompletedC3GammaEnergy completedGammaEnergy
  have hstate :
      totalCarryGammaState canonicalCompletedC3SixCameraSource z ≠ 0 :=
    totalCarryGammaState_ne_zero_of_source_ne_zero
      canonicalCompletedC3SixCameraSource hz
      (canonicalCompletedC3SixCameraSource_ne_zero hs)
  exact pow_pos (norm_pos_iff.mpr hstate) 2

/-- In centered-height coordinates, the private total gamma state is exactly
the public gamma state obtained from the uncollapsed completed TFVD ledger. -/
theorem canonicalCompletedC3TotalGammaState_centeredHeightParameter
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    totalCarryGammaState canonicalCompletedC3SixCameraSource
        (centeredHeightParameter s) =
      NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff := by
  have hz : (centeredHeightParameter s).im ≠ 0 := by
    rw [← carryComplexTimeOfParameter_eq_centeredHeightParameter]
    exact
      NativeCarryC3Crosswalk.
        carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff
  rw [totalCarryGammaState_of_im_ne_zero
      canonicalCompletedC3SixCameraSource hz,
    canonicalCompletedC3SixCameraSource_centeredHeightParameter]
  unfold NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
  rw [carryComplexTimeOfParameter_eq_centeredHeightParameter]

/-- Therefore the private canonical energy is literally the positive gamma
energy already proved for the public completed TFVD ledger. -/
theorem canonicalCompletedC3GammaEnergy_centeredHeightParameter
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3GammaEnergy (centeredHeightParameter s) =
      ‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff).fst‖ ^ 2 +
        ‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState s hoff).snd‖ ^ 2 := by
  unfold canonicalCompletedC3GammaEnergy completedGammaEnergy
  rw [canonicalCompletedC3TotalGammaState_centeredHeightParameter s hoff]
  rw [WithLp.prod_norm_sq_eq_of_L2]

/-- Canonical specialization of the Cauchy/energy equivalence. -/
theorem canonicalCompletedC3GammaCauchyScalarization_iff_energy :
    CanonicalCompletedC3GammaCauchyScalarizationSeam ↔
      HasCanonicalCompletedNativeGammaEnergyScalarization
        canonicalCompletedC3SixCameraSource :=
  canonicalCompletedNativeGammaCauchyScalarization_iff_energy
    canonicalCompletedC3SixCameraSource

end

end CarrySelfAdjointOperator
