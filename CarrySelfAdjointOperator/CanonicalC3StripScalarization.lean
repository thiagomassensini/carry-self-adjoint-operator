import CarrySelfAdjointOperator.CanonicalC3GammaStateIdentity
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Canonical completed C3 scalarization on the natural strip

The global scalarization interface asks for an identity at every nonreal
centered-height parameter.  Zero confinement only needs the natural image of
the open Genuine strip.  This module records that minimal interface and proves
that it is exactly equivalent to the diagonal Green-energy identity of the
canonical total gamma state.

Because the preceding module identifies that private state literally with the
public completed-TFVD ledger state, the energy in this theorem is the already
proved positive C3 gamma energy.  The only datum not constructed here is the
scalar boundary-trace equality itself.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Completed Wronskian/Cauchy scalarization restricted to the centered image
of the open Genuine strip. -/
def HasCanonicalCompletedNativeGammaCauchyStripScalarization
    (source : ℂ → RealifiedCameraComplexification) : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z =
        (-(2 : ℂ) * Complex.I) *
          (completedGammaCauchySkew source z hz : ℂ)

/-- Equivalent strip-local diagonal Green identity in terms of the exact total
gamma-state norm. -/
def HasCanonicalCompletedNativeGammaStripDiagonalEnergy
    (source : ℂ → RealifiedCameraComplexification) : Prop :=
  ∀ (z : ℂ), operatorHeightParameter z ∈ genuineCriticalStrip →
    ∀ hz : z.im ≠ 0,
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z =
        (z - (starRingEnd ℂ) z) *
          ((‖totalCarryGammaState source z‖ ^ 2 : ℝ) : ℂ)

/-- On the natural strip, the Cauchy scalarization and the diagonal gamma
energy are the same statement. -/
theorem canonicalGammaCauchyStripScalarization_iff_diagonalEnergy
    (source : ℂ → RealifiedCameraComplexification) :
    HasCanonicalCompletedNativeGammaCauchyStripScalarization source ↔
      HasCanonicalCompletedNativeGammaStripDiagonalEnergy source := by
  constructor
  · intro hscalar z hzStrip hz
    rw [hscalar z hzStrip hz]
    unfold completedGammaCauchySkew
    rw [NativeCarryC3Crosswalk.carryGammaSource_cauchy_skew_energy]
    change _ = (z - (starRingEnd ℂ) z) *
      (((‖totalCarryGammaState source z‖ ^ 2 : ℝ)) : ℂ)
    rw [totalCarryGammaState_of_im_ne_zero source hz]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    apply Complex.ext <;> simp <;> ring
  · intro henergy z hzStrip hz
    have h := henergy z hzStrip hz
    unfold completedGammaCauchySkew
    rw [NativeCarryC3Crosswalk.carryGammaSource_cauchy_skew_energy]
    rw [totalCarryGammaState_of_im_ne_zero source hz,
      WithLp.prod_norm_sq_eq_of_L2] at h
    rw [h]
    apply Complex.ext <;> simp <;> ring

/-- Minimal scalarization interface for the canonical source which is already
identified with the public completed-TFVD ledger source. -/
def CanonicalCompletedC3GammaCauchyStripScalarization : Prop :=
  HasCanonicalCompletedNativeGammaCauchyStripScalarization
    canonicalCompletedC3SixCameraSource

/-- The same minimal interface written directly as the norm energy of the
exact private/public gamma state. -/
def CanonicalCompletedC3GammaStripDiagonalEnergy : Prop :=
  HasCanonicalCompletedNativeGammaStripDiagonalEnergy
    canonicalCompletedC3SixCameraSource

/-- Canonical strip scalarization is equivalent to the diagonal energy of the
exact completed-ledger gamma state. -/
theorem canonicalCompletedC3GammaCauchyStripScalarization_iff_energy :
    CanonicalCompletedC3GammaCauchyStripScalarization ↔
      CanonicalCompletedC3GammaStripDiagonalEnergy :=
  canonicalGammaCauchyStripScalarization_iff_diagonalEnergy
    canonicalCompletedC3SixCameraSource

/-- At a strip parameter, the energy side is literally the sum of squared
norms of the public completed-TFVD gamma-state components. -/
theorem canonicalCompletedC3StripEnergy_eq_seededGammaEnergy
    (henergy : CanonicalCompletedC3GammaStripDiagonalEnergy)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion
        (centeredHeightParameter s) (centeredHeightParameter s) =
      (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        ((‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
              s hoff).fst‖ ^ 2 +
            ‖(NativeCarryC3Crosswalk.seededCompletedTfvdCarryGammaState
              s hoff).snd‖ ^ 2 : ℝ) : ℂ) := by
  have hz : (centeredHeightParameter s).im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have h := henergy (centeredHeightParameter s) (by simpa using hs) hz
  rw [canonicalTotalCarryGammaState_centeredHeightParameter_eq_seeded s hoff,
    WithLp.prod_norm_sq_eq_of_L2] at h
  exact h

/-- The strip-local scalarization already suffices for unconditional public
Genuine-zero confinement. -/
theorem finalGenuineZeroConfinement_of_canonicalCompletedC3StripScalarization
    (hscalar : CanonicalCompletedC3GammaCauchyStripScalarization) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  by_contra hoff
  let z : ℂ := centeredHeightParameter s
  have hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [z] using hs
  have hzIm : z.im ≠ 0 := by
    simpa [z] using
      (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
  have hcharacteristic :
      completedNativeOperatorCharacteristic z = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta]
    · simp [z, genuineContinuation_eq_riemannZeta hs, hzero]
    · exact hzStrip
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z = 0 := by
    simp [completedGreenWronskian, hcharacteristic]
  have henergy :=
    (canonicalCompletedC3GammaCauchyStripScalarization_iff_energy.mp
      hscalar) z hzStrip hzIm
  rw [hwronskian] at henergy
  have hstate :
      totalCarryGammaState canonicalCompletedC3SixCameraSource z ≠ 0 := by
    simpa [z] using canonicalTotalCarryGammaState_ne_zero hs hoff
  have hnorm :
      ‖totalCarryGammaState canonicalCompletedC3SixCameraSource z‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hstate)
  have hnormComplex :
      ((‖totalCarryGammaState canonicalCompletedC3SixCameraSource z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hnorm
  have hfixed : z = (starRingEnd ℂ) z := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp henergy.symm).resolve_right hnormComplex
  have him := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at him
  exact hzIm (by linarith)

end

end CarrySelfAdjointOperator
