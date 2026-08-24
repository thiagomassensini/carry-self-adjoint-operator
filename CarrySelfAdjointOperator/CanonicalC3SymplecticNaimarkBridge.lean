import CarrySelfAdjointOperator.CanonicalC3GreenIntertwiner
import CarrySelfAdjointOperator.CanonicalC3SixCameraSource
import NativeCarryC3Crosswalk.CompletedTfvdNaimarkFeasibility
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

/-!
# Symplectic C3 bridge to the global Naimark space

The faithful six-camera source retains every real coordinate, but its split
into real and imaginary channels is not the symplectic split used by the
intrinsic C3 Green form.  This file constructs the corrected split.

Each complex C3 leg is first realified isometrically through its standard
finite-dimensional real orthonormal basis.  Its real coordinates are embedded
in the all-bases camera completion through an orthonormal family obtained from
literal camera vectors.  A boundary pair
`(x₁, x₂)` is then sent to `(-R x₁, R x₂)`.  The ambient real Green skew is
therefore exactly the real part of the intrinsic complex Green form.  The
coordinatewise Naimark isometry preserves this identity.

This is a finite/core transport theorem.  It does not identify the resulting
Green value with the completed scalar Wronskian; that remains a separate
scalar boundary compatibility statement.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

open scoped RealInnerProductSpace

noncomputable section

/-- The real orthonormal-coordinate index of one complex C3 boundary leg. -/
abbrev CanonicalC3RealCoordinate :=
  Fin (Module.finrank ℝ
    (NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3))

/-- One three-cell complex leg has exactly six real Hilbert coordinates. -/
theorem finiteC3GreenBoundarySpace_real_finrank_eq_six :
    Module.finrank ℝ
      (NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3) = 6 := by
  rw [← Module.finrank_mul_finrank ℝ ℂ
    (NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3)]
  norm_num [Complex.finrank_real_complex]

/-- Canonical realification of one three-cell complex C3 boundary leg. -/
def canonicalC3LegRealification :
    NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3 ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ CanonicalC3RealCoordinate :=
  (stdOrthonormalBasis ℝ
    (NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3)).repr

/-- The coordinatewise real Hilbert structure on a finite complex C3 leg is
the real part of its complex Hilbert structure. -/
theorem finiteC3GreenBoundarySpace_real_inner_eq_re_inner
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace 3) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  calc
    (∑ i, inner ℝ (x i) (y i)) =
        ∑ i, (inner ℂ (x i) (y i)).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact real_inner_eq_re_inner ℂ (x i) (y i)
    _ = (∑ i, inner ℂ (x i) (y i)).re := by
      exact (map_sum Complex.reAddGroupHom
        (fun i ↦ inner ℂ (x i) (y i)) Finset.univ).symm

/-- Distinct literal camera labels assigned to the real coordinates. -/
def canonicalC3RealCoordinateCameraIndex
    (j : CanonicalC3RealCoordinate) : CameraIndex :=
  ⟨j.val + 2, by omega⟩

theorem canonicalC3RealCoordinateCameraIndex_injective :
    Function.Injective canonicalC3RealCoordinateCameraIndex := by
  intro i j hij
  have hval := congrArg Subtype.val hij
  simp [canonicalC3RealCoordinateCameraIndex] at hval
  apply Fin.ext
  omega

/-- Six linearly independent vectors in the global camera completion. -/
def canonicalC3RawCameraVector
    (j : CanonicalC3RealCoordinate) : CameraHilbert :=
  cameraVector (canonicalC3RealCoordinateCameraIndex j)

theorem canonicalC3RawCameraVector_linearIndependent :
    LinearIndependent ℝ canonicalC3RawCameraVector := by
  have hsingle : LinearIndependent ℝ
      (fun camera : CameraIndex ↦
        Finsupp.single camera (1 : ℝ) : CameraIndex → CameraFinsupp) :=
    Finsupp.linearIndependent_single_one ℝ CameraIndex
  have hrestricted : LinearIndependent ℝ
      (fun j : CanonicalC3RealCoordinate ↦
        Finsupp.single (canonicalC3RealCoordinateCameraIndex j) (1 : ℝ)) :=
    hsingle.comp canonicalC3RealCoordinateCameraIndex
      canonicalC3RealCoordinateCameraIndex_injective
  exact hrestricted.map' cameraEmbedding.toLinearMap
    (LinearMap.ker_eq_bot.mpr cameraEmbedding.injective)

/-- Orthonormalized six-camera family in the global completion. -/
def canonicalC3OrthonormalCameraVector
    (j : CanonicalC3RealCoordinate) : CameraHilbert :=
  InnerProductSpace.gramSchmidtNormed ℝ canonicalC3RawCameraVector j

theorem canonicalC3OrthonormalCameraVector_orthonormal :
    Orthonormal ℝ canonicalC3OrthonormalCameraVector :=
  InnerProductSpace.gramSchmidtNormed_orthonormal
    canonicalC3RawCameraVector_linearIndependent

/-- Linear synthesis of the six Euclidean coordinates into the global
camera completion. -/
def canonicalC3CameraCoordinateLinearMap :
    EuclideanSpace ℝ CanonicalC3RealCoordinate →ₗ[ℝ] CameraHilbert where
  toFun x := ∑ j : CanonicalC3RealCoordinate,
    x j • canonicalC3OrthonormalCameraVector j
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul,
      smul_smul, Finset.smul_sum]

@[simp] theorem canonicalC3CameraCoordinateLinearMap_basisFun
    (j : CanonicalC3RealCoordinate) :
    canonicalC3CameraCoordinateLinearMap
        (EuclideanSpace.basisFun CanonicalC3RealCoordinate ℝ j) =
      canonicalC3OrthonormalCameraVector j := by
  classical
  simp [canonicalC3CameraCoordinateLinearMap]

/-- Isometric six-coordinate inclusion in the all-bases camera Hilbert
space. -/
def canonicalC3CameraCoordinateIsometry :
    EuclideanSpace ℝ CanonicalC3RealCoordinate →ₗᵢ[ℝ] CameraHilbert :=
  canonicalC3CameraCoordinateLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun
      CanonicalC3RealCoordinate ℝ).toBasis)
    (EuclideanSpace.basisFun CanonicalC3RealCoordinate ℝ).orthonormal
    (by
      change Orthonormal ℝ
        (fun j : CanonicalC3RealCoordinate ↦
          canonicalC3CameraCoordinateLinearMap
            (EuclideanSpace.basisFun
              CanonicalC3RealCoordinate ℝ j))
      simpa only [canonicalC3CameraCoordinateLinearMap_basisFun] using
        canonicalC3OrthonormalCameraVector_orthonormal)

/-- Symplectic real packing of a complete C3 boundary pair.  The minus sign
is applied before the final real Green readout. -/
def canonicalC3SymplecticCameraPackingLinearMap :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 →ₗ[ℝ]
      RealifiedCameraComplexification where
  toFun x := WithLp.toLp 2
    (-canonicalC3CameraCoordinateIsometry
        (canonicalC3LegRealification x.1),
      canonicalC3CameraCoordinateIsometry
        (canonicalC3LegRealification x.2))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        -canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification (x.1 + y.1)) =
          -canonicalC3CameraCoordinateIsometry
              (canonicalC3LegRealification x.1) +
            -canonicalC3CameraCoordinateIsometry
              (canonicalC3LegRealification y.1)
      rw [map_add, map_add]
      abel
    · change
        canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification (x.2 + y.2)) =
          canonicalC3CameraCoordinateIsometry
              (canonicalC3LegRealification x.2) +
            canonicalC3CameraCoordinateIsometry
              (canonicalC3LegRealification y.2)
      rw [map_add, map_add]
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change
        -canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification (r • x.1)) =
          r • (-canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification x.1))
      rw [map_smul, map_smul, smul_neg]
    · change
        canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification (r • x.2)) =
          r • canonicalC3CameraCoordinateIsometry
            (canonicalC3LegRealification x.2)
      rw [map_smul, map_smul]

/-- Continuous symplectic C3 packing; boundedness is automatic because the
source is finite-dimensional. -/
def canonicalC3SymplecticCameraPacking :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 →L[ℝ]
      RealifiedCameraComplexification :=
  LinearMap.toContinuousLinearMap
    canonicalC3SymplecticCameraPackingLinearMap

@[simp] theorem canonicalC3SymplecticCameraPacking_apply
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    canonicalC3SymplecticCameraPacking x = WithLp.toLp 2
      (-canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.1),
        canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.2)) :=
  rfl

/-- No C3 boundary coordinate is lost by the symplectic packing. -/
theorem canonicalC3SymplecticCameraPacking_injective :
    Function.Injective canonicalC3SymplecticCameraPacking := by
  intro x y hxy
  have hp := congrArg
    (WithLp.ofLp : RealifiedCameraComplexification →
      CameraHilbert × CameraHilbert) hxy
  have hfst :
      -canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.1) =
        -canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification y.1) := by
    simpa only [canonicalC3SymplecticCameraPacking_apply] using
      congrArg Prod.fst hp
  have hsnd :
      canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.2) =
        canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification y.2) := by
    simpa only [canonicalC3SymplecticCameraPacking_apply] using
      congrArg Prod.snd hp
  apply Prod.ext
  · apply canonicalC3LegRealification.injective
    apply canonicalC3CameraCoordinateIsometry.injective
    exact neg_injective hfst
  · apply canonicalC3LegRealification.injective
    apply canonicalC3CameraCoordinateIsometry.injective
    exact hsnd

/-- The corrected packing intertwines the intrinsic complex Green form with
the ambient real Green skew exactly. -/
theorem realifiedGreenSkew_canonicalC3SymplecticCameraPacking
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (canonicalC3SymplecticCameraPacking x)
        (canonicalC3SymplecticCameraPacking y) =
      (greenForm (𝕜 := ℂ) x y).re := by
  change
    inner ℝ
        (-canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.1))
        (canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification y.2)) -
      inner ℝ
        (canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification x.2))
        (-canonicalC3CameraCoordinateIsometry
          (canonicalC3LegRealification y.1)) = _
  simp only [inner_neg_left, inner_neg_right]
  rw [canonicalC3CameraCoordinateIsometry.inner_map_map,
    canonicalC3CameraCoordinateIsometry.inner_map_map,
    canonicalC3LegRealification.inner_map_map,
    canonicalC3LegRealification.inner_map_map]
  rw [finiteC3GreenBoundarySpace_real_inner_eq_re_inner,
    finiteC3GreenBoundarySpace_real_inner_eq_re_inner]
  simp [greenForm]
  ring

/-- Naimark realization of the corrected complete C3 boundary pair. -/
def canonicalC3SymplecticNaimarkRealization :
    NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedNaimarkPort ∘L canonicalC3SymplecticCameraPacking

theorem canonicalC3SymplecticNaimarkRealization_injective :
    Function.Injective canonicalC3SymplecticNaimarkRealization := by
  intro x y hxy
  apply canonicalC3SymplecticCameraPacking_injective
  apply realifiedNaimarkPort_injective
  exact hxy

/-- The global Naimark promotion preserves the corrected Green identity. -/
theorem realifiedGreenSkew_canonicalC3SymplecticNaimarkRealization
    (x y : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (canonicalC3SymplecticNaimarkRealization x)
        (canonicalC3SymplecticNaimarkRealization y) =
      (greenForm (𝕜 := ℂ) x y).re := by
  rw [show canonicalC3SymplecticNaimarkRealization x =
      realifiedNaimarkPort (canonicalC3SymplecticCameraPacking x) from rfl,
    show canonicalC3SymplecticNaimarkRealization y =
      realifiedNaimarkPort (canonicalC3SymplecticCameraPacking y) from rfl,
    NativeCarryC3Crosswalk.realifiedGreenSkew_realifiedNaimarkPort]
  exact realifiedGreenSkew_canonicalC3SymplecticCameraPacking x y

/-- The actual enriched C3 state promoted through the corrected global
Naimark bridge. -/
def canonicalCompletedC3SymplecticNaimarkState
    (z : ℂ) : RealifiedNaimarkComplexification :=
  canonicalC3SymplecticNaimarkRealization
    (canonicalCompletedOperatorC3State z)

/-- The corrected global state remains nonzero throughout the operator image
of the open critical strip. -/
theorem canonicalCompletedC3SymplecticNaimarkState_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3SymplecticNaimarkState z ≠ 0 := by
  intro hzero
  apply canonicalEnrichedC3SourcePort_ne_zero hs
  apply canonicalC3SymplecticNaimarkRealization_injective
  simpa [canonicalCompletedC3SymplecticNaimarkState,
    canonicalCompletedOperatorC3State] using hzero

/-- On the direct/reflected canonical C3 pair, the global Naimark skew is the
real part of the exact radial Green factorization. -/
theorem canonicalC3SymplecticNaimarkReflectedGreenSkew_eq_radialFactorization
    (s : ℂ) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (canonicalC3SymplecticNaimarkRealization
          (canonicalEnrichedC3SourcePort s))
        (canonicalC3SymplecticNaimarkRealization
          (canonicalEnrichedC3SourcePort (reflectedParameter s))) =
      cpRadialDifference 3 (criticalDisplacement s.re) *
        (finiteReflectedGradientPairing 3 s).re := by
  rw [realifiedGreenSkew_canonicalC3SymplecticNaimarkRealization]
  change (canonicalEnrichedC3ReflectedGreenBulk s).re = _
  rw [canonicalEnrichedC3ReflectedGreenBulk_eq_radialFactorization]
  simp

/-- In the open strip, the corrected global Green skew vanishes exactly on
the critical line. -/
theorem canonicalC3SymplecticNaimarkReflectedGreenSkew_eq_zero_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryC3Crosswalk.realifiedGreenSkew
        (canonicalC3SymplecticNaimarkRealization
          (canonicalEnrichedC3SourcePort s))
        (canonicalC3SymplecticNaimarkRealization
          (canonicalEnrichedC3SourcePort (reflectedParameter s))) = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [canonicalC3SymplecticNaimarkReflectedGreenSkew_eq_radialFactorization,
    mul_eq_zero]
  have hpairing :
      (finiteReflectedGradientPairing 3 s).re ≠ 0 :=
    ne_of_gt
      (finiteReflectedGradientPairing_re_pos (by norm_num) hs)
  simp only [hpairing, or_false]
  constructor
  · intro hradial
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    rw [hcritical]
    simp [cpRadialDifference]

end

end CarrySelfAdjointOperator
