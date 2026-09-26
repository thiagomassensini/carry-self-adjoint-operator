import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenPhysicalFourCornerCrosswalk
import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedRealAxisConvolution
import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenNontrivialWitness
import Mathlib.Tactic

/-!
# Real first variation of the physical holomorphic Green presentation

The physical comparison from the independent-reflected carrier to the
historical four-corner cell is made on `v = conj u`; it is therefore a
value-level comparison only.  This file uses the real line as the legitimate
one-dimensional interface.  It keeps separate:

* the holomorphic camera-pair kernel, whose literal first jet differentiates
  the independent reflected coordinate `v` with `u` fixed; and
* the phase-normalized physical carrier, restricted to `u = v = (t : ℂ)`.

The discrete/TFVD information is not differentiated here.  In particular,
no complex derivative of `u ↦ K (u, conj u)` is formed.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Finite
open FiniteNativeCarryOperator.Camera

noncomputable section
set_option autoImplicit false

/-! ## The holomorphic real diagonal -/

/-- The real diagonal of one camera-pair holomorphic kernel.  This is not the
physical phase-normalized kernel: it keeps the C3 eigenvalue polarization. -/
def canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) (t : ℝ) : ℂ :=
  canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
    M q hq0 hq1 S (t : ℂ) (t : ℂ) directCamera reflectedCamera

/-- The direct holomorphic port is constant over the independent-reflected
plane, because its reconstructed `w` source is constant. -/
theorem cameraResolvedIndependentReflectedHolomorphicDirectGreenPort_independent
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ v₁ u₂ v₂ : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
      M q hq0 hq1 S u₁ v₁ camera =
    cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
      M q hq0 hq1 S u₂ v₂ camera := by
  unfold cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_wSource_independent]

/-- The reflected holomorphic port is independent of the direct coordinate
`u`; its only variable source coordinate is the independent reflected height
`v`. -/
theorem cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (camera : ℕ) :
    cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
      M q hq0 hq1 S u₁ v camera =
    cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
      M q hq0 hq1 S u₂ v camera := by
  unfold cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
  rw [cameraResolvedIndependentReflectedSixSourceReconstruction_reflectedZSource_independent_u]

/-- Thus the holomorphic camera-pair kernel itself is independent of `u`.
This is the exact dependency audit needed to compare its real diagonal with
the pre-existing literal `v`-jet. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_independent_u
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (u₁ u₂ v : ℂ) (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
      M q hq0 hq1 S u₁ v directCamera reflectedCamera =
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
      M q hq0 hq1 S u₂ v directCamera reflectedCamera := by
  unfold canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
  rw [cameraResolvedIndependentReflectedHolomorphicDirectGreenPort_independent,
    cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort_independent_u]

/-- Restricting the holomorphic kernel to the real diagonal changes no
derivative direction: by the preceding independence theorem it is the real
restriction of the `v`-function at fixed `u = 0`. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_eq_fixedU
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
      M q hq0 hq1 S directCamera reflectedCamera =
      fun t : ℝ =>
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
          M q hq0 hq1 S 0 (t : ℂ) directCamera reflectedCamera := by
  funext t
  exact canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_independent_u
    M q hq0 hq1 S (t : ℂ) 0 (t : ℂ) directCamera reflectedCamera

/-- The honest real derivative of the holomorphic real diagonal is exactly
the already-defined first holomorphic jet.  There is no direct-coordinate
contribution: it vanished through the established `u`-independence, not by
an unproved chain-rule cancellation. -/
theorem deriv_canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_firstJet
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) :
    deriv
      (canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
        M q hq0 hq1 S directCamera reflectedCamera) 0 =
      canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
        M q hq0 hq1 S 0 directCamera reflectedCamera 1 := by
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_eq_fixedU]
  rw [deriv_comp_ofReal_eq
    (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_analyticAt_zero
      M q hq0 hq1 S 0 directCamera reflectedCamera).differentiableAt]
  simp only [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient,
    iteratedDeriv_one, Nat.factorial_one]
  norm_num

/-- The prior same-camera/nonzero-pair witness therefore survives as a
nonzero first variation of the holomorphic real diagonal.  It is explicitly
*not* a witness for the phase-normalized physical pullback defined below. -/
theorem exists_cameraPair_deriv_holomorphicRealDiagonalGreen_ne_zero
    (M : ℕ) (hM : 0 < M) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∃ directCamera ∈ canonicalFiniteCameraAtlas M,
      ∃ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
        deriv
          (canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
            M q hqpos.le hq1 S directCamera reflectedCamera) 0 ≠ 0 := by
  rcases exists_cameraPair_holomorphicGreenFirstJet_ne_zero M hM q hqpos hq1 S with
    ⟨directCamera, hdirect, reflectedCamera, hreflected, hjet⟩
  refine ⟨directCamera, hdirect, reflectedCamera, hreflected, ?_⟩
  rw [deriv_canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_firstJet]
  exact hjet

/-! ## The sewn holomorphic real diagonal -/

/-- The real diagonal of the sewn canonical holomorphic Green boundary. -/
def canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) : ℂ :=
  canonicalC3IndependentReflectedHolomorphicGreenBoundary
    M q hq0 hq1 S (t : ℂ) (t : ℂ)

/-- Sewing after real restriction is the literal finite double sum of the
real-diagonal camera-pair holomorphic kernels. -/
theorem canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_eq_cameraPairwise
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen M q hq0 hq1 S t =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
            M q hq0 hq1 S directCamera reflectedCamera t := by
  unfold canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
  rw [canonicalC3IndependentReflectedHolomorphicGreenBoundary_eq_cameraPairwise]
  rfl

/-- The real-diagonal camera kernel has the expected `HasDerivAt` witness at
the literal first holomorphic jet.  This is the real restriction of the
analytic fixed-`u` kernel, after the proven `u`-independence rewrite. -/
theorem hasDerivAt_canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (directCamera reflectedCamera : ℕ) :
    HasDerivAt
      (canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
        M q hq0 hq1 S directCamera reflectedCamera)
      (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
        M q hq0 hq1 S 0 directCamera reflectedCamera 1) 0 := by
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_eq_fixedU]
  have hcomplex :=
    (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_analyticAt_zero
      M q hq0 hq1 S 0 directCamera reflectedCamera).differentiableAt.hasDerivAt
  convert hcomplex.comp_ofReal using 1 <;>
    simp [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient,
      iteratedDeriv_one]

/-- The first real variation of the sewn holomorphic carrier is the finite
sum of its literal first camera-pair jets. -/
theorem deriv_canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_cameraPairwiseFirstJetSum
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
      M q hq0 hq1 S) 0 =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
            M q hq0 hq1 S 0 directCamera reflectedCamera 1 := by
  rw [show canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
      M q hq0 hq1 S =
      fun t : ℝ =>
        ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
            canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
              M q hq0 hq1 S directCamera reflectedCamera t by
        funext t
        exact canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_eq_cameraPairwise
          M q hq0 hq1 S t]
  have hsumfun : (fun t : ℝ =>
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
            M q hq0 hq1 S directCamera reflectedCamera t) =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
            M q hq0 hq1 S directCamera reflectedCamera := by
    funext t
    simp only [Finset.sum_apply]
  rw [hsumfun]
  exact (HasDerivAt.sum (fun directCamera _ =>
    HasDerivAt.sum (fun reflectedCamera _ =>
      hasDerivAt_canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_zero
        M q hq0 hq1 S directCamera reflectedCamera))).deriv

/-- Expanding the sewn real holomorphic variation leaves the C3 eigenvalue
derivative multiplying the literal central ordinary-source pairings. -/
theorem deriv_canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_scaledCentralInnerSum
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
      M q hq0 hq1 S) 0 =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          holomorphicC3EigenvalueDerivativeAtZero *
            canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
              M q hq0 hq1 S 0 directCamera reflectedCamera 0 := by
  rw [deriv_canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_cameraPairwiseFirstJetSum]
  apply Finset.sum_congr rfl
  intro directCamera _
  apply Finset.sum_congr rfl
  intro reflectedCamera _
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient_one_eq_scaledCentralInner]

/-- The scalar multiplying the sewn central pairings is exactly the C3
critical amplitude times the native logarithmic-clock frequency `-i log 3`.
No real/imaginary projection is imposed here: this remains a complex Green
readout. -/
theorem deriv_canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_logClockCentralInnerSum
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
      M q hq0 hq1 S) 0 =
      ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          (nativeCriticalDirichletAmplitude 3 *
              (-Complex.I * (Real.log (3 : ℝ) : ℂ))) *
            canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
              M q hq0 hq1 S 0 directCamera reflectedCamera 0 := by
  rw [deriv_canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_zero_eq_scaledCentralInnerSum,
    holomorphicC3EigenvalueDerivativeAtZero_eq_logClockFrequency]

/-! ## The physical real pullback -/

/-- The physical normalized Green boundary restricted to the real line.  The
definition uses the literal real diagonal; the following lemma records that
it is also the physical conjugate section there. -/
def canonicalC3IndependentReflectedPhysicalRealGreen
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) : ℂ :=
  canonicalC3IndependentReflectedCorrectedGreenBoundary
    M q hq0 hq1 S (t : ℂ) (t : ℂ)

/-- Complex conjugation fixes the chosen real physical parameter. -/
theorem canonicalC3PhysicalRealParameter_conj (t : ℝ) :
    (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by
  simp

/-- On the real line the physical pullback is literally the conjugate
physical section. -/
theorem canonicalC3IndependentReflectedPhysicalRealGreen_eq_physicalSection
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedPhysicalRealGreen M q hq0 hq1 S t =
      canonicalC3IndependentReflectedCorrectedGreenBoundary
        M q hq0 hq1 S (t : ℂ) ((starRingEnd ℂ) (t : ℂ)) := by
  simp [canonicalC3IndependentReflectedPhysicalRealGreen]

/-- The real physical pullback is the historical four-corner component with
the exact `3 * M` prefix and fixed second height.  This is equality of real
functions, not a complex differentiation of the conjugate section. -/
theorem canonicalC3PhysicalRealGreen_eq_historicalFourCorner
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S t =
      canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
        (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0) := by
  rw [canonicalC3IndependentReflectedPhysicalRealGreen_eq_physicalSection]
  exact canonicalC3PhysicalDressedHolomorphicGreen_eq_historicalFourCorner
    M q hqpos hq1 S (t : ℂ)

/-! ## Phase cancellation on the physical real line -/

/-- On the real physical line the historical mixed radial coefficient is
zero.  Both radial factors are one: the reflected-height relation first turns
the historical reflected parameter into the same real independent coordinate.
This is a value statement about the physical presentation. -/
theorem canonicalC3MixedRadialCoefficient_operatorHeightParameter_ofReal_eq_zero
    (t : ℝ) :
    canonicalC3MixedRadialCoefficient (operatorHeightParameter (t : ℂ))
      (operatorHeightParameter 0) = 0 := by
  unfold canonicalC3MixedRadialCoefficient
  rw [reflectedParameter_operatorHeightParameter_eq_operatorHeightParameter_conj]
  change canonicalC3IndependentReflectedRadialGreenFactor
      ((starRingEnd ℂ) (t : ℂ)) -
      canonicalC3IndependentReflectedRadialGreenFactor 0 = 0
  simp [canonicalC3IndependentReflectedRadialGreenFactor_ofReal]

/-- Consequently the physical phase-normalized Green boundary vanishes on
the real physical line.  This uses the historical mixed-radial coefficient,
not the earlier analytic germ theorem for the diagonal undressed carrier. -/
theorem canonicalC3IndependentReflectedPhysicalRealGreen_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S t = 0 := by
  rw [canonicalC3PhysicalRealGreen_eq_historicalFourCorner M q hqpos hq1 S t,
    canonicalCompletedNativeHistoricalFourCornerGreenComponent_eq,
    canonicalC3MixedRadialCoefficient_operatorHeightParameter_ofReal_eq_zero]
  simp

/-- The physical normalized first variation on the real line is therefore
zero.  This makes explicit the phase-normalization cancellation which prevents
identifying the physical derivative with the nonzero holomorphic `v`-jet. -/
theorem deriv_canonicalC3IndependentReflectedPhysicalRealGreen_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S) 0 = 0 := by
  rw [show canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S =
      fun _ : ℝ => 0 by
        funext t
        exact canonicalC3IndependentReflectedPhysicalRealGreen_eq_zero
          M q hqpos hq1 S t]
  simp

/-- The same honest real first variation of the historical four-corner
presentation vanishes, by the physical real crosswalk. -/
theorem deriv_canonicalC3HistoricalFourCornerPhysicalReal_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (fun t : ℝ =>
      canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
        (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)) 0 = 0 := by
  have hfun : (fun t : ℝ =>
      canonicalCompletedNativeHistoricalFourCornerGreenComponent (3 * M)
        (operatorHeightParameter (t : ℂ)) (operatorHeightParameter 0)) =
      canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S := by
    funext t
    exact (canonicalC3PhysicalRealGreen_eq_historicalFourCorner
      M q hqpos hq1 S t).symm
  rw [hfun]
  exact deriv_canonicalC3IndependentReflectedPhysicalRealGreen_zero M q hqpos hq1 S

/-! ## Exact first-order phase complement -/

/-- The phase complement compares presentations only after both have been
pulled back to the same real parameter.  It is not an error term: it records
the complete change from the holomorphic eigenvalue polarization to the
physical phase-normalized presentation. -/
def canonicalC3IndependentReflectedPhysicalRealPhaseComplement
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) : ℝ → ℂ :=
  canonicalC3IndependentReflectedPhysicalRealGreen M q hq0 hq1 S -
    canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen M q hq0 hq1 S

/-- The phase complement has the negative of the sewn holomorphic first
variation.  The statement is exact: on the real physical line the normalized
Green presentation is zero, while the holomorphic polarization retains its
nontrivial first-order information. -/
theorem deriv_canonicalC3IndependentReflectedPhysicalRealPhaseComplement_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedPhysicalRealPhaseComplement
      M q hqpos.le hq1 S) 0 =
      - ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
            canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
              M q hqpos.le hq1 S 0 directCamera reflectedCamera 1 := by
  have hphysical : HasDerivAt
      (canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S)
      0 0 := by
    rw [show canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S =
        fun _ : ℝ => 0 by
          funext t
          exact canonicalC3IndependentReflectedPhysicalRealGreen_eq_zero
            M q hqpos hq1 S t]
    exact hasDerivAt_const (x := 0) (c := (0 : ℂ))
  have hholomorphic : HasDerivAt
      (canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
        M q hqpos.le hq1 S)
      (∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
            M q hqpos.le hq1 S 0 directCamera reflectedCamera 1) 0 := by
    rw [show canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen
        M q hqpos.le hq1 S =
        fun t : ℝ =>
          ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
            ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
              canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
                M q hqpos.le hq1 S directCamera reflectedCamera t by
          funext t
          exact canonicalC3IndependentReflectedHolomorphicRealDiagonalGreen_eq_cameraPairwise
            M q hqpos.le hq1 S t]
    have hsumfun : (fun t : ℝ =>
        ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
            canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
              M q hqpos.le hq1 S directCamera reflectedCamera t) =
        ∑ directCamera ∈ canonicalFiniteCameraAtlas M,
          ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
            canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen
              M q hqpos.le hq1 S directCamera reflectedCamera := by
      funext t
      simp only [Finset.sum_apply]
    rw [hsumfun]
    exact HasDerivAt.sum (fun directCamera _ =>
      HasDerivAt.sum (fun reflectedCamera _ =>
        hasDerivAt_canonicalC3CameraResolvedIndependentReflectedHolomorphicRealDiagonalGreen_zero
          M q hqpos.le hq1 S directCamera reflectedCamera))
  simpa [canonicalC3IndependentReflectedPhysicalRealPhaseComplement] using
    (hphysical.sub hholomorphic).deriv

/-- The real physical first variation has the exact decomposition with unit
coefficient on the sewn holomorphic first variation and the explicit phase
complement.  Thus the coefficient `α₀` in this presentation is literally
`1`; its phase complement cancels that contribution on the real physical
line, rather than a direct-coordinate derivative doing so. -/
theorem deriv_canonicalC3IndependentReflectedPhysicalRealGreen_zero_eq_holomorphicFirstJetSum_add_phaseComplement
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    deriv (canonicalC3IndependentReflectedPhysicalRealGreen M q hqpos.le hq1 S) 0 =
      (∑ directCamera ∈ canonicalFiniteCameraAtlas M,
        ∑ reflectedCamera ∈ canonicalFiniteCameraAtlas M,
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
            M q hqpos.le hq1 S 0 directCamera reflectedCamera 1) +
      deriv (canonicalC3IndependentReflectedPhysicalRealPhaseComplement
        M q hqpos.le hq1 S) 0 := by
  rw [deriv_canonicalC3IndependentReflectedPhysicalRealGreen_zero M q hqpos hq1 S,
    deriv_canonicalC3IndependentReflectedPhysicalRealPhaseComplement_zero M q hqpos hq1 S]
  ring

/-!
The two preceding derivative theorems are deliberately not combined into a
false equality between a physical normalized derivative and a holomorphic
camera-pair jet.  The physical phase dress has already converted the
holomorphic eigenvalue into the real radial multiplier, which is identically
one on this line; its mixed Green collision coefficient is therefore zero.
-/

end

end CarrySelfAdjointOperator
