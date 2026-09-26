import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedUndressedGreen
import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedUndressedGreenAnalytic
import Mathlib.Tactic

/-!
# Holomorphic Green polarization before phase normalization

The diagonal positive-source substrate has equal Green legs.  The historical
holomorphic C3 port restores the spectral eigenvalue in its first leg before
the physical phase/radial normalization is applied.  This file records that
three-stage separation without modifying `undressedGreenPort`.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open CanonicalC3AllCutoffMixedSourceHilbert

noncomputable section
set_option autoImplicit false

/-! ## The three Green-port layers -/

/-- The holomorphic Green polarization of the positive diagonal substrate.
Its first leg retains the C3 shift eigenvalue `3 ^ (-s)`. -/
def holomorphicGreenPort
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    FiniteC3GreenPortCarrier N :=
  radialGreenDress (natDirichletTerm s 3) (undressedGreenPort N state)

@[simp] theorem holomorphicGreenPort_fst_apply
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (holomorphicGreenPort N s state).1 n =
      natDirichletTerm s 3 * state.1 (n : ℕ) := by
  rfl

@[simp] theorem holomorphicGreenPort_snd_apply
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) (n : Fin N) :
    (holomorphicGreenPort N s state).2 n = state.1 (n : ℕ) := by
  rfl

/-- On the canonical finite prefix, the newly named holomorphic port is
literally the historical undressed C3 Green boundary pair. -/
theorem holomorphicGreenPort_prefix_eq_finiteC3HolomorphicGenuineGreenBoundaryPair
    (M : ℕ) (s : ℂ) :
    holomorphicGreenPort M s (canonicalCompletedC3HilbertPrefixState s M) =
      finiteC3HolomorphicGenuineGreenBoundaryPair M s := by
  rw [holomorphicGreenPort, undressedGreenPort_prefix_eq_positiveDiagonal]
  exact (finiteC3HolomorphicGenuineGreenBoundaryPair_eq_eigenvalueDress M s).symm

/-- The phase normalizer converts the holomorphic C3 eigenvalue to exactly
the first-leg multiplier of the physical normalized port. -/
theorem cpPhaseNormalizer_mul_holomorphicC3Eigenvalue
    (s : ℂ) :
    cpPhaseNormalizer 3 s * natDirichletTerm s 3 = c3RadialGreenFactor s := by
  simpa [c3RadialGreenFactor] using
    (cpPhaseNormalizer_mul_eigenvalue 3 (by norm_num : Nat.Prime 3) s)

/-- The physical normalized port is phase-normalizer dressing after, rather
than instead of, the holomorphic Green polarization. -/
theorem greenPort_eq_phaseNormalizerDress_holomorphicGreenPort
    (N : ℕ) (s : ℂ) (state : CanonicalCompletedC3HilbertState) :
    greenPort N s state =
      radialGreenDress (cpPhaseNormalizer 3 s)
        (holomorphicGreenPort N s state) := by
  rw [greenPort_eq_radialGreenDress_undressedGreenPort]
  apply Prod.ext <;> ext n
  · change c3RadialGreenFactor s * state.1 (n : ℕ) =
      cpPhaseNormalizer 3 s * (natDirichletTerm s 3 * state.1 (n : ℕ))
    rw [← mul_assoc, cpPhaseNormalizer_mul_holomorphicC3Eigenvalue]
  · rfl

/-! ## Generic Green polarization -/

/-- The Green form of two holomorphic ports is the C3 eigenvalue collision
factor times the ordinary-source inner product.  The conjugation displayed
here is fixed by the repository convention that `inner` is conjugate-linear
in its first argument. -/
theorem greenForm_holomorphicGreenPort_eq_eigenvalueDiff_mul_inner
    (N : ℕ) (r s : ℂ)
    (direct reflected : CanonicalCompletedC3HilbertState) :
    greenForm (𝕜 := ℂ)
        (holomorphicGreenPort N r direct)
        (holomorphicGreenPort N s reflected) =
      (natDirichletTerm s 3 - (starRingEnd ℂ) (natDirichletTerm r 3)) *
        inner ℂ (undressedGreenPort N direct).1 (undressedGreenPort N reflected).1 := by
  have hdirect : (undressedGreenPort N direct).2 =
      (undressedGreenPort N direct).1 := rfl
  have hreflected : (undressedGreenPort N reflected).2 =
      (undressedGreenPort N reflected).1 := rfl
  simp only [holomorphicGreenPort, radialGreenDress, greenForm,
    inner_smul_left, inner_smul_right]
  rw [hdirect, hreflected]
  ring

/-! ## Camera-resolved holomorphic polarization -/

/-- The direct camera source is dressed by the centered spectral eigenvalue.
The source itself remains the already reconstructed direct source. -/
def cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  holomorphicGreenPort (3 * M) (operatorHeightParameter 0)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).wSource

/-- The reflected camera source is dressed by the holomorphic eigenvalue at
its independent spectral-height coordinate. -/
def cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ) (camera : ℕ) :
    FiniteC3GreenPortCarrier (3 * M) :=
  holomorphicGreenPort (3 * M) (operatorHeightParameter v)
    (cameraResolvedSeededClockIndependentReflectedSixSourceReconstruction
      M q hq0 hq1 S u v camera).reflectedZSource

/-- The camera-pair Green kernel with the spectral C3 eigenvalue retained in
the first Green leg. -/
def canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
      M q hq0 hq1 S u v directCamera)
    (cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
      M q hq0 hq1 S u v reflectedCamera)

/-- The ordinary-source inner product which survives the holomorphic C3
collision factor.  The direct port is fixed at reflected coordinate zero
using its established coordinate independence. -/
def canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) (v : ℂ) : ℂ :=
  inner ℂ
    (cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u 0 directCamera).1
    (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u v reflectedCamera).1

/-- Exact factorization of a camera-pair holomorphic kernel into the
eigenvalue collision and the central ordinary-source inner product. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_eq_eigenvalueDiff_mul_inner
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u v : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
      M q hq0 hq1 S u v directCamera reflectedCamera =
      (natDirichletTerm (operatorHeightParameter v) 3 -
        (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera v := by
  unfold canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
    cameraResolvedIndependentReflectedHolomorphicDirectGreenPort
    cameraResolvedIndependentReflectedHolomorphicReflectedGreenPort
  rw [greenForm_holomorphicGreenPort_eq_eigenvalueDiff_mul_inner]
  have hdirect :
      cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v directCamera =
      cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u 0 directCamera :=
    cameraResolvedIndependentReflectedUndressedDirectGreenPort_independent
      M q hq0 hq1 S u v u 0 directCamera
  change _ * inner ℂ
      (cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u v directCamera).1
      (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
        M q hq0 hq1 S u v reflectedCamera).1 =
    _ * inner ℂ
      (cameraResolvedIndependentReflectedUndressedDirectGreenPort
        M q hq0 hq1 S u 0 directCamera).1
      (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
        M q hq0 hq1 S u v reflectedCamera).1
  rw [hdirect]

/-! ## The central spectral collision -/

/-- The C3 first-leg eigenvalue along the holomorphic height coordinate. -/
def holomorphicC3EigenvalueAlongHeight (v : ℂ) : ℂ :=
  natDirichletTerm (operatorHeightParameter v) 3

/-- The exact complex derivative of the C3 eigenvalue along the height
coordinate at the central collision. -/
def holomorphicC3EigenvalueDerivativeAtZero : ℂ :=
  (-natLogDirichletTerm (1 / 2 : ℂ) 3) * Complex.I

theorem holomorphicC3EigenvalueAlongHeight_zero :
    holomorphicC3EigenvalueAlongHeight 0 = natDirichletTerm (1 / 2 : ℂ) 3 := by
  simp [holomorphicC3EigenvalueAlongHeight, operatorHeightParameter]

/-- The central C3 eigenvalue is real, so its involution fixes it. -/
theorem star_natDirichletTerm_half_three :
    (starRingEnd ℂ) (natDirichletTerm (1 / 2 : ℂ) 3) =
      natDirichletTerm (1 / 2 : ℂ) 3 := by
  rw [natDirichletTerm_half_eq_realRpow]
  simp

/-- The two eigenvalue legs collide at the central spectral parameter. -/
theorem holomorphicC3EigenvalueCollision_zero :
    natDirichletTerm (operatorHeightParameter 0) 3 -
        (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3) = 0 := by
  rw [show operatorHeightParameter 0 = (1 / 2 : ℂ) by
    norm_num [operatorHeightParameter]]
  rw [star_natDirichletTerm_half_three]
  ring

/-- The camera-pair holomorphic kernel has a collision zero at the center.
This is the eigenvalue collision, not the diagonal-port degeneracy proved for
the distinct undressed carrier. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
      M q hq0 hq1 S u 0 directCamera reflectedCamera = 0 := by
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_eq_eigenvalueDiff_mul_inner,
    holomorphicC3EigenvalueCollision_zero]
  simp

/-- The exact first derivative of the C3 eigenvalue is obtained by composing
the Dirichlet derivative with the affine spectral-height parameter. -/
theorem hasDerivAt_holomorphicC3EigenvalueAlongHeight_zero :
    HasDerivAt holomorphicC3EigenvalueAlongHeight
      holomorphicC3EigenvalueDerivativeAtZero 0 := by
  unfold holomorphicC3EigenvalueAlongHeight holomorphicC3EigenvalueDerivativeAtZero
  have hterm := hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
    3 (by norm_num : 3 ≠ 0) (operatorHeightParameter 0)
  have hcomp := hterm.comp 0 (hasDerivAt_operatorHeightParameter 0)
  change HasDerivAt
    ((fun s : ℂ => natDirichletTerm s 3) ∘ operatorHeightParameter)
    ((-natLogDirichletTerm (1 / 2 : ℂ) 3) * Complex.I) 0
  simpa [operatorHeightParameter] using hcomp

/-- The central C3 Dirichlet eigenvalue does not vanish. -/
theorem natDirichletTerm_half_three_ne_zero :
    natDirichletTerm (1 / 2 : ℂ) 3 ≠ 0 := by
  unfold natDirichletTerm dirichletTerm
  convert Complex.natCast_add_one_cpow_ne_zero 2 (-(1 / 2 : ℂ)) using 1
  norm_num

/-- The logarithmically weighted C3 Dirichlet eigenvalue at the center is
nonzero: both the positive real logarithm and the Dirichlet eigenvalue are
nonzero. -/
theorem natLogDirichletTerm_half_three_ne_zero :
    natLogDirichletTerm (1 / 2 : ℂ) 3 ≠ 0 := by
  unfold natLogDirichletTerm
  apply mul_ne_zero
  · exact_mod_cast (Nat.Prime.log_ne_zero (by norm_num : Nat.Prime 3))
  · exact natDirichletTerm_half_three_ne_zero

/-- The C3 collision scalar is nonzero. -/
theorem holomorphicC3Eigenvalue_deriv_zero_ne_zero :
    holomorphicC3EigenvalueDerivativeAtZero ≠ 0 := by
  unfold holomorphicC3EigenvalueDerivativeAtZero
  exact mul_ne_zero (neg_ne_zero.mpr natLogDirichletTerm_half_three_ne_zero)
    Complex.I_ne_zero

/-! ## Analyticity of the holomorphic camera kernel -/

/-- The C3 eigenvalue along the affine spectral-height parameter is analytic
at the collision center. -/
theorem holomorphicC3EigenvalueAlongHeight_analyticAt_zero :
    AnalyticAt ℂ holomorphicC3EigenvalueAlongHeight 0 := by
  unfold holomorphicC3EigenvalueAlongHeight natDirichletTerm dirichletTerm
  have hparameter : AnalyticAt ℂ (fun v => -operatorHeightParameter v) 0 :=
    operatorHeightParameter_analyticAt_zero.neg
  exact analyticAt_const.cpow hparameter
    (Complex.natCast_mem_slitPlane.mpr (by norm_num))

/-- A fixed first-coordinate inner product as a continuous complex-linear map
on a two-leg Green port. -/
def holomorphicGreenInnerFixedLeft {N : ℕ}
    (direct : FiniteC3GreenPortCarrier N) :
    FiniteC3GreenPortCarrier N →L[ℂ] ℂ :=
  (innerSL ℂ direct.1).comp
    (ContinuousLinearMap.fst ℂ
      (FiniteC3GreenBoundarySpace N) (FiniteC3GreenBoundarySpace N))

@[simp] theorem holomorphicGreenInnerFixedLeft_apply
    {N : ℕ} (direct reflected : FiniteC3GreenPortCarrier N) :
    holomorphicGreenInnerFixedLeft direct reflected = inner ℂ direct.1 reflected.1 := by
  simp [holomorphicGreenInnerFixedLeft, innerSL_apply_apply]

/-- The central ordinary-source inner product is analytic in the independent
reflected height coordinate. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    AnalyticAt ℂ
      (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
        M q hq0 hq1 S u directCamera reflectedCamera) 0 := by
  let direct : FiniteC3GreenPortCarrier (3 * M) :=
    cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u 0 directCamera
  let reflected : ℂ → FiniteC3GreenPortCarrier (3 * M) := fun v =>
    cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u v reflectedCamera
  rw [show canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
      M q hq0 hq1 S u directCamera reflectedCamera =
      fun v => holomorphicGreenInnerFixedLeft direct (reflected v) by
        funext v
        simp only [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner,
          holomorphicGreenInnerFixedLeft_apply, direct, reflected]]
  have hreflected : AnalyticAt ℂ reflected 0 := by
    simpa only [reflected] using
      cameraResolvedIndependentReflectedUndressedReflectedGreenPort_analyticAt_zero
        M q hq0 hq1 S u reflectedCamera
  have hmap : AnalyticAt ℂ
      (fun port : FiniteC3GreenPortCarrier (3 * M) =>
        holomorphicGreenInnerFixedLeft direct port) (reflected 0) :=
    (holomorphicGreenInnerFixedLeft direct).analyticAt (reflected 0)
  simpa only [reflected, Function.comp_def] using hmap.comp hreflected

/-- The spectral collision factor is analytic at the center. -/
theorem holomorphicC3EigenvalueCollision_analyticAt_zero :
    AnalyticAt ℂ
      (fun v => natDirichletTerm (operatorHeightParameter v) 3 -
        (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) 0 := by
  change AnalyticAt ℂ
    (holomorphicC3EigenvalueAlongHeight - fun _ : ℂ =>
      (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) 0
  exact holomorphicC3EigenvalueAlongHeight_analyticAt_zero.sub analyticAt_const

/-- Each camera-pair holomorphic Green kernel is analytic in the independent
reflected height coordinate. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_analyticAt_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    AnalyticAt ℂ
      (fun v => canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) 0 := by
  rw [show (fun v =>
      canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) =
      fun v =>
        (natDirichletTerm (operatorHeightParameter v) 3 -
          (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera v by
        funext v
        exact canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_eq_eigenvalueDiff_mul_inner
          M q hq0 hq1 S u v directCamera reflectedCamera]
  exact holomorphicC3EigenvalueCollision_analyticAt_zero.mul
    (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner_analyticAt_zero
      M q hq0 hq1 S u directCamera reflectedCamera)

/-! ## First holomorphic Green jet -/

/-- The collision factor has derivative exactly equal to the nonzero C3
eigenvalue derivative; the second summand is constant in the height variable. -/
theorem hasDerivAt_holomorphicC3EigenvalueCollision_zero :
    HasDerivAt
      (fun v => natDirichletTerm (operatorHeightParameter v) 3 -
        (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3))
      holomorphicC3EigenvalueDerivativeAtZero 0 := by
  change HasDerivAt
    (holomorphicC3EigenvalueAlongHeight - fun _ : ℂ =>
      (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3))
    holomorphicC3EigenvalueDerivativeAtZero 0
  simpa using
    hasDerivAt_holomorphicC3EigenvalueAlongHeight_zero.sub (hasDerivAt_const (x := 0)
      (c := (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)))

/-- At the collision zero, differentiating the holomorphic Green kernel only
differentiates its eigenvalue factor.  No derivative of the reconstructed
reflected source is required in this formula. -/
theorem deriv_canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_zero
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    deriv (fun v =>
      canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) 0 =
      holomorphicC3EigenvalueDerivativeAtZero *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera 0 := by
  rw [show (fun v =>
      canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
        M q hq0 hq1 S u v directCamera reflectedCamera) =
      fun v =>
        (natDirichletTerm (operatorHeightParameter v) 3 -
          (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera v by
        funext v
        exact canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_eq_eigenvalueDiff_mul_inner
          M q hq0 hq1 S u v directCamera reflectedCamera]
  have hinner :=
    (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner_analyticAt_zero
      M q hq0 hq1 S u directCamera reflectedCamera).differentiableAt.hasDerivAt
  have hproduct := hinner.mul hasDerivAt_holomorphicC3EigenvalueCollision_zero
  have hderiv :
      deriv
        (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera *
          fun v => natDirichletTerm (operatorHeightParameter v) 3 -
            (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) 0 =
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera 0 *
          holomorphicC3EigenvalueDerivativeAtZero := by
    simpa [holomorphicC3EigenvalueCollision_zero] using hproduct.deriv
  calc
    deriv (fun v =>
        (natDirichletTerm (operatorHeightParameter v) 3 -
          (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera v) 0 =
      deriv
        (canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera *
          fun v => natDirichletTerm (operatorHeightParameter v) 3 -
            (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) 0 := by
        congr 1
        funext v
        change
          (natDirichletTerm (operatorHeightParameter v) 3 -
              (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3)) *
            canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
              M q hq0 hq1 S u directCamera reflectedCamera v =
            canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
              M q hq0 hq1 S u directCamera reflectedCamera v *
              (natDirichletTerm (operatorHeightParameter v) 3 -
                (starRingEnd ℂ) (natDirichletTerm (operatorHeightParameter 0) 3))
        ring
    _ =
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera 0 *
          holomorphicC3EigenvalueDerivativeAtZero := hderiv
    _ = holomorphicC3EigenvalueDerivativeAtZero *
          canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
            M q hq0 hq1 S u directCamera reflectedCamera 0 := by ring

/-- Literal-order complex Taylor coefficients of the holomorphic camera-pair
kernel.  This definition is intentionally confined to the holomorphic carrier;
it is not a jet construction for the physical normalized port. -/
def canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera order : ℕ) : ℂ :=
  iteratedDeriv order
    (fun v => canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel
      M q hq0 hq1 S u v directCamera reflectedCamera) 0 / order.factorial

/-- Since `1! = 1`, the literal first holomorphic jet is exactly the C3
eigenvalue derivative times the central reconstructed ordinary-source Gram
scalar. -/
theorem canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient_one_eq_scaledCentralInner
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
      M q hq0 hq1 S u directCamera reflectedCamera 1 =
      holomorphicC3EigenvalueDerivativeAtZero *
        canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
          M q hq0 hq1 S u directCamera reflectedCamera 0 := by
  simpa [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient,
    iteratedDeriv_one] using
    deriv_canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenKernel_zero
      M q hq0 hq1 S u directCamera reflectedCamera

end

end CarrySelfAdjointOperator
