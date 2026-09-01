import CarrySelfAdjointOperator.CompletedC3CausalChiralKernelObstruction
import Mathlib.Tactic

/-!
# Strict positivity of the coisometric ambient C3 carrier

The fixed twelve-dimensional Wronskian readout cannot contain the full
completed causal family.  The canonical Naimark carrier has no such loss:
its port is complex-linear, its adjoint is an exact left inverse, and it
preserves the polarized Hilbert product.

Dedekind independence of the completed real-exponent gradients therefore
passes first to the symplectic camera states and then, without loss, to the
ambient Naimark responses.  Their Gram matrix is positive definite for every
finite family of distinct positive real exponents.  In particular, the
explicit thirteen-state obstruction family has a strictly positive ambient
Gram even though it cannot factor through the fixed Wronskian trace carrier.

This result identifies the correct positive carrier.  It does not identify
its Gram kernel with the completed-native `dslope` moment kernel.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

theorem completedC3SymplecticCameraComplexState_realExponent_linearIndependent
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℂ
      (fun i => canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma i : ℂ) (by simpa using hpos i))) := by
  let leg : ι → CameraHilbert := fun i =>
    completedC3LegCameraState
      (canonicalCompletedC3DirichletGradientState
        (sigma i : ℂ) (by simpa using hpos i))
  have hgradientComplex :=
    canonicalCompletedC3DirichletGradientState_realExponent_linearIndependent_complex
      sigma hpos hinjective
  have hgradientReal : LinearIndependent ℝ
      (fun i => canonicalCompletedC3DirichletGradientState
        (sigma i : ℂ) (by simpa using hpos i)) :=
    hgradientComplex.restrict_scalars' ℝ
  have hleg := hgradientReal.map'
    completedC3GlobalLegCameraIsometry.toLinearMap
    (LinearMap.ker_eq_bot.mpr completedC3GlobalLegCameraIsometry.injective)
  change LinearIndependent ℝ leg at hleg
  let reAddHom : CarryGammaComplexCamera →+ CameraHilbert :=
    { toFun := RealHilbertComplexification.re
      map_zero' := RealHilbertComplexification.re_zero
      map_add' := RealHilbertComplexification.re_add }
  let imAddHom : CarryGammaComplexCamera →+ CameraHilbert :=
    { toFun := RealHilbertComplexification.im
      map_zero' := RealHilbertComplexification.im_zero
      map_add' := RealHilbertComplexification.im_add }
  let reMap : CarryGammaComplexCamera →ₗ[ℝ] CameraHilbert :=
    (reAddHom.toRealLinearMap (by
      change Continuous (fun u : CarryGammaComplexCamera => u.fst)
      exact (WithLp.fstL 2 ℝ CameraHilbert CameraHilbert).continuous)).toLinearMap
  let imMap : CarryGammaComplexCamera →ₗ[ℝ] CameraHilbert :=
    (imAddHom.toRealLinearMap (by
      change Continuous (fun u : CarryGammaComplexCamera => u.snd)
      exact (WithLp.sndL 2 ℝ CameraHilbert CameraHilbert).continuous)).toLinearMap
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  have hre := congrArg reMap hsum
  have him := congrArg imMap hsum
  simp only [map_sum, map_zero] at hre him
  have hReApply (j : ι) :
      reMap (coeff j • canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma j : ℂ) (by simpa using hpos j))) =
        (-((coeff j).re) *
            completedC3RadialRealCoefficient (sigma j : ℂ) -
          (coeff j).im) • leg j := by
    change RealHilbertComplexification.re
      (coeff j • canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma j : ℂ) (by simpa using hpos j))) = _
    rw [RealHilbertComplexification.re_smul]
    simp [leg, canonicalCompletedC3GammaCameraView,
      completedC3SymplecticCameraState,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      smul_smul, sub_smul]
  have hImApply (j : ι) :
      imMap (coeff j • canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma j : ℂ) (by simpa using hpos j))) =
        (-((coeff j).im) *
            completedC3RadialRealCoefficient (sigma j : ℂ) +
          (coeff j).re) • leg j := by
    change RealHilbertComplexification.im
      (coeff j • canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma j : ℂ) (by simpa using hpos j))) = _
    rw [RealHilbertComplexification.im_smul]
    simp [leg, canonicalCompletedC3GammaCameraView,
      completedC3SymplecticCameraState,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      smul_smul, add_smul]
  have hre' :
      ∑ j, (-((coeff j).re) *
            completedC3RadialRealCoefficient (sigma j : ℂ) -
          (coeff j).im) • leg j = 0 := by
    simpa only [hReApply] using hre
  have him' :
      ∑ j, (-((coeff j).im) *
            completedC3RadialRealCoefficient (sigma j : ℂ) +
          (coeff j).re) • leg j = 0 := by
    simpa only [hImApply] using him
  have hreCoeff := (Fintype.linearIndependent_iff.mp hleg)
    (fun j => -((coeff j).re) *
        completedC3RadialRealCoefficient (sigma j : ℂ) - (coeff j).im)
    hre' i
  have himCoeff := (Fintype.linearIndependent_iff.mp hleg)
    (fun j => -((coeff j).im) *
        completedC3RadialRealCoefficient (sigma j : ℂ) + (coeff j).re)
    him' i
  let r := completedC3RadialRealCoefficient (sigma i : ℂ)
  have hreEq : -(coeff i).re * r - (coeff i).im = 0 := by
    simpa [r] using hreCoeff
  have himEq : -(coeff i).im * r + (coeff i).re = 0 := by
    simpa [r] using himCoeff
  have hreFromIm : (coeff i).re = (coeff i).im * r := by
    linarith
  rw [hreFromIm] at hreEq
  have himFactor : (coeff i).im * (r ^ 2 + 1) = 0 := by
    calc
      (coeff i).im * (r ^ 2 + 1) =
          -(-((coeff i).im * r) * r - (coeff i).im) := by ring
      _ = 0 := by rw [hreEq]; simp
  have hr : r ^ 2 + 1 ≠ 0 := by positivity
  have himZero : (coeff i).im = 0 :=
    (mul_eq_zero.mp himFactor).resolve_right hr
  have hreZero : (coeff i).re = 0 := by
    rw [hreFromIm, himZero, zero_mul]
  apply Complex.ext <;> simp [hreZero, himZero]

/-- Coordinatewise Naimark embedding in the canonical complex Hilbert
presentations of the camera and ambient carriers. -/
def canonicalCompletedC3ComplexNaimarkPort :
    CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexNaimark where
  toFun u := canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u)
  map_add' u v := by
    change realifiedNaimarkPort (u + v) =
      realifiedNaimarkPort u + realifiedNaimarkPort v
    exact map_add realifiedNaimarkPort u v
  map_smul' z u := by
    apply RealHilbertComplexification.ext
    · change (realifiedNaimarkPort (z • u)).fst =
        z.re • (realifiedNaimarkPort u).fst -
          z.im • (realifiedNaimarkPort u).snd
      rw [realifiedNaimarkPort_fst, realifiedNaimarkPort_fst,
        realifiedNaimarkPort_snd]
      change naimarkIsometry (RealHilbertComplexification.re (z • u)) =
        z.re • naimarkIsometry (RealHilbertComplexification.re u) -
          z.im • naimarkIsometry (RealHilbertComplexification.im u)
      rw [RealHilbertComplexification.re_smul,
        map_sub, map_smul, map_smul]
    · change (realifiedNaimarkPort (z • u)).snd =
        z.im • (realifiedNaimarkPort u).fst +
          z.re • (realifiedNaimarkPort u).snd
      rw [realifiedNaimarkPort_snd, realifiedNaimarkPort_fst,
        realifiedNaimarkPort_snd]
      change naimarkIsometry (RealHilbertComplexification.im (z • u)) =
        z.im • naimarkIsometry (RealHilbertComplexification.re u) +
          z.re • naimarkIsometry (RealHilbertComplexification.im u)
      rw [RealHilbertComplexification.im_smul,
        map_add, map_smul, map_smul]

@[simp] theorem canonicalCompletedC3ComplexNaimarkPort_apply
    (u : CarryGammaComplexCamera) :
    canonicalCompletedC3ComplexNaimarkPort u =
      canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u) :=
  rfl

/-- The complex Naimark embedding is injective because the underlying
realified Naimark port already has its coisometric left inverse. -/
theorem canonicalCompletedC3ComplexNaimarkPort_injective :
    Function.Injective canonicalCompletedC3ComplexNaimarkPort := by
  intro u v huv
  exact realifiedNaimarkPort_injective huv

/-- The complex port preserves the full polarized Hilbert product.  This is
the complex form of the coisometric identity `U* U = I`. -/
theorem inner_canonicalCompletedC3ComplexNaimarkPort
    (u v : CarryGammaComplexCamera) :
    inner ℂ (canonicalCompletedC3ComplexNaimarkPort u)
        (canonicalCompletedC3ComplexNaimarkPort v) =
      inner ℂ u v := by
  change inner ℂ
      (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort u))
      (canonicalCompletedC3GammaNaimarkView (realifiedNaimarkPort v)) = _
  rw [inner_complex_gammaNaimarkView_port_eq_adjoint]
  change inner ℂ
      (canonicalCompletedC3GammaCameraView u)
      (canonicalCompletedC3GammaCameraView
        ((realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) v)) = _
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- Distinct positive real exponents remain independent after the exact
Naimark embedding. -/
theorem completedC3SymplecticGammaNaimarkState_realExponent_linearIndependent
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℂ
      (fun i => canonicalCompletedC3GammaNaimarkView
        (completedC3SymplecticNaimarkState
          (sigma i : ℂ) (by simpa using hpos i))) := by
  have hcamera :=
    completedC3SymplecticCameraComplexState_realExponent_linearIndependent
      sigma hpos hinjective
  have hmap := hcamera.map'
    canonicalCompletedC3ComplexNaimarkPort
    (LinearMap.ker_eq_bot.mpr
      canonicalCompletedC3ComplexNaimarkPort_injective)
  change LinearIndependent ℂ
    (canonicalCompletedC3ComplexNaimarkPort ∘ fun i =>
      canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (sigma i : ℂ) (by simpa using hpos i)))
  exact hmap

/-- Centered-height point whose operator parameter is the prescribed real
exponent. -/
def canonicalCompletedC3CenteredRealExponentPoint (sigma : ℝ) : ℂ :=
  Complex.I * ((((1 : ℝ) / 2) - sigma : ℝ) : ℂ)

@[simp] theorem operatorHeightParameter_canonicalCompletedC3CenteredRealExponentPoint
    (sigma : ℝ) :
    operatorHeightParameter
        (canonicalCompletedC3CenteredRealExponentPoint sigma) =
      (sigma : ℂ) := by
  simp only [operatorHeightParameter,
    canonicalCompletedC3CenteredRealExponentPoint]
  rw [← mul_assoc, Complex.I_mul_I]
  push_cast
  ring

/-- The actual ambient response states at distinct positive real exponents
are complex-linearly independent. -/
theorem canonicalCompletedC3AmbientResponseState_realExponent_linearIndependent
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    LinearIndependent ℂ
      (fun i => canonicalCompletedC3AmbientResponseState
        (canonicalCompletedC3CenteredRealExponentPoint (sigma i))
        (by simpa using hpos i)) := by
  simpa [canonicalCompletedC3AmbientResponseState,
    completedC3SymplecticNaimarkComplexState] using
    completedC3SymplecticGammaNaimarkState_realExponent_linearIndependent
      sigma hpos hinjective

/-- Coisometric Naimark transport upgrades the ambient response kernel from
positive semidefinite to positive definite on every finite family of
distinct positive real exponents. -/
theorem canonicalCompletedC3AmbientResponseKernel_realExponent_posDef
    {ι : Type*} [Fintype ι]
    (sigma : ι → ℝ) (hpos : ∀ i, 0 < sigma i)
    (hinjective : Function.Injective sigma) :
    (Matrix.of fun i j =>
      canonicalCompletedC3AmbientResponseKernel
        (canonicalCompletedC3CenteredRealExponentPoint (sigma i))
        (canonicalCompletedC3CenteredRealExponentPoint (sigma j))
        (by simpa using hpos i) (by simpa using hpos j)).PosDef := by
  change (Matrix.gram ℂ (fun i => canonicalCompletedC3AmbientResponseState
    (canonicalCompletedC3CenteredRealExponentPoint (sigma i))
    (by simpa using hpos i))).PosDef
  exact Matrix.posDef_gram_of_linearIndependent
    (canonicalCompletedC3AmbientResponseState_realExponent_linearIndependent
      sigma hpos hinjective)

/-- In particular, the explicit thirteen-state family which obstructs every
fixed twelve-dimensional Wronskian readout has a strictly positive ambient
Naimark Gram. -/
theorem canonicalCausalChiralObstruction_ambientResponseKernel_posDef :
    (Matrix.of fun i j : Fin 13 =>
      canonicalCompletedC3AmbientResponseKernel
        (canonicalCausalChiralObstructionPoint i)
        (canonicalCausalChiralObstructionPoint j)
        (operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip i).1
        (operatorHeightParameter_canonicalCausalChiralObstructionPoint_mem_strip j).1).PosDef := by
  simpa only [canonicalCausalChiralObstructionPoint,
    canonicalCompletedC3CenteredRealExponentPoint] using
    canonicalCompletedC3AmbientResponseKernel_realExponent_posDef
      canonicalCausalChiralObstructionExponent
      canonicalCausalChiralObstructionExponent_pos
      canonicalCausalChiralObstructionExponent_injective

end

end CarrySelfAdjointOperator
