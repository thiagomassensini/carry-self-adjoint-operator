import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import CarrySelfAdjointOperator.CanonicalEnrichedC3Port
import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import Mathlib.Tactic

/-!
# Faithful six-camera source for the canonical C3 port

The complete cutoff-one C3 port has two legs, each with three complex cells.
This file places those six complex coordinates in the literal native cameras
`2, ..., 7`: the first realified channel stores every real part and the
second stores every imaginary part.  The intrinsic camera embedding then
places both finitely supported channels in the all-bases camera Hilbert
completion.

The packing is proved injective.  Consequently the already-formalized
nonvanishing of the enriched C3 port supplies the nonzero source needed by
the gamma field without using a zeta zero, target height, or scalar readout.
This is a provenance-preserving source construction; compatibility of its
Cauchy skew with the completed scalar Wronskian remains the explicit
scalarization equation.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Camera labels `2,3,4` assigned to the first C3 leg. -/
def firstC3CameraIndex (i : Fin 3) : CameraIndex :=
  ⟨i.val + 2, by omega⟩

/-- Camera labels `5,6,7` assigned to the second C3 leg. -/
def secondC3CameraIndex (i : Fin 3) : CameraIndex :=
  ⟨i.val + 5, by omega⟩

/-- Finitely supported six-camera channel containing all real parts of a C3
port. -/
def canonicalC3RealCameraFinsupp
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    CameraFinsupp :=
  (∑ i : Fin 3,
      Finsupp.single (firstC3CameraIndex i) (x.1 i).re) +
    ∑ i : Fin 3,
      Finsupp.single (secondC3CameraIndex i) (x.2 i).re

/-- Finitely supported six-camera channel containing all imaginary parts of
the same C3 port. -/
def canonicalC3ImagCameraFinsupp
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    CameraFinsupp :=
  (∑ i : Fin 3,
      Finsupp.single (firstC3CameraIndex i) (x.1 i).im) +
    ∑ i : Fin 3,
      Finsupp.single (secondC3CameraIndex i) (x.2 i).im

@[simp] theorem canonicalC3RealCameraFinsupp_first
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3)
    (j : Fin 3) :
    canonicalC3RealCameraFinsupp x (firstC3CameraIndex j) =
      (x.1 j).re := by
  fin_cases j <;>
    simp [canonicalC3RealCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem canonicalC3RealCameraFinsupp_second
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3)
    (j : Fin 3) :
    canonicalC3RealCameraFinsupp x (secondC3CameraIndex j) =
      (x.2 j).re := by
  fin_cases j <;>
    simp [canonicalC3RealCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem canonicalC3ImagCameraFinsupp_first
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3)
    (j : Fin 3) :
    canonicalC3ImagCameraFinsupp x (firstC3CameraIndex j) =
      (x.1 j).im := by
  fin_cases j <;>
    simp [canonicalC3ImagCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem canonicalC3ImagCameraFinsupp_second
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3)
    (j : Fin 3) :
    canonicalC3ImagCameraFinsupp x (secondC3CameraIndex j) =
      (x.2 j).im := by
  fin_cases j <;>
    simp [canonicalC3ImagCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

/-- All twelve real coordinates are retained by the six-camera packing. -/
theorem canonicalC3CameraFinsuppPair_injective :
    Function.Injective
      (fun x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3 ↦
        (canonicalC3RealCameraFinsupp x,
          canonicalC3ImagCameraFinsupp x)) := by
  intro x y hxy
  have hreal : canonicalC3RealCameraFinsupp x =
      canonicalC3RealCameraFinsupp y := congrArg Prod.fst hxy
  have himag : canonicalC3ImagCameraFinsupp x =
      canonicalC3ImagCameraFinsupp y := congrArg Prod.snd hxy
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext i
    apply Complex.ext
    · have h := congrArg
        (fun u : CameraFinsupp ↦ u (firstC3CameraIndex i)) hreal
      simpa using h
    · have h := congrArg
        (fun u : CameraFinsupp ↦ u (firstC3CameraIndex i)) himag
      simpa using h
  · apply WithLp.ofLp_injective 2
    funext i
    apply Complex.ext
    · have h := congrArg
        (fun u : CameraFinsupp ↦ u (secondC3CameraIndex i)) hreal
      simpa using h
    · have h := congrArg
        (fun u : CameraFinsupp ↦ u (secondC3CameraIndex i)) himag
      simpa using h

/-- Faithful realified all-bases camera source carried by a complete C3 port. -/
def canonicalC3SixCameraSourceMap
    (x : NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :
    RealifiedCameraComplexification :=
  WithLp.toLp 2
    (cameraEmbedding (canonicalC3RealCameraFinsupp x),
      cameraEmbedding (canonicalC3ImagCameraFinsupp x))

@[simp] theorem canonicalC3SixCameraSourceMap_zero :
    canonicalC3SixCameraSourceMap 0 = 0 := by
  simp [canonicalC3SixCameraSourceMap, canonicalC3RealCameraFinsupp,
    canonicalC3ImagCameraFinsupp]

/-- Completion and realification do not collapse any C3 port. -/
theorem canonicalC3SixCameraSourceMap_injective :
    Function.Injective canonicalC3SixCameraSourceMap := by
  intro x y hxy
  have hpair := congrArg
    (WithLp.ofLp : RealifiedCameraComplexification →
      CameraHilbert × CameraHilbert) hxy
  apply canonicalC3CameraFinsuppPair_injective
  apply Prod.ext
  · exact cameraEmbedding.injective (congrArg Prod.fst hpair)
  · exact cameraEmbedding.injective (congrArg Prod.snd hpair)

/-- Concrete source obtained from the actual completed-operator C3 state. -/
def canonicalCompletedC3SixCameraSource
    (z : ℂ) : RealifiedCameraComplexification :=
  canonicalC3SixCameraSourceMap (canonicalCompletedOperatorC3State z)

/-- The concrete six-camera source is nonzero throughout the operator image
of the open critical strip. -/
theorem canonicalCompletedC3SixCameraSource_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3SixCameraSource z ≠ 0 := by
  intro hzero
  apply canonicalEnrichedC3SourcePort_ne_zero hs
  apply canonicalC3SixCameraSourceMap_injective
  simpa [canonicalCompletedC3SixCameraSource,
    canonicalCompletedOperatorC3State] using hzero

/-- With the faithful six-camera source, the exact Cauchy scalarization alone
closes the zero-confinement implication; source nonvanishing is discharged
internally from the enriched C3 theorem. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalC3SixCameraScalarization
    (hscalar :
      HasCanonicalCompletedNativeGammaCauchyScalarization
        canonicalCompletedC3SixCameraSource)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    s.re = (1 : ℝ) / 2 := by
  apply riemannZeta_zero_re_eq_half_of_gammaCauchyScalarization
    canonicalCompletedC3SixCameraSource hscalar hs hzero
  intro _hz
  apply canonicalCompletedC3SixCameraSource_ne_zero
  simpa using hs

end

end CarrySelfAdjointOperator
