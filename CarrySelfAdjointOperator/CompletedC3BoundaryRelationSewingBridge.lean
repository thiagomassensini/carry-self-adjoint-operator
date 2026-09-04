import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import CarrySelfAdjointOperator.CompletedC3FourTraceSymplecticBridge
import Mathlib.Tactic

/-!
# Completed C3 boundary-relation sewing bridge

This module rewrites the remaining completed C3 Gamma--Wronskian sewing gate
in the literal Green-form language already used by the source-extended carry
boundary relation.

There are two independently constructed boundary states:

* the canonical six-camera Gamma state, whose oriented boundary coordinates
  are `(source, Cauchy trace)`;
* the completed scalar TFVD trace, whose oriented coordinates are
  `(boundary companion, characteristic) = (-F', F)`.

The first Green form is exactly the existing polarized Gamma boundary readout.
The second Green form is exactly the completed scalar Wronskian with the
argument order used by the sewing gate.  Therefore the raw
Gamma--Wronskian defect is literally the difference of two boundary Green
forms.

The two real quadratures of the Gamma boundary state are also exhibited as
literal Weyl boundary values of concrete vectors in `carrySourceRelation`.
Thus the boundary carrier introduced here is not a new ad hoc relation: it is
the canonical complexification of the already formalized source-extended
self-adjoint logarithmic boundary relation.

No equality of the two boundary states is asserted here.  The purpose of the
module is to expose the remaining task as a boundary-relation identification,
so that a future provenance-preserving C3 boundary map can target the exact
object required by the already formalized source relation.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Complex boundary carrier used by the canonical C3 Gamma source relation.
The first coordinate is the six-camera source and the second is its compressed
Cauchy trace. -/
abbrev CanonicalCompletedC3GammaBoundaryCarrier :=
  CarryGammaComplexCamera × CarryGammaComplexCamera

/-- Oriented Weyl-boundary state of the canonical completed C3 Gamma source.
The order `(source, Cauchy)` is chosen so that the generic Green form has the
same orientation as `canonicalCompletedC3PolarizedGammaBoundaryReadout`. -/
def canonicalCompletedC3GammaBoundaryState
    (z : ℂ) (hz : z.im ≠ 0) : CanonicalCompletedC3GammaBoundaryCarrier :=
  (canonicalCompletedC3SixCameraSource z,
    carryGammaComplexCauchyReadout z hz
      (canonicalCompletedC3SixCameraSource z))

@[simp] theorem canonicalCompletedC3GammaBoundaryState_fst
    (z : ℂ) (hz : z.im ≠ 0) :
    (canonicalCompletedC3GammaBoundaryState z hz).1 =
      canonicalCompletedC3SixCameraSource z :=
  rfl

@[simp] theorem canonicalCompletedC3GammaBoundaryState_snd
    (z : ℂ) (hz : z.im ≠ 0) :
    (canonicalCompletedC3GammaBoundaryState z hz).2 =
      carryGammaComplexCauchyReadout z hz
        (canonicalCompletedC3SixCameraSource z) :=
  rfl

/-- First real quadrature of the canonical C3 Gamma defect state, viewed as a
literal element of the concrete source-extended carry relation. -/
def canonicalCompletedC3GammaSourceRelationFst
    (z : ℂ) (hz : z.im ≠ 0) : carrySourceRelation :=
  carrySourceRelationElement
    (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z)).1
    (canonicalCompletedC3SixCameraSource z).fst

/-- Second real quadrature of the same Gamma defect state in the source
relation. -/
def canonicalCompletedC3GammaSourceRelationSnd
    (z : ℂ) (hz : z.im ≠ 0) : carrySourceRelation :=
  carrySourceRelationElement
    (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z)).2
    (canonicalCompletedC3SixCameraSource z).snd

/-- The Weyl boundary chart of the first relation quadrature is exactly the
first quadrature of `(Cauchy trace, source)`. -/
theorem canonicalCompletedC3GammaSourceRelationFst_weylBoundaryMap
    (z : ℂ) (hz : z.im ≠ 0) :
    carryWeylBoundaryMap
        (canonicalCompletedC3GammaSourceRelationFst z hz) =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.fst,
        (canonicalCompletedC3GammaBoundaryState z hz).1.fst) := by
  rw [canonicalCompletedC3GammaSourceRelationFst,
    carryWeylBoundaryMap_element]
  apply Prod.ext
  · change
      naimarkAdjoint
          ((carryGammaIntoDomain z hz
            (canonicalCompletedC3SixCameraSource z)).1 : NaimarkSpace) =
        (carryGammaComplexCauchyReadout z hz
          (canonicalCompletedC3SixCameraSource z)).fst
    rw [carryGammaIntoDomain_fst_coe]
    have h := congrArg WithLp.fst
      (carryDefectGammaZero_apply z hz
        (canonicalCompletedC3SixCameraSource z))
    simpa [carryDefectGammaZero, carryGammaComplexCauchyReadout,
      ContinuousLinearMap.comp_apply] using h
  · rfl

/-- The Weyl boundary chart of the second relation quadrature is exactly the
second quadrature of `(Cauchy trace, source)`. -/
theorem canonicalCompletedC3GammaSourceRelationSnd_weylBoundaryMap
    (z : ℂ) (hz : z.im ≠ 0) :
    carryWeylBoundaryMap
        (canonicalCompletedC3GammaSourceRelationSnd z hz) =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.snd,
        (canonicalCompletedC3GammaBoundaryState z hz).1.snd) := by
  rw [canonicalCompletedC3GammaSourceRelationSnd,
    carryWeylBoundaryMap_element]
  apply Prod.ext
  · change
      naimarkAdjoint
          ((carryGammaIntoDomain z hz
            (canonicalCompletedC3SixCameraSource z)).2 : NaimarkSpace) =
        (carryGammaComplexCauchyReadout z hz
          (canonicalCompletedC3SixCameraSource z)).snd
    rw [carryGammaIntoDomain_snd_coe]
    have h := congrArg WithLp.snd
      (carryDefectGammaZero_apply z hz
        (canonicalCompletedC3SixCameraSource z))
    simpa [carryDefectGammaZero, carryGammaComplexCauchyReadout,
      ContinuousLinearMap.comp_apply] using h
  · rfl

/-- The positive Gamma boundary numerator is literally the Green form of the
canonical six-camera boundary states.  This places the existing Gamma sewing
object directly in the language of `Boundary.SourceRelation`. -/
theorem canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_boundaryGreenForm
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) := by
  rfl

/-- Scalar completed TFVD boundary pair in the same orientation used by the
existing scalar symplectic carrier: `(Psi,F)=(-F',F)`. -/
def canonicalCompletedC3ScalarBoundaryPair (z : ℂ) : ℂ × ℂ :=
  (completedNativeOperatorBoundaryCompanion z,
    completedNativeOperatorCharacteristic z)

@[simp] theorem canonicalCompletedC3ScalarBoundaryPair_fst (z : ℂ) :
    (canonicalCompletedC3ScalarBoundaryPair z).1 =
      completedNativeOperatorBoundaryCompanion z :=
  rfl

@[simp] theorem canonicalCompletedC3ScalarBoundaryPair_snd (z : ℂ) :
    (canonicalCompletedC3ScalarBoundaryPair z).2 =
      completedNativeOperatorCharacteristic z :=
  rfl

/-- The completed scalar Wronskian, with the argument order used by the Gamma
sewing gate, is exactly the scalar boundary Green form. -/
theorem completedC3Wronskian_eq_scalarBoundaryGreenForm
    (z w : ℂ) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w) := by
  simp [completedGreenWronskian, greenForm,
    canonicalCompletedC3ScalarBoundaryPair]

/-- The raw sewing defect is exactly the difference between two Green forms:
the six-camera Gamma boundary form and the completed scalar TFVD boundary
form.  No source equation or positivity premise is hidden in this rewrite. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3GammaBoundaryState z hz)
          (canonicalCompletedC3GammaBoundaryState w hw) -
        greenForm (𝕜 := ℂ)
          (canonicalCompletedC3ScalarBoundaryPair z)
          (canonicalCompletedC3ScalarBoundaryPair w) := by
  unfold canonicalCompletedC3RawGammaWronskianDefect
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_boundaryGreenForm,
    completedC3Wronskian_eq_scalarBoundaryGreenForm]

/-- Boundary-relation spelling of the completed C3 sewing gate. -/
def CanonicalCompletedC3BoundaryGreenSewing : Prop :=
  ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3ScalarBoundaryPair z)
        (canonicalCompletedC3ScalarBoundaryPair w)

/-- The new boundary-relation spelling is literally equivalent to vanishing
of the already existing raw Gamma--Wronskian defect at every off-axis pair. -/
theorem canonicalCompletedC3BoundaryGreenSewing_iff_rawDefect_zero :
    CanonicalCompletedC3BoundaryGreenSewing ↔
      ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
        canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 := by
  constructor
  · intro h z w hz hw
    rw [canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub]
    exact sub_eq_zero.mpr (h z w hz hw)
  · intro h z w hz hw
    have hzero := h z w hz hw
    rw [canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub]
      at hzero
    exact sub_eq_zero.mp hzero

/-- A boundary Green sewing immediately supplies the pointwise raw Wronskian
identity required by the existing normalized Gamma--`dslope` theorem. -/
theorem CanonicalCompletedC3BoundaryGreenSewing.rawWronskian
    (h : CanonicalCompletedC3BoundaryGreenSewing)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_boundaryGreenForm,
    completedC3Wronskian_eq_scalarBoundaryGreenForm]
  exact h z w hz hw

/-- Consequently, away from characteristic zeros and spectral collision, the
boundary-relation sewing closes the already normalized positive Gamma kernel
against the completed native `dslope`. -/
theorem CanonicalCompletedC3BoundaryGreenSewing.normalizedGammaKernel_eq_dslope
    (h : CanonicalCompletedC3BoundaryGreenSewing)
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      canonicalCompletedNativePolarizedDslopeKernel z w := by
  apply
    (canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
      M z w hz hw hzStrip hwStrip hzF hwF hsep).2
  exact h.rawWronskian z w hz hw

end

end CarrySelfAdjointOperator
