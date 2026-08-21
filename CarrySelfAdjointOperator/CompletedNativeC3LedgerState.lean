import CarrySelfAdjointOperator.GreenDirectSumState
import CarrySelfAdjointOperator.CompletedProductJet
import CarrySelfAdjointOperator.CanonicalEnrichedC3Port

/-!
# Concrete completed native/C3 provenance ledger

The abstract product state is specialized here to the actual xi completion
factor, the actual native scalar, and the canonical enriched C3 port.  The
state assigned to the archimedean factor remains an arbitrary Hilbert state:
the theorem below does not pretend that its Green realization has already
been constructed.

The concrete conclusion is nevertheless unconditional.  Throughout the open
strip the C3 coordinate

`nativeXiCompletionFactor z • canonicalCompletedOperatorC3State z`

is nonzero.  Hence a zeta zero annihilates the completed scalar
characteristic while the provenance-preserving product ledger remains
nonzero.  This is the state-level form of "the scalar readout vanishes but the
carry defect survives".
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Product-completion ledger with the canonical enriched C3 state in its
native-scalar coordinate.  No zero data enter this definition. -/
def completedNativeC3ProductLedgerState
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (z : ℂ) :
    BinaryHilbertSum Hxi
      (NativeCarryC3Crosswalk.FiniteC3GreenPortCarrier 3) :=
  weightedProductGreenState
    nativeXiCompletionFactor nativeHeightScalar
    xiState canonicalCompletedOperatorC3State z

/-- The native scalar in centered-height coordinates is exactly zeta on the
open strip. -/
theorem nativeHeightScalar_centeredHeightParameter_eq_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeHeightScalar (centeredHeightParameter s) = riemannZeta s := by
  unfold nativeHeightScalar
  rw [operatorHeightParameter_centeredHeightParameter,
    nativeScalar_eq_riemannZeta hs]

/-- The archimedean coordinate is weighted by the actual native scalar. -/
@[simp] theorem completedNativeC3ProductLedgerState_fst
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (z : ℂ) :
    (WithLp.ofLp (completedNativeC3ProductLedgerState xiState z)).1 =
      nativeHeightScalar z • xiState z :=
  rfl

/-- The C3 coordinate of the completed ledger is exactly the xi-weighted
canonical enriched port. -/
@[simp] theorem completedNativeC3ProductLedgerState_snd
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) (z : ℂ) :
    (WithLp.ofLp (completedNativeC3ProductLedgerState xiState z)).2 =
      nativeXiCompletionFactor z • canonicalCompletedOperatorC3State z :=
  rfl

/-- The concrete C3 coordinate is nonzero at every centered parameter whose
spectral parameter lies in the open strip. -/
theorem completedNativeC3ProductLedgerState_snd_ne_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (WithLp.ofLp (completedNativeC3ProductLedgerState xiState z)).2 ≠ 0 := by
  rw [completedNativeC3ProductLedgerState_snd]
  exact smul_ne_zero
    (nativeXiCompletionFactor_ne_zero hs)
    (by
      unfold canonicalCompletedOperatorC3State
      exact canonicalEnrichedC3SourcePort_ne_zero hs)

/-- Therefore the full product ledger is nonzero throughout the open strip,
independently of the still-unconstructed archimedean factor state. -/
theorem completedNativeC3ProductLedgerState_ne_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) {z : ℂ}
    (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeC3ProductLedgerState xiState z ≠ 0 := by
  apply weightedProductGreenState_ne_zero_of_right
  · exact nativeXiCompletionFactor_ne_zero hs
  · unfold canonicalCompletedOperatorC3State
    exact canonicalEnrichedC3SourcePort_ne_zero hs

/-- At a zeta zero the first product coordinate vanishes exactly.  The C3
coordinate remains the nonzero xi-weighted enriched port. -/
theorem completedNativeC3ProductLedgerState_fst_eq_zero_at_riemannZeta_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) (hzero : riemannZeta s = 0) :
    (WithLp.ofLp (completedNativeC3ProductLedgerState
        xiState (centeredHeightParameter s))).1 = 0 := by
  rw [completedNativeC3ProductLedgerState_fst,
    nativeHeightScalar_centeredHeightParameter_eq_riemannZeta hs,
    hzero, zero_smul]

/-- At every open-strip zeta zero, the actual completed scalar
characteristic is zero while its concrete provenance ledger is nonzero. -/
theorem riemannZeta_zero_completedCharacteristic_zero_and_c3Ledger_ne_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) (hzero : riemannZeta s = 0) :
    completedNativeOperatorCharacteristic (centeredHeightParameter s) = 0 ∧
      completedNativeC3ProductLedgerState
        xiState (centeredHeightParameter s) ≠ 0 := by
  constructor
  · rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta]
    · simp [hzero]
    · simpa using hs
  · apply completedNativeC3ProductLedgerState_ne_zero
    simpa using hs

/-- Exact strip-local Green identity still to be constructed for the
provenance-preserving completed state.  Unlike the scalar C3 intertwiner, this
identity is stated before projecting the two Hilbert channels to one scalar
Green bulk. -/
def HasCompletedNativeC3ProductLedgerOffAxisGreenIdentity
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi) : Prop :=
  ∀ z : ℂ, operatorHeightParameter z ∈ genuineCriticalStrip →
    z.im ≠ 0 →
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z =
        (z - (starRingEnd ℂ) z) *
          inner ℂ
            (completedNativeC3ProductLedgerState xiState z)
            (completedNativeC3ProductLedgerState xiState z)

/-- Two genuine component Green representations construct the concrete
completed-state identity by the exact product rule.  This theorem separates
the analytic work into the archimedean completion channel and the native C3
channel without losing either one. -/
theorem completedNativeC3ProductLedgerOffAxisGreenIdentity_of_factors
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hxi : HasDivisionFreeGreenRepresentation
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion xiState)
    (hnative : HasDivisionFreeGreenRepresentation
      nativeHeightScalar nativeHeightScalarBoundaryCompanion
        canonicalCompletedOperatorC3State) :
    HasCompletedNativeC3ProductLedgerOffAxisGreenIdentity xiState := by
  intro z hs _hz
  change completedGreenWronskian
      (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
      completedNativeOperatorBoundaryCompanion z z =
    (z - (starRingEnd ℂ) z) *
      inner ℂ
        (weightedProductGreenState
          nativeXiCompletionFactor nativeHeightScalar
          xiState canonicalCompletedOperatorC3State z)
        (weightedProductGreenState
          nativeXiCompletionFactor nativeHeightScalar
          xiState canonicalCompletedOperatorC3State z)
  calc
    completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        completedNativeOperatorBoundaryCompanion z z =
      completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        (productBoundaryCompanion
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
          nativeHeightScalar nativeHeightScalarBoundaryCompanion) z z := by
            unfold completedGreenWronskian
            rw [completedNativeOperatorBoundaryCompanion_eq_product hs]
    _ = _ := (hxi.mul hnative) z z

/-- The concrete completed-state identity would close confinement with no
additional nonvanishing premise: that premise is already discharged by the
xi-weighted C3 coordinate. -/
theorem riemannZeta_zero_re_eq_half_of_completedNativeC3ProductLedgerGreen
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    (xiState : ℂ → Hxi)
    (hgreen :
      HasCompletedNativeC3ProductLedgerOffAxisGreenIdentity xiState)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hre
  let z : ℂ := centeredHeightParameter s
  have hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip := by
    simpa [z] using hs
  have hzIm : z.im ≠ 0 := by
    dsimp [z]
    rw [centeredHeightParameter_im]
    intro him
    apply hre
    linarith
  have hdata :=
    riemannZeta_zero_completedCharacteristic_zero_and_c3Ledger_ne_zero
      xiState hs hzero
  have hcharacteristic : completedNativeOperatorCharacteristic z = 0 := by
    simpa [z] using hdata.1
  have hstate : completedNativeC3ProductLedgerState xiState z ≠ 0 := by
    simpa [z] using hdata.2
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z = 0 := by
    simp [completedGreenWronskian, hcharacteristic]
  have hgreenAt := hgreen z hzStrip hzIm
  rw [hwronskian] at hgreenAt
  have hinner :
      inner ℂ
          (completedNativeC3ProductLedgerState xiState z)
          (completedNativeC3ProductLedgerState xiState z) ≠ 0 :=
    inner_self_ne_zero.mpr hstate
  have hfixed : z = (starRingEnd ℂ) z := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hgreenAt.symm).resolve_right hinner
  have hcoord := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at hcoord
  exact hzIm (by linarith [hcoord])

end

end CarrySelfAdjointOperator
