import CarrySelfAdjointOperator.CompletedC3SymplecticGammaCommonFiberInjectivity
import CarrySelfAdjointOperator.CompletedC3CompressedSourceTailControl
import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open MeasureTheory
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Infinite

open scoped BigOperators ComplexConjugate InnerProductSpace lp

noncomputable section

def canonicalC3CommonFiberMap :
    canonicalC3RawCameraSpan →ₗ[ℝ]
      NativeCarrySpectralWeyl.Infinite.KolmogorovSpace :=
  canonicalC3KolmogorovSpan.subtype.comp
    canonicalC3CommonFiberEquiv.toLinearMap

theorem canonicalC3CommonFiberMap_injective :
    Function.Injective canonicalC3CommonFiberMap := by
  intro x y h
  apply canonicalC3CommonFiberEquiv.injective
  apply Subtype.ext
  exact h

theorem naimarkIsometry_rawSpan_ae_eq_commonFiber
    (x : canonicalC3RawCameraSpan) :
    ∀ᵐ t ∂NativeCarrySpectralWeyl.Infinite.positiveLebesgueMeasure,
      t ∈ canonicalC3CommonNaimarkInterval →
        (NativeCarrySpectralWeyl.Infinite.naimarkIsometry
          (x : NativeCarrySpectralWeyl.Infinite.CameraHilbert)) t =
          canonicalC3CommonFiberMap x := by
  let P : NativeCarrySpectralWeyl.Infinite.CameraHilbert → Prop := fun y =>
    ∃ hy : y ∈ canonicalC3RawCameraSpan,
      ∀ᵐ t ∂NativeCarrySpectralWeyl.Infinite.positiveLebesgueMeasure,
        t ∈ canonicalC3CommonNaimarkInterval →
          (NativeCarrySpectralWeyl.Infinite.naimarkIsometry y) t =
            canonicalC3CommonFiberMap ⟨y, hy⟩
  have hP : ∀ y : NativeCarrySpectralWeyl.Infinite.CameraHilbert,
      y ∈ canonicalC3RawCameraSpan → P y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨j, rfl⟩
        refine ⟨Submodule.subset_span (Set.mem_range_self j), ?_⟩
        filter_upwards [
          canonicalC3RawCameraVector_ae_eq_kolmogorov_on_common j] with t ht
        intro htcommon
        rw [ht htcommon]
        have hraw := canonicalC3CommonFiberEquiv_raw j
        simpa [canonicalC3CommonFiberMap] using
          (congrArg Subtype.val hraw).symm
    | zero =>
        refine ⟨Submodule.zero_mem _, ?_⟩
        filter_upwards [
          Lp.coeFn_zero
            NativeCarrySpectralWeyl.Infinite.KolmogorovSpace 2
            NativeCarrySpectralWeyl.Infinite.positiveLebesgueMeasure] with t ht
        intro htcommon
        rw [map_zero, ht]
        have hzero :
            (⟨(0 : NativeCarrySpectralWeyl.Infinite.CameraHilbert),
              Submodule.zero_mem _⟩ : canonicalC3RawCameraSpan) = 0 := by
          apply Subtype.ext
          rfl
        rw [hzero, map_zero]
        simp
    | add y₁ y₂ hy₁ hy₂ h₁ h₂ =>
        rcases h₁ with ⟨hy₁', h₁⟩
        rcases h₂ with ⟨hy₂', h₂⟩
        refine ⟨Submodule.add_mem _ hy₁' hy₂', ?_⟩
        filter_upwards [
          Lp.coeFn_add
            (NativeCarrySpectralWeyl.Infinite.naimarkIsometry y₁)
            (NativeCarrySpectralWeyl.Infinite.naimarkIsometry y₂),
          h₁, h₂] with t hadd h₁t h₂t
        intro htcommon
        have hy₁₂ : y₁ + y₂ ∈ canonicalC3RawCameraSpan :=
          Submodule.add_mem _ hy₁' hy₂'
        have hmap :
            canonicalC3CommonFiberMap ⟨y₁ + y₂, hy₁₂⟩ =
              canonicalC3CommonFiberMap ⟨y₁, hy₁'⟩ +
                canonicalC3CommonFiberMap ⟨y₂, hy₂'⟩ := by
          calc
            canonicalC3CommonFiberMap ⟨y₁ + y₂, hy₁₂⟩ =
                canonicalC3CommonFiberMap
                  ((⟨y₁, hy₁'⟩ : canonicalC3RawCameraSpan) +
                    ⟨y₂, hy₂'⟩) := by
              congr 1
            _ = _ := canonicalC3CommonFiberMap.map_add _ _
        rw [map_add, hadd, Pi.add_apply, h₁t htcommon, h₂t htcommon,
          hmap]
    | smul a y hy h =>
        rcases h with ⟨hy', h⟩
        refine ⟨Submodule.smul_mem _ a hy', ?_⟩
        filter_upwards [
          Lp.coeFn_smul a
            (NativeCarrySpectralWeyl.Infinite.naimarkIsometry y),
          h] with t hsmul ht
        intro htcommon
        have hys : a • y ∈ canonicalC3RawCameraSpan :=
          Submodule.smul_mem _ a hy'
        have hmap :
            canonicalC3CommonFiberMap ⟨a • y, hys⟩ =
              a • canonicalC3CommonFiberMap ⟨y, hy'⟩ := by
          calc
            canonicalC3CommonFiberMap ⟨a • y, hys⟩ =
                canonicalC3CommonFiberMap
                  (a • (⟨y, hy'⟩ : canonicalC3RawCameraSpan)) := by
              congr 1
            _ = _ := canonicalC3CommonFiberMap.map_smul _ _
        rw [map_smul, hsmul, Pi.smul_apply, ht htcommon, hmap]
  rcases hP (x : NativeCarrySpectralWeyl.Infinite.CameraHilbert) x.property with
    ⟨hx, h⟩
  simpa only [Subtype.coe_eta] using h

theorem canonicalC3CameraCoordinateIsometry_mem_rawSpan
    (v : EuclideanSpace ℝ CanonicalC3RealCoordinate) :
    canonicalC3CameraCoordinateIsometry v ∈
      canonicalC3RawCameraSpan := by
  change
    (∑ j : CanonicalC3RealCoordinate,
      v j • canonicalC3OrthonormalCameraVector j) ∈
        Submodule.span ℝ (Set.range canonicalC3RawCameraVector)
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _
    (canonicalC3OrthonormalCameraVector_mem_span_raw j)

theorem canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan
    (z : ℂ) :
    (canonicalCompletedC3SymplecticGammaCameraSource z).fst ∈
      canonicalC3RawCameraSpan := by
  change
    -canonicalC3CameraCoordinateIsometry
        (canonicalC3LegRealification
          (canonicalCompletedOperatorC3State z).1) ∈
      canonicalC3RawCameraSpan
  exact Submodule.neg_mem _
    (canonicalC3CameraCoordinateIsometry_mem_rawSpan
      (canonicalC3LegRealification
        (canonicalCompletedOperatorC3State z).1))

theorem canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan
    (z : ℂ) :
    (canonicalCompletedC3SymplecticGammaCameraSource z).snd ∈
      canonicalC3RawCameraSpan := by
  change
    canonicalC3CameraCoordinateIsometry
        (canonicalC3LegRealification
          (canonicalCompletedOperatorC3State z).2) ∈
      canonicalC3RawCameraSpan
  exact canonicalC3CameraCoordinateIsometry_mem_rawSpan
    (canonicalC3LegRealification
      (canonicalCompletedOperatorC3State z).2)

noncomputable def canonicalCompletedC3SymplecticCentralRawFst :
    canonicalC3RawCameraSpan :=
  ⟨(canonicalCompletedC3SymplecticGammaCameraSource 0).fst,
    canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan 0⟩

noncomputable def canonicalCompletedC3SymplecticCentralRawSnd :
    canonicalC3RawCameraSpan :=
  ⟨(canonicalCompletedC3SymplecticGammaCameraSource 0).snd,
    canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan 0⟩

noncomputable def canonicalCompletedC3SymplecticCentralCommonFiberFst :
    NativeCarrySpectralWeyl.Infinite.KolmogorovSpace :=
  canonicalC3CommonFiberMap
    canonicalCompletedC3SymplecticCentralRawFst

noncomputable def canonicalCompletedC3SymplecticCentralCommonFiberSnd :
    NativeCarrySpectralWeyl.Infinite.KolmogorovSpace :=
  canonicalC3CommonFiberMap
    canonicalCompletedC3SymplecticCentralRawSnd

theorem canonicalCompletedC3SymplecticCentralNaimarkFst_ae_eq_commonFiber :
    ∀ᵐ t ∂NativeCarrySpectralWeyl.Infinite.positiveLebesgueMeasure,
      t ∈ canonicalC3CommonNaimarkInterval →
        (NativeCarrySpectralWeyl.Infinite.naimarkIsometry
          (canonicalCompletedC3SymplecticGammaCameraSource 0).fst) t =
          canonicalCompletedC3SymplecticCentralCommonFiberFst := by
  simpa [canonicalCompletedC3SymplecticCentralCommonFiberFst,
    canonicalCompletedC3SymplecticCentralRawFst] using
    naimarkIsometry_rawSpan_ae_eq_commonFiber
      canonicalCompletedC3SymplecticCentralRawFst

theorem canonicalCompletedC3SymplecticCentralNaimarkSnd_ae_eq_commonFiber :
    ∀ᵐ t ∂NativeCarrySpectralWeyl.Infinite.positiveLebesgueMeasure,
      t ∈ canonicalC3CommonNaimarkInterval →
        (NativeCarrySpectralWeyl.Infinite.naimarkIsometry
          (canonicalCompletedC3SymplecticGammaCameraSource 0).snd) t =
          canonicalCompletedC3SymplecticCentralCommonFiberSnd := by
  simpa [canonicalCompletedC3SymplecticCentralCommonFiberSnd,
    canonicalCompletedC3SymplecticCentralRawSnd] using
    naimarkIsometry_rawSpan_ae_eq_commonFiber
      canonicalCompletedC3SymplecticCentralRawSnd

theorem canonicalCompletedC3SymplecticGammaCameraSource_zero_ne_zero :
    canonicalCompletedC3SymplecticGammaCameraSource 0 ≠ 0 := by
  apply canonicalCompletedC3SymplecticGammaCameraSource_ne_zero
  simpa [completedNativeHeightDomain] using
    zero_mem_completedNativeHeightDomain

theorem canonicalCompletedC3SymplecticCentralCommonFiber_nontrivial :
    canonicalCompletedC3SymplecticCentralCommonFiberFst ≠ 0 ∨
      canonicalCompletedC3SymplecticCentralCommonFiberSnd ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨hfst, hsnd⟩
  have hrawfst : canonicalCompletedC3SymplecticCentralRawFst = 0 := by
    apply canonicalC3CommonFiberMap_injective
    simpa [canonicalCompletedC3SymplecticCentralCommonFiberFst, hfst]
  have hrawsnd : canonicalCompletedC3SymplecticCentralRawSnd = 0 := by
    apply canonicalC3CommonFiberMap_injective
    simpa [canonicalCompletedC3SymplecticCentralCommonFiberSnd, hsnd]
  have hsourcefst :
      (canonicalCompletedC3SymplecticGammaCameraSource 0).fst = 0 :=
    congrArg Subtype.val hrawfst
  have hsourcesnd :
      (canonicalCompletedC3SymplecticGammaCameraSource 0).snd = 0 :=
    congrArg Subtype.val hrawsnd
  have hsourcezero :
      canonicalCompletedC3SymplecticGammaCameraSource 0 = 0 := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hsourcefst
    · exact hsourcesnd
  exact canonicalCompletedC3SymplecticGammaCameraSource_zero_ne_zero
    hsourcezero

#print axioms canonicalC3CommonFiberMap_injective
#print axioms naimarkIsometry_rawSpan_ae_eq_commonFiber
#print axioms canonicalC3CameraCoordinateIsometry_mem_rawSpan
#print axioms canonicalCompletedC3SymplecticGammaCameraSource_fst_mem_rawSpan
#print axioms canonicalCompletedC3SymplecticGammaCameraSource_snd_mem_rawSpan
#print axioms canonicalCompletedC3SymplecticCentralNaimarkFst_ae_eq_commonFiber
#print axioms canonicalCompletedC3SymplecticCentralNaimarkSnd_ae_eq_commonFiber
#print axioms canonicalCompletedC3SymplecticGammaCameraSource_zero_ne_zero
#print axioms canonicalCompletedC3SymplecticCentralCommonFiber_nontrivial

end

end CarrySelfAdjointOperator
