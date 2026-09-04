import CarrySelfAdjointOperator.ProjectiveValveFiniteSpanIncidence
import CarrySelfAdjointOperator.AllBaseBracketIncidenceGlobalIndependence
import CarrySelfAdjointOperator.BR2ProjectiveHilbertIncidenceTransport

/-!
# Native bracket incidences in projective-valve finite spans

Finitely supported real incidence vectors embed in formal curvature series.
The exact projective depth change is linear and invertible, so the transported
series retain every coefficient and every finite linear relation. Native
center pivots give independence, including all even and odd orders, and hence
supply the independence premise of the projective finite-span geometry.

The range of the transported finite-support series also maps injectively to
the already constructed TFVD Hilbert carrier. This is an algebraic core map;
no summability of arbitrary formal series or native moment Gram identity is
asserted.
-/

namespace CarrySelfAdjointOperator

noncomputable section

namespace ProjectiveDepth

variable {R : Type*} [CommRing R]

/-- The existing projective coordinate change preserves the full linear
structure, in addition to its previously proved inverse identities. -/
def coordinateChangeLinearEquiv : PowerSeries R ≃ₗ[R] PowerSeries R where
  toFun := toProjective
  invFun := fromProjective
  left_inv := fromProjective_toProjective
  right_inv := toProjective_fromProjective
  map_add' := toProjective_add
  map_smul' := fun c f =>
    PowerSeries.subst_smul (inverseCoordinate_hasSubst (R := R)) c f

@[simp] theorem coordinateChangeLinearEquiv_apply (f : PowerSeries R) :
    coordinateChangeLinearEquiv f = toProjective f := rfl

end ProjectiveDepth

namespace ProjectiveValve

open PowerSeries FiniteNativeCarryOperator.Camera
open scoped LinearAlgebra.Projectivization

/-- The original-depth curvature series of a finite incidence ledger. -/
def nativeIncidenceSeries : (ℕ →₀ ℝ) →ₗ[ℝ] PowerSeries ℝ where
  toFun v := mk (fun n => v n)
  map_add' v w := by
    ext n
    simp
  map_smul' c v := by
    ext n
    simp

@[simp] theorem coeff_nativeIncidenceSeries (v : ℕ →₀ ℝ) (n : ℕ) :
    coeff n (nativeIncidenceSeries v) = v n := by
  simp [nativeIncidenceSeries]

/-- No incidence coordinate is lost by the series representation. -/
theorem nativeIncidenceSeries_injective :
    Function.Injective nativeIncidenceSeries := by
  intro v w h
  ext n
  simpa only [coeff_nativeIncidenceSeries] using congrArg (coeff n) h

/-- Transport finite incidence ledgers to projective-depth curvatures. -/
def nativeIncidenceProjectiveMap : (ℕ →₀ ℝ) →ₗ[ℝ] PowerSeries ℝ :=
  ProjectiveDepth.coordinateChangeLinearEquiv.toLinearMap.comp nativeIncidenceSeries

@[simp] theorem nativeIncidenceProjectiveMap_apply (v : ℕ →₀ ℝ) :
    nativeIncidenceProjectiveMap v =
      ProjectiveDepth.toProjective (nativeIncidenceSeries v) := rfl

/-- The inverse chart recovers the original series exactly. -/
@[simp] theorem fromProjective_nativeIncidenceProjectiveMap (v : ℕ →₀ ℝ) :
    ProjectiveDepth.fromProjective (nativeIncidenceProjectiveMap v) =
      nativeIncidenceSeries v :=
  ProjectiveDepth.fromProjective_toProjective _

/-- Coefficientwise recovery provides an explicit inverse on every incidence. -/
@[simp] theorem coeff_fromProjective_nativeIncidenceProjectiveMap
    (v : ℕ →₀ ℝ) (n : ℕ) :
    coeff n (ProjectiveDepth.fromProjective (nativeIncidenceProjectiveMap v)) = v n := by
  rw [fromProjective_nativeIncidenceProjectiveMap, coeff_nativeIncidenceSeries]

/-- The projective transport is injective on the whole finite-support core. -/
theorem nativeIncidenceProjectiveMap_injective :
    Function.Injective nativeIncidenceProjectiveMap :=
  ProjectiveDepth.coordinateChangeLinearEquiv.injective.comp nativeIncidenceSeries_injective

/-- All finite linear relations are preserved and reflected, including
relations involving several cameras with overlapping incidence supports. -/
theorem nativeIncidenceProjectiveMap_sum_eq_zero_iff
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → ℕ →₀ ℝ) :
    (∑ i ∈ s, a i • nativeIncidenceProjectiveMap (v i)) = 0 ↔
      (∑ i ∈ s, a i • v i) = 0 := by
  simp only [← map_smul]
  rw [← map_sum]
  exact nativeIncidenceProjectiveMap_injective.eq_iff' (map_zero _)

/-- One actual centered bracket, expressed in projective-depth curvature
coordinates. -/
def nativeBracketProjectiveCurvature (base radius index : ℕ) : PowerSeries ℝ :=
  nativeIncidenceProjectiveMap (cameraBracketIncidence base radius index)

/-- The native center pivots remain exactly recoverable after the projective
change; the pivot at the owned center is `-2`. -/
theorem nativeBracketProjectiveCurvature_centerCoefficient
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (i j : ℕ) :
    coeff (alignedCenter base j)
        (ProjectiveDepth.fromProjective (nativeBracketProjectiveCurvature base radius i)) =
      if i = j then (-2 : ℝ) else 0 := by
  rw [nativeBracketProjectiveCurvature, coeff_fromProjective_nativeIncidenceProjectiveMap]
  exact cameraBracketIncidence_apply_alignedCenter hbase hradius i j

/-- Every injectively indexed finite native bracket family remains linearly
independent in the projective curvature coordinate. -/
theorem nativeBracketProjectiveCurvature_linearIndependent
    {ι : Type*} [Fintype ι] {base radius : ℕ}
    (hbase : IsSupported base) (hradius : radius ∈ radiusSet base)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    LinearIndependent ℝ (fun i => nativeBracketProjectiveCurvature base radius (index i)) :=
  (cameraBracketIncidence_linearIndependent_of_injective hbase hradius index hindex).map_injOn
    nativeIncidenceProjectiveMap nativeIncidenceProjectiveMap_injective.injOn

/-- Global even-order independence survives the same transport. -/
theorem nativeBracketProjectiveCurvature_even_linearIndependent
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ (fun n : ℕ => nativeBracketProjectiveCurvature base radius (2 * n)) :=
  (evenCameraBracketIncidence_linearIndependent_global hbase hradius).map_injOn
    nativeIncidenceProjectiveMap nativeIncidenceProjectiveMap_injective.injOn

/-- Global odd-order independence survives the same transport. -/
theorem nativeBracketProjectiveCurvature_odd_linearIndependent
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ => nativeBracketProjectiveCurvature base radius (2 * n + 1)) :=
  (oddCameraBracketIncidence_linearIndependent_global hbase hradius).map_injOn
    nativeIncidenceProjectiveMap nativeIncidenceProjectiveMap_injective.injOn

/-- Every supported bracket supplies a nonzero projective curvature. -/
theorem nativeBracketProjectiveCurvature_ne_zero
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (n : ℕ) :
    nativeBracketProjectiveCurvature base radius n ≠ 0 := by
  intro hzero
  have h := nativeBracketProjectiveCurvature_centerCoefficient hbase hradius n n
  have hback : ProjectiveDepth.fromProjective (0 : PowerSeries ℝ) = 0 :=
    ProjectiveDepth.coordinateChangeLinearEquiv.symm.map_zero
  rw [hzero, hback] at h
  norm_num at h

/-- The projective direction of a native bracket, with nonvanishing derived
from its actual center pivot. -/
def nativeBracketProjectiveDirection
    {base radius : ℕ} (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) (n : ℕ) : ProjectiveValveDirection ℝ :=
  Projectivization.mk ℝ (nativeBracketProjectiveCurvature base radius n)
    (nativeBracketProjectiveCurvature_ne_zero hbase hradius n)

/-- Native incidence independence discharges the projective independence
premise of the finite-span API. -/
theorem nativeBracketProjectiveDirection_independent
    {ι : Type*} [Fintype ι] {base radius : ℕ}
    (hbase : IsSupported base) (hradius : radius ∈ radiusSet base)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    Projectivization.Independent (fun i => nativeBracketProjectiveDirection hbase hradius (index i)) :=
  Projectivization.Independent.mk _ _
    (nativeBracketProjectiveCurvature_linearIndependent hbase hradius index hindex)

/-- Exact finite-span dimension, with independence supplied by the native
geometry rather than added as a hypothesis. -/
theorem nativeBracketProjectiveDirection_finiteSpan_finrank
    {ι : Type*} [Fintype ι] {base radius : ℕ}
    (hbase : IsSupported base) (hradius : radius ∈ radiusSet base)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    Module.finrank ℝ (projectiveValveFiniteSpanSubspace
      (fun i => nativeBracketProjectiveDirection hbase hradius (index i))) = Fintype.card ι :=
  projectiveValveFiniteSpanSubspace_finrank_eq_card _
    (nativeBracketProjectiveDirection_independent hbase hradius index hindex)

/-- The corresponding multiplicative subgroup is precisely the supremum of
the actual native bracket direction orbits. -/
theorem nativeBracketProjectiveDirection_finiteSpan_eq_iSup_orbits
    {ι : Type*} [Fintype ι] {base radius : ℕ}
    (hbase : IsSupported base) (hradius : radius ∈ radiusSet base) (index : ι → ℕ) :
    projectiveValveFiniteSpan (fun i => nativeBracketProjectiveDirection hbase hradius (index i)) =
      ⨆ i, projectiveValveDirectionOrbit (nativeBracketProjectiveDirection hbase hradius (index i)) :=
  projectiveValveFiniteSpan_eq_iSup_orbits _

/-- Exact algebraic equivalence onto the projective finite-support core. -/
def nativeIncidenceProjectiveEquivRange :
    (ℕ →₀ ℝ) ≃ₗ[ℝ] LinearMap.range nativeIncidenceProjectiveMap :=
  LinearEquiv.ofInjective nativeIncidenceProjectiveMap nativeIncidenceProjectiveMap_injective

/-- Transfer this core to the already constructed TFVD Hilbert carrier. The
domain is the range of finite-support incidences, not all formal series. -/
def nativeProjectiveCoreToHilbert :
    LinearMap.range nativeIncidenceProjectiveMap →ₗ[ℝ] CanonicalCompletedTfvdGreenHilbertCarrier :=
  br2CameraBracketProjectiveHilbertMap.comp nativeIncidenceProjectiveEquivRange.symm.toLinearMap

/-- The Hilbert handoff preserves every incidence coordinate. -/
theorem nativeProjectiveCoreToHilbert_injective :
    Function.Injective nativeProjectiveCoreToHilbert :=
  br2CameraBracketProjectiveHilbertMap_injective.comp nativeIncidenceProjectiveEquivRange.symm.injective

/-- Both paths from an incidence to the existing Hilbert carrier agree. -/
@[simp] theorem nativeProjectiveCoreToHilbert_incidence (v : ℕ →₀ ℝ) :
    nativeProjectiveCoreToHilbert (nativeIncidenceProjectiveEquivRange v) =
      br2CameraBracketProjectiveHilbertMap v := by
  change br2CameraBracketProjectiveHilbertMap
      (nativeIncidenceProjectiveEquivRange.symm (nativeIncidenceProjectiveEquivRange v)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- On every native bracket, the projective path lands in the same concrete
vertical state as the original BR2 construction. -/
theorem nativeProjectiveCoreToHilbert_bracket (base radius n : ℕ) :
    nativeProjectiveCoreToHilbert
        (nativeIncidenceProjectiveEquivRange (cameraBracketIncidence base radius n)) =
      br2CameraBracketVerticalState base radius n := by
  rw [nativeProjectiveCoreToHilbert_incidence,
    br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]

end ProjectiveValve

end
end CarrySelfAdjointOperator
