import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.PSeries
import CarrySelfAdjointOperator.HistoricalJHCoequalizer

open scoped ENNReal

namespace CarrySelfAdjointOperator

open Metric

noncomputable section

/-! ## The determined tower Hilbert scale

The historical audit fixes the tower coordinate `j` independently of the
J/H-provenance axes: its physical index is `PNat`, the value space is
`ℓ²(j ≥ 1)`, and the flux space has the norm with weight `j⁻²`.

The full pre-quotient provenance norm is intentionally absent from this
module.  Thus none of the definitions below equips the passive J/H factor
with an invented measure, nor does it construct `H_Q^0` or `H_Q^-1`.

`HistoricalTowerHminus1` is a coordinate-faithful model of the weighted
space: an element stores its scaled coordinates `y_j / j`; the exported
`historicalTowerHminus1RawCoordinate` recovers the physical coordinate
`y_j`.  This makes the audited equality
`‖diag(j) x‖₋₁ = ‖x‖₀` definitionally transparent at the completed level.
-/

/-- The finite physical tower core, with the historical index `j ≥ 1`. -/
abbrev HistoricalTowerCore := PNat →₀ ℂ

/-- The finite-core number operator on one tower basis atom. -/
def historicalTowerNumberCoreAt (j : PNat) : ℂ →ₗ[ℂ] HistoricalTowerCore where
  toFun a := Finsupp.single j ((j : ℂ) * a)
  map_add' a b := by simp [mul_add]
  map_smul' a b := by
    simp only [smul_eq_mul, Finsupp.smul_single, RingHom.id_apply]
    ring_nf

/-- `diag(j)` on the finite tower core. -/
def historicalTowerNumberCore : HistoricalTowerCore →ₗ[ℂ] HistoricalTowerCore :=
  Finsupp.lsum ℂ historicalTowerNumberCoreAt

theorem historicalTowerNumberCore_apply
    (x : HistoricalTowerCore) (j : PNat) :
    historicalTowerNumberCore x j = (j : ℂ) * x j := by
  classical
  induction x using Finsupp.induction with
  | zero => simp [historicalTowerNumberCore]
  | single_add a b x ha hb ih =>
      rw [LinearMap.map_add, Finsupp.add_apply, ih]
      rw [historicalTowerNumberCore, Finsupp.lsum_single]
      simp only [historicalTowerNumberCoreAt, LinearMap.coe_mk, AddHom.coe_mk,
        Finsupp.single_apply]
      by_cases h : a = j
      · subst a
        simp [mul_add]
      · simp [h]

/-- The finite-core inverse `diag(1/j)`, valid because the historical tower
uses `PNat` rather than an index containing zero. -/
def historicalTowerNumberInvCoreAt (j : PNat) : ℂ →ₗ[ℂ] HistoricalTowerCore where
  toFun a := Finsupp.single j (a / (j : ℂ))
  map_add' a b := by simp [add_div]
  map_smul' a b := by
    simp only [smul_eq_mul, Finsupp.smul_single, RingHom.id_apply]
    ring_nf

def historicalTowerNumberInvCore : HistoricalTowerCore →ₗ[ℂ] HistoricalTowerCore :=
  Finsupp.lsum ℂ historicalTowerNumberInvCoreAt

theorem historicalTowerNumberInvCore_apply
    (x : HistoricalTowerCore) (j : PNat) :
    historicalTowerNumberInvCore x j = x j / (j : ℂ) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp [historicalTowerNumberInvCore]
  | single_add a b x ha hb ih =>
      rw [LinearMap.map_add, Finsupp.add_apply, ih]
      rw [historicalTowerNumberInvCore, Finsupp.lsum_single]
      simp only [historicalTowerNumberInvCoreAt, LinearMap.coe_mk, AddHom.coe_mk,
        Finsupp.single_apply]
      by_cases h : a = j
      · subst a
        simp [add_div]
      · simp [h]

theorem historicalTowerNumberInvCore_comp_number :
    historicalTowerNumberInvCore.comp historicalTowerNumberCore = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro j
  rw [LinearMap.comp_apply, historicalTowerNumberInvCore_apply,
    historicalTowerNumberCore_apply]
  have hj : (j : ℂ) ≠ 0 := by exact_mod_cast j.ne_zero
  field_simp
  simp

theorem historicalTowerNumberCore_comp_inv :
    historicalTowerNumberCore.comp historicalTowerNumberInvCore = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro j
  rw [LinearMap.comp_apply, historicalTowerNumberCore_apply,
    historicalTowerNumberInvCore_apply]
  have hj : (j : ℂ) ≠ 0 := by exact_mod_cast j.ne_zero
  field_simp
  simp

/-- The algebraic `H⁰` product on finite tower vectors. -/
def historicalTowerH0CoreInner
    (x y : HistoricalTowerCore) : ℂ :=
  x.sum fun j a => star a * y j

/-- The algebraic `H⁻¹` product on the same physical finite vectors.  Written
through `diag(1/j)`, it is exactly the finite sum with weight `j⁻²`. -/
def historicalTowerHminus1CoreInner
    (x y : HistoricalTowerCore) : ℂ :=
  historicalTowerH0CoreInner
    (historicalTowerNumberInvCore x)
    (historicalTowerNumberInvCore y)

/-- The exact finite-core isometry identity, before completion. -/
theorem historicalTowerNumberCore_inner
    (x y : HistoricalTowerCore) :
    historicalTowerHminus1CoreInner (historicalTowerNumberCore x)
      (historicalTowerNumberCore y) =
      historicalTowerH0CoreInner x y := by
  simp only [historicalTowerHminus1CoreInner]
  change historicalTowerH0CoreInner
      ((historicalTowerNumberInvCore.comp historicalTowerNumberCore) x)
      ((historicalTowerNumberInvCore.comp historicalTowerNumberCore) y) =
    historicalTowerH0CoreInner x y
  rw [historicalTowerNumberInvCore_comp_number]
  rfl

/-- The standard complete `ℓ²` model of the historical value space `H⁰`. -/
abbrev HistoricalTowerH0 := lp (fun _ : PNat => ℂ) 2

/-- Finite tower vectors included in the standard complete `ℓ²` model. -/
def historicalTowerCoreToH0 (x : HistoricalTowerCore) : HistoricalTowerH0 :=
  ⟨fun j => x j, by
    apply memℓp_gen
    have h := (Finsupp.hasFiniteSupport x).comp
      (g := fun z : ℂ => ‖z‖ ^ (2 : ℝ)) (by simp)
    simpa [Function.comp_def] using summable_of_hasFiniteSupport h⟩

@[simp]
theorem historicalTowerCoreToH0_apply
    (x : HistoricalTowerCore) (j : PNat) :
    historicalTowerCoreToH0 x j = x j := rfl

/-- A complete coordinate model of the historical weighted `H⁻¹` space.
The stored coordinate is `y_j / j`; `rawCoordinate` below recovers `y_j`. -/
abbrev HistoricalTowerHminus1 := ULift.{0} HistoricalTowerH0

/-- The scaled `ℓ²` coordinate of a vector of `H⁻¹`. -/
def historicalTowerHminus1ScaledCoordinate
    (y : HistoricalTowerHminus1) : HistoricalTowerH0 :=
  LinearIsometryEquiv.ulift.{0} ℂ HistoricalTowerH0 y

/-- The physical tower coordinate in `H⁻¹`.  Consequently its squared `ℓ²`
weight is `|y_j|² / j²`, exactly as prescribed by the audit. -/
def historicalTowerHminus1RawCoordinate
    (y : HistoricalTowerHminus1) (j : PNat) : ℂ :=
  (j : ℂ) * historicalTowerHminus1ScaledCoordinate y j

theorem historicalTowerHminus1_raw_div
    (y : HistoricalTowerHminus1) (j : PNat) :
    historicalTowerHminus1RawCoordinate y j / (j : ℂ) =
      historicalTowerHminus1ScaledCoordinate y j := by
  dsimp [historicalTowerHminus1RawCoordinate]
  have hj : (j : ℂ) ≠ 0 := by exact_mod_cast j.ne_zero
  field_simp

/-- The completed tower number map `H⁰ → H⁻¹`. -/
def historicalTowerNumberIsometry :
    HistoricalTowerH0 →ₗᵢ[ℂ] HistoricalTowerHminus1 :=
  (LinearIsometryEquiv.ulift.{0} ℂ HistoricalTowerH0).symm.toLinearIsometry

/-- Its completed inverse, corresponding to `diag(1/j)` in physical
coordinates. -/
def historicalTowerNumberIsometryInv :
    HistoricalTowerHminus1 →ₗᵢ[ℂ] HistoricalTowerH0 :=
  (LinearIsometryEquiv.ulift.{0} ℂ HistoricalTowerH0).toLinearIsometry

theorem historicalTowerNumberIsometry_norm
    (x : HistoricalTowerH0) :
    ‖historicalTowerNumberIsometry x‖ = ‖x‖ :=
  historicalTowerNumberIsometry.norm_map x

theorem historicalTowerNumberIsometryInv_apply_number
    (x : HistoricalTowerH0) :
    historicalTowerNumberIsometryInv (historicalTowerNumberIsometry x) = x := rfl

theorem historicalTowerNumberIsometry_apply_inv
    (y : HistoricalTowerHminus1) :
    historicalTowerNumberIsometry (historicalTowerNumberIsometryInv y) = y := rfl

theorem historicalTowerNumberIsometry_rawCoordinate
    (x : HistoricalTowerH0) (j : PNat) :
    historicalTowerHminus1RawCoordinate (historicalTowerNumberIsometry x) j =
      (j : ℂ) * x j := rfl

/-- The completed isometry agrees coordinatewise with the audited finite-core
number operator. -/
theorem historicalTowerNumberIsometry_extends_core
    (x : HistoricalTowerCore) (j : PNat) :
    historicalTowerHminus1RawCoordinate
        (historicalTowerNumberIsometry (historicalTowerCoreToH0 x)) j =
      historicalTowerNumberCore x j := by
  rw [historicalTowerNumberIsometry_rawCoordinate,
    historicalTowerCoreToH0_apply, historicalTowerNumberCore_apply]

/-- The historical zero-time tower state `h(j) = 1/j` is a genuine `H⁰`
vector.  The proof uses only the `p=2` series, never identifies the resulting
constant flux with an `H⁰` vector. -/
def historicalTowerZeroTime : HistoricalTowerH0 :=
  ⟨fun j => (1 : ℂ) / (j : ℂ), by
    apply memℓp_gen
    have hsNat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    have hsPNat : Summable (fun j : PNat => ((j : ℝ) ^ (2 : ℕ))⁻¹) :=
      (summable_pnat_iff_summable_nat).mpr hsNat
    refine hsPNat.congr ?_
    intro j
    rw [norm_div, norm_one]
    norm_num⟩

@[simp]
theorem historicalTowerZeroTime_apply (j : PNat) :
    historicalTowerZeroTime j = (1 : ℂ) / (j : ℂ) := rfl

/-- In physical `H⁻¹` coordinates the zero-time flux is the constant
sequence.  It is intentionally stated through the weighted target space,
not as a spurious assertion that the constant sequence lies in `H⁰`. -/
theorem historicalTowerNumberIsometry_zeroTime_rawCoordinate
    (j : PNat) :
    historicalTowerHminus1RawCoordinate
        (historicalTowerNumberIsometry historicalTowerZeroTime) j = 1 := by
  rw [historicalTowerNumberIsometry_rawCoordinate,
    historicalTowerZeroTime_apply]
  have hj : (j : ℂ) ≠ 0 := by exact_mod_cast j.ne_zero
  field_simp

/-- The graph of the completed *tower* number is closed.  This is deliberately
not named `HistoricalPostT0BoundaryRelation`: that historical relation lives
on the full J/H quotient scale, whose provenance norm is not specified by the
audited sources. -/
def historicalTowerNumberGraph : Set (HistoricalTowerH0 × HistoricalTowerHminus1) :=
  { z | z.2 = historicalTowerNumberIsometry z.1 }

theorem isClosed_historicalTowerNumberGraph :
    IsClosed historicalTowerNumberGraph := by
  exact isClosed_eq continuous_snd
    (historicalTowerNumberIsometry.continuous.comp continuous_fst)

theorem historicalTowerNumberGraph_singleValued
    {x : HistoricalTowerH0} {y₁ y₂ : HistoricalTowerHminus1}
    (hy₁ : (x, y₁) ∈ historicalTowerNumberGraph)
    (hy₂ : (x, y₂) ∈ historicalTowerNumberGraph) :
    y₁ = y₂ := by
  exact hy₁.trans hy₂.symm

theorem historicalTowerNumberGraph_zero_flux
    {y : HistoricalTowerHminus1}
    (hy : (0, y) ∈ historicalTowerNumberGraph) :
    y = 0 := by
  simpa [historicalTowerNumberGraph] using hy

/-- The physical-prime forward graph map on the completed tower scale.  The
prime here is the material tower parameter `p_T`; no analysis prime is
identified with it. -/
def historicalTowerLogForward (pT : ℕ) :
    HistoricalTowerH0 → HistoricalTowerH0 × HistoricalTowerHminus1 :=
  fun x => (x, (Real.log (pT : ℝ) : ℂ) • historicalTowerNumberIsometry x)

def historicalTowerLogGraph (pT : ℕ) :
    Set (HistoricalTowerH0 × HistoricalTowerHminus1) :=
  { z | z.2 = (Real.log (pT : ℝ) : ℂ) • historicalTowerNumberIsometry z.1 }

theorem historicalTowerLogForward_mem_graph
    (pT : ℕ) (x : HistoricalTowerH0) :
    historicalTowerLogForward pT x ∈ historicalTowerLogGraph pT := rfl

/-- Generic exact transport of quotient norms along an isometric linear
equivalence.  This is the quotient/completion ingredient available without
choosing a norm on the historical J/H provenance carrier. -/
def quotientLIEOfLinearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (K : Submodule ℂ E) :
    (E ⧸ K) ≃ₗᵢ[ℂ] (F ⧸ K.map e.toLinearEquiv.toLinearMap) := by
  let f : E ≃ₗ[ℂ] F := e.toLinearEquiv
  let K' : Submodule ℂ F := K.map f.toLinearMap
  refine
    { __ := Submodule.Quotient.equiv K K' f rfl
      norm_map' := ?_ }
  intro q
  refine Submodule.Quotient.induction_on K q ?_
  intro x
  simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  change ‖(QuotientAddGroup.mk (s := K'.toAddSubgroup) (f x))‖ =
    ‖(QuotientAddGroup.mk (s := K.toAddSubgroup) x)‖
  rw [QuotientAddGroup.norm_mk, QuotientAddGroup.norm_mk]
  change Metric.infDist (e x)
      ((K.map e.toLinearEquiv.toLinearMap : Submodule ℂ F) : Set F) =
    Metric.infDist x (K : Set E)
  rw [Submodule.map_coe]
  convert (Metric.infDist_image e.isometry (x := x) (t := (K : Set E))) using 1; rfl

end

end CarrySelfAdjointOperator
