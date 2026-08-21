import NativeCarryC3Crosswalk.GeometricCutoffCompleteness
import CPFormal.Finite.Bracket

/-!
# Causal bracket reconstruction and uniqueness of an admissible state

The centered bracket is not only a probe.  Written with its left leg as the
index, it is an exact recurrence:

`right = bracket - left + 2 * center`.

This file packages that recurrence as a canonical reconstruction from two
seeds and a bracket field, proves existence and uniqueness of the realized
state, and then identifies the relevant unit cells inside the natural
all-bases native-camera geometry.  Thus positivity/admissibility does not
choose between several geometric realizations: once the reconstructed state
is admissible, it is the unique admissible realization of those data.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open FiniteNativeCarryOperator.Operator
open NativeCarrySpectralWeyl.Camera

/-! ## Abstract causal bracket geometry -/

variable {A : Type*} [AddCommGroup A]

/-- Unit-radius centered bracket, indexed by its left leg.  The three
coordinates are respectively the left leg, center and right leg. -/
def causalUnitBracket (x : ℕ → A) (left : ℕ) : A :=
  x left - 2 • x (left + 1) + x (left + 2)

/-- Local right-leg reconstruction.  No analysis or positivity is used. -/
theorem rightLeg_eq_bracket_sub_left_add_two_center
    (x : ℕ → A) (left : ℕ) :
    x (left + 2) =
      causalUnitBracket x left - x left + 2 • x (left + 1) := by
  unfold causalUnitBracket
  abel

/-- Two cells with the same left leg, center and bracket necessarily have
the same right leg. -/
theorem rightLeg_eq_of_left_center_bracket_eq
    {x y : ℕ → A} {left : ℕ}
    (hleft : x left = y left)
    (hcenter : x (left + 1) = y (left + 1))
    (hbracket : causalUnitBracket x left = causalUnitBracket y left) :
    x (left + 2) = y (left + 2) := by
  calc
    x (left + 2) =
        causalUnitBracket x left - x left + 2 • x (left + 1) :=
      rightLeg_eq_bracket_sub_left_add_two_center x left
    _ = causalUnitBracket y left - y left + 2 • y (left + 1) := by
      rw [hbracket, hleft, hcenter]
    _ = y (left + 2) :=
      (rightLeg_eq_bracket_sub_left_add_two_center y left).symm

/-- Discrete slope along two consecutive legs. -/
def causalSlope (x : ℕ → A) (n : ℕ) : A :=
  x (n + 1) - x n

/-- The unit bracket is exactly the increment of the discrete slope.  This is
the local Green/telescoping form of the same causal identity. -/
theorem causalUnitBracket_eq_slope_sub_slope
    (x : ℕ → A) (n : ℕ) :
    causalUnitBracket x n = causalSlope x (n + 1) - causalSlope x n := by
  simp only [causalUnitBracket, causalSlope]
  rw [show n + 1 + 1 = n + 2 by omega]
  abel

/-- First telescoping: every later slope is the initial slope plus all previous
unit brackets. -/
theorem causalSlope_eq_initial_add_sum_brackets
    (x : ℕ → A) (n : ℕ) :
    causalSlope x n =
      causalSlope x 0 + ∑ k ∈ Finset.range n, causalUnitBracket x k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep :
          causalSlope x (n + 1) =
            causalSlope x n + causalUnitBracket x n := by
        rw [causalUnitBracket_eq_slope_sub_slope]
        abel
      rw [hstep, ih, Finset.sum_range_succ]
      abel

/-- Second telescoping: a state is its left seed plus the sum of its slopes. -/
theorem state_eq_leftSeed_add_sum_slopes
    (x : ℕ → A) (n : ℕ) :
    x n = x 0 + ∑ k ∈ Finset.range n, causalSlope x k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        x (n + 1) = x n + causalSlope x n := by
          simp only [causalSlope]
          abel
        _ = (x 0 + ∑ k ∈ Finset.range n, causalSlope x k) +
              causalSlope x n := by rw [ih]
        _ = x 0 +
              ((∑ k ∈ Finset.range n, causalSlope x k) +
                causalSlope x n) := by abel

/-- Closed all-orders reconstruction as two exact telescopings. -/
theorem state_eq_double_telescope
    (x : ℕ → A) (n : ℕ) :
    x n = x 0 + ∑ k ∈ Finset.range n,
      (causalSlope x 0 + ∑ j ∈ Finset.range k, causalUnitBracket x j) := by
  rw [state_eq_leftSeed_add_sum_slopes x n]
  apply congrArg (fun z ↦ x 0 + z)
  apply Finset.sum_congr rfl
  intro k hk
  exact causalSlope_eq_initial_add_sum_brackets x k

/-- Complete causal data: two initial legs and the bracket attached to every
subsequent cell. -/
structure CausalBracketData (A : Type*) where
  leftSeed : A
  centerSeed : A
  bracket : ℕ → A

/-- The state forced by causal bracket data. -/
def causalBracketReconstruction (data : CausalBracketData A) : ℕ → A :=
  Nat.twoStepInduction data.leftSeed data.centerSeed
    (fun n left center ↦ data.bracket n - left + 2 • center)

@[simp] theorem causalBracketReconstruction_zero
    (data : CausalBracketData A) :
    causalBracketReconstruction data 0 = data.leftSeed := rfl

@[simp] theorem causalBracketReconstruction_one
    (data : CausalBracketData A) :
    causalBracketReconstruction data 1 = data.centerSeed := rfl

theorem causalBracketReconstruction_step
    (data : CausalBracketData A) (n : ℕ) :
    causalBracketReconstruction data (n + 2) =
      data.bracket n - causalBracketReconstruction data n +
        2 • causalBracketReconstruction data (n + 1) := rfl

/-- The reconstructed state realizes every prescribed bracket exactly. -/
@[simp] theorem causalUnitBracket_reconstruction
    (data : CausalBracketData A) (n : ℕ) :
    causalUnitBracket (causalBracketReconstruction data) n =
      data.bracket n := by
  rw [causalUnitBracket, causalBracketReconstruction_step]
  abel

/-- Predicate saying that a state realizes all seeds and all brackets. -/
def RealizesCausalBracketData
    (data : CausalBracketData A) (x : ℕ → A) : Prop :=
  x 0 = data.leftSeed ∧
    x 1 = data.centerSeed ∧
      ∀ n, causalUnitBracket x n = data.bracket n

theorem causalBracketReconstruction_realizes
    (data : CausalBracketData A) :
    RealizesCausalBracketData data (causalBracketReconstruction data) := by
  exact ⟨by simp, by simp, causalUnitBracket_reconstruction data⟩

/-- Explicit all-orders formula for the canonical state.  It is the double
telescoping of the initial slope and the prescribed bracket field. -/
theorem causalBracketReconstruction_eq_double_telescope
    (data : CausalBracketData A) (n : ℕ) :
    causalBracketReconstruction data n =
      data.leftSeed + ∑ k ∈ Finset.range n,
        ((data.centerSeed - data.leftSeed) +
          ∑ j ∈ Finset.range k, data.bracket j) := by
  rw [state_eq_double_telescope (causalBracketReconstruction data) n]
  simp only [causalBracketReconstruction_zero,
    causalBracketReconstruction_one, zero_add, causalSlope]
  apply congrArg (fun z ↦ data.leftSeed + z)
  apply Finset.sum_congr rfl
  intro k hk
  apply congrArg (fun z ↦ data.centerSeed - data.leftSeed + z)
  apply Finset.sum_congr rfl
  intro j hj
  exact causalUnitBracket_reconstruction data j

/-- Global causal uniqueness: equality of the two seeds and of every bracket
propagates through all right legs. -/
theorem eq_of_seed_eq_of_causalUnitBracket_eq
    {x y : ℕ → A}
    (hleft : x 0 = y 0) (hcenter : x 1 = y 1)
    (hbracket : ∀ n, causalUnitBracket x n = causalUnitBracket y n) :
    x = y := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact hleft
  | one => exact hcenter
  | more n hn hn1 =>
      exact rightLeg_eq_of_left_center_bracket_eq hn hn1 (hbracket n)

/-- Any realization of the data is the canonical causal reconstruction. -/
theorem causalBracketReconstruction_unique
    (data : CausalBracketData A) (x : ℕ → A)
    (hx : RealizesCausalBracketData data x) :
    x = causalBracketReconstruction data := by
  apply eq_of_seed_eq_of_causalUnitBracket_eq hx.1 hx.2.1
  intro n
  rw [hx.2.2 n, causalUnitBracket_reconstruction]

/-- Existence and uniqueness of the state generated by the bracket geometry. -/
theorem existsUnique_realizesCausalBracketData
    (data : CausalBracketData A) :
    ∃! x : ℕ → A, RealizesCausalBracketData data x := by
  refine ⟨causalBracketReconstruction data,
    causalBracketReconstruction_realizes data, ?_⟩
  intro x hx
  exact causalBracketReconstruction_unique data x hx

/-- If the canonical reconstruction satisfies any additional admissibility
predicate (positivity, finite energy, a boundary condition, or their
conjunction), then it is the unique admissible realization.  The predicate
supplies existence in the desired class; geometric propagation supplies
uniqueness. -/
theorem existsUnique_admissible_realizesCausalBracketData
    (data : CausalBracketData A) (Admissible : (ℕ → A) → Prop)
    (hadmissible : Admissible (causalBracketReconstruction data)) :
    ∃! x : ℕ → A,
      Admissible x ∧ RealizesCausalBracketData data x := by
  refine ⟨causalBracketReconstruction data,
    ⟨hadmissible, causalBracketReconstruction_realizes data⟩, ?_⟩
  intro x hx
  exact causalBracketReconstruction_unique data x hx.2

/-! ## The causal cells already present in the all-bases atlas -/

/-- Every natural center `center >= 3` is the first aligned center of the
camera carrying the same label. -/
theorem naturalCamera_first_alignedCenter_eq_self
    {center : ℕ} (hcenter : 3 ≤ center) :
    alignedCenter center 0 = center := by
  rw [alignedCenter_of_ne_two (by omega)]
  simp

/-- Every natural camera contains the unit radius. -/
theorem one_mem_naturalCamera_radiusSet
    {camera : ℕ} (hcamera : 3 ≤ camera) :
    1 ∈ radiusSet camera := by
  rw [mem_radiusSet_iff]
  constructor
  · omega
  · omega

/-- The first unit-radius cell of camera `left + 1` is literally the causal
cell with that left leg.  Hence the all-bases atlas contains every unit cell
starting at `left >= 2`. -/
theorem naturalCamera_first_centeredBracket_eq_causalUnitBracket
    (time : ℝ) {left : ℕ} (hleft : 2 ≤ left) :
    centeredBracket time (alignedCenter (left + 1) 0) 1 =
      causalUnitBracket (nativeState time) left := by
  rw [alignedCenter_of_ne_two (by omega)]
  simp [centeredBracket, causalUnitBracket, Nat.add_assoc]

/-- Packaged geometric coverage statement: camera `left + 1` contains radius
one, is centered at `left + 1`, and realizes the causal bracket of the native
state. -/
theorem allBases_contains_causal_unit_cell
    (time : ℝ) {left : ℕ} (hleft : 2 ≤ left) :
    1 ∈ radiusSet (left + 1) ∧
      alignedCenter (left + 1) 0 = left + 1 ∧
        centeredBracket time (alignedCenter (left + 1) 0) 1 =
          causalUnitBracket (nativeState time) left := by
  exact ⟨one_mem_naturalCamera_radiusSet (by omega),
    naturalCamera_first_alignedCenter_eq_self (by omega),
    naturalCamera_first_centeredBracket_eq_causalUnitBracket time hleft⟩

/-! ## All-bases tail propagation -/

/-- The natural all-bases unit cells determine the entire state from depth
two onward once depths two and three are known. -/
theorem eq_on_ge_two_of_naturalCameraUnitBrackets_eq
    {x y : ℕ → A}
    (h₂ : x 2 = y 2) (h₃ : x 3 = y 3)
    (hcamera : ∀ camera : ℕ, 3 ≤ camera →
      causalUnitBracket x (camera - 1) =
        causalUnitBracket y (camera - 1)) :
    ∀ n : ℕ, 2 ≤ n → x n = y n := by
  let xTail : ℕ → A := fun n ↦ x (n + 2)
  let yTail : ℕ → A := fun n ↦ y (n + 2)
  have htailBracket : ∀ n : ℕ,
      causalUnitBracket xTail n = causalUnitBracket yTail n := by
    intro n
    have h := hcamera (n + 3) (by omega)
    simpa [causalUnitBracket, xTail, yTail, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h
  have htail : xTail = yTail :=
    eq_of_seed_eq_of_causalUnitBracket_eq h₂ h₃ htailBracket
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [xTail, yTail, Nat.add_comm] using congrFun htail k

/-- Full all-bases uniqueness after adjoining the two lower seed coordinates.
The four initial coordinates and the first unit cell of every natural camera
determine the whole state. -/
theorem eq_of_four_seed_eq_of_naturalCameraUnitBrackets_eq
    {x y : ℕ → A}
    (h₀ : x 0 = y 0) (h₁ : x 1 = y 1)
    (h₂ : x 2 = y 2) (h₃ : x 3 = y 3)
    (hcamera : ∀ camera : ℕ, 3 ≤ camera →
      causalUnitBracket x (camera - 1) =
        causalUnitBracket y (camera - 1)) :
    x = y := by
  funext n
  by_cases hn : 2 ≤ n
  · exact eq_on_ge_two_of_naturalCameraUnitBrackets_eq
      h₂ h₃ hcamera n hn
  · interval_cases n <;> assumption

end CarrySelfAdjointOperator


