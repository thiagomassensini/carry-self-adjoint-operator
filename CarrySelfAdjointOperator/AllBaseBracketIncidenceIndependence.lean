import CarrySelfAdjointOperator.AllBaseCenterLegNoDiagonal
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# All-base bracket-incidence independence

The center--leg divisibility split does more than remove a spurious diagonal.
Every centered bracket owns a pivot coordinate on the aligned-center lattice:
its coefficient there is `-2`, while every leg of every bracket lies outside
that lattice. Distinct aligned centers are distinct because the camera slope
is positive.

Consequently, evaluating a finite linear combination at the center owned by
one bracket recovers exactly its coefficient. Every injectively indexed
finite family of bracket-incidence vectors is therefore linearly independent.
This holds for every supported base, including composite bases, and gives the
native source of the strictness required after Hankel semidefiniteness.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Every supported camera has a positive center slope. -/
theorem cameraSlope_pos_of_supported
    {base : ℕ} (hbase : IsSupported base) :
    0 < cameraSlope base := by
  change 2 ≤ base at hbase
  by_cases h2 : base = 2
  · subst base
    simp
  · rw [cameraSlope_of_ne_two h2]
    omega

/-- The aligned-center map is injective in every supported camera. -/
theorem alignedCenter_injective_of_supported
    {base : ℕ} (hbase : IsSupported base) :
    Function.Injective (alignedCenter base) := by
  intro i j hij
  rw [alignedCenter_eq_cameraSlope_mul,
    alignedCenter_eq_cameraSlope_mul] at hij
  have hsucc : i + 1 = j + 1 :=
    Nat.mul_left_cancel (cameraSlope_pos_of_supported hbase) hij
  omega

/-- Real incidence vector of one centered bracket: unit mass on both legs and
coefficient `-2` at the aligned center. -/
def cameraBracketIncidence
    (base radius index : ℕ) : ℕ →₀ ℝ :=
  Finsupp.single (cameraLeftLeg base index radius) 1 +
    Finsupp.single (alignedCenter base index) (-2) +
      Finsupp.single (cameraRightLeg base index radius) 1

/-- Evaluation on the center lattice is diagonal: the bracket at index `i`
has value `-2` at its own center and zero at every other aligned center.
The vanishing of both leg terms is exactly the all-base center--leg no-go. -/
@[simp] theorem cameraBracketIncidence_apply_alignedCenter
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (i j : ℕ) :
    cameraBracketIncidence base radius i (alignedCenter base j) =
      if i = j then (-2 : ℝ) else 0 := by
  classical
  have hleft :
      cameraLeftLeg base i radius ≠ alignedCenter base j :=
    (alignedCenter_ne_cameraLeftLeg hbase hradius j i).symm
  have hright :
      cameraRightLeg base i radius ≠ alignedCenter base j :=
    (alignedCenter_ne_cameraRightLeg hbase hradius j i).symm
  by_cases hij : i = j
  · subst j
    simp [cameraBracketIncidence, hleft, hright]
  · have hcenter : alignedCenter base i ≠ alignedCenter base j :=
      fun h => hij (alignedCenter_injective_of_supported hbase h)
    simp [cameraBracketIncidence, hleft, hright, hcenter, hij]

/-- Any injectively indexed finite family of bracket incidences is linearly
independent. Each coefficient is recovered by evaluating the combination at
its uniquely owned aligned center. -/
theorem cameraBracketIncidence_linearIndependent_of_injective
    {ι : Type*} [Fintype ι]
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    LinearIndependent ℝ
      (fun i : ι => cameraBracketIncidence base radius (index i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  have hdiag : ∀ j : ι,
      cameraBracketIncidence base radius (index j)
          (alignedCenter base (index i)) =
        if j = i then (-2 : ℝ) else 0 := by
    intro j
    rw [cameraBracketIncidence_apply_alignedCenter hbase hradius]
    by_cases hji : j = i
    · simp [hji]
    · have hne : index j ≠ index i := fun h => hji (hindex h)
      simp [hji, hne]
  have heval :
      (∑ j : ι,
        coeff j *
          cameraBracketIncidence base radius (index j)
            (alignedCenter base (index i))) = 0 := by
    simpa using congrArg
      (fun v : ℕ →₀ ℝ => v (alignedCenter base (index i))) hsum
  simp_rw [hdiag] at heval
  simp at heval
  linarith

/-- Even parity center indices are injective. -/
theorem evenParityCameraIndex_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => 2 * (i : ℕ)) := by
  intro i j hij
  have hij' : 2 * (i : ℕ) = 2 * (j : ℕ) := by
    simpa using hij
  apply Fin.ext
  omega

/-- Odd parity center indices are injective. -/
theorem oddParityCameraIndex_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => 2 * (i : ℕ) + 1) := by
  intro i j hij
  have hij' : 2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1 := by
    simpa using hij
  apply Fin.ext
  omega

/-- The even finite bracket-incidence prefix is linearly independent. -/
theorem evenCameraBracketIncidence_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N =>
        cameraBracketIncidence base radius (2 * (i : ℕ))) :=
  cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius _ (evenParityCameraIndex_injective N)

/-- The odd finite bracket-incidence prefix is linearly independent. -/
theorem oddCameraBracketIncidence_linearIndependent
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N =>
        cameraBracketIncidence base radius (2 * (i : ℕ) + 1)) :=
  cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius _ (oddParityCameraIndex_injective N)

/-- The complete even bracket-incidence family is linearly independent.  This
is the global form needed by the completed Green-jet carrier, obtained by
checking every finite support with the same unique-center pivot. -/
theorem evenCameraBracketIncidence_linearIndependent_global
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun i : ℕ => cameraBracketIncidence base radius (2 * i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  apply cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius
  intro i j hij
  apply Subtype.ext
  dsimp only at hij
  omega

/-- The complete odd bracket-incidence family is linearly independent. -/
theorem oddCameraBracketIncidence_linearIndependent_global
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun i : ℕ => cameraBracketIncidence base radius (2 * i + 1)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  apply cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius
  intro i j hij
  apply Subtype.ext
  dsimp only at hij
  omega

end

end CarrySelfAdjointOperator
