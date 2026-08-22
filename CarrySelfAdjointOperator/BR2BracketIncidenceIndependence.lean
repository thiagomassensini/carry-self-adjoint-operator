import CarrySelfAdjointOperator.BracketLegLatticeSeparation
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# BR2 bracket-incidence independence

The center--leg lattice separation supplies a pivot for every centered
bracket. At its aligned center the incidence vector has coefficient `-2`;
all bracket legs, including those of every other bracket, lie off the center
lattice. Distinct centers are distinct because the exact camera slope is
positive.

Evaluation at the center owned by one bracket therefore recovers exactly its
coefficient in any finite linear combination. Every injectively indexed
finite family of bracket incidences is linearly independent, uniformly for
all supported cameras, prime or composite.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The exact camera slope is positive for every supported camera. -/
theorem br2CameraSlope_pos
    {camera : ℕ} (hcamera : 2 ≤ camera) :
    0 < cameraSlope camera := by
  by_cases h2 : camera = 2
  · subst camera
    simp
  · rw [cameraSlope_of_ne_two h2]
    omega

/-- Aligned centers are injectively indexed. -/
theorem br2AlignedCenter_injective
    {camera : ℕ} (hcamera : 2 ≤ camera) :
    Function.Injective (alignedCenter camera) := by
  intro i j hij
  rw [alignedCenter_eq_cameraSlope_mul,
    alignedCenter_eq_cameraSlope_mul] at hij
  have hsucc : i + 1 = j + 1 :=
    Nat.mul_left_cancel (br2CameraSlope_pos hcamera) hij
  omega

/-- Real incidence vector of one centered bracket. -/
def br2CameraBracketIncidence
    (camera radius index : ℕ) : ℕ →₀ ℝ :=
  Finsupp.single (alignedCenter camera index - radius) 1 +
    Finsupp.single (alignedCenter camera index) (-2) +
      Finsupp.single (alignedCenter camera index + radius) 1

/-- Evaluation on the aligned-center lattice is diagonal. -/
@[simp] theorem br2CameraBracketIncidence_apply_alignedCenter
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (i j : ℕ) :
    br2CameraBracketIncidence camera radius i (alignedCenter camera j) =
      if i = j then (-2 : ℝ) else 0 := by
  classical
  have hlegs :=
    bracketLegs_ne_any_alignedCenter
      (camera := camera) (index := i) (radius := radius)
      (otherIndex := j) hcamera hradius
  have hleft :
      alignedCenter camera i - radius ≠ alignedCenter camera j := hlegs.1
  have hright :
      alignedCenter camera i + radius ≠ alignedCenter camera j := hlegs.2
  by_cases hij : i = j
  · subst j
    simp [br2CameraBracketIncidence, hleft, hright]
  · have hcenter : alignedCenter camera i ≠ alignedCenter camera j :=
      fun h => hij (br2AlignedCenter_injective hcamera h)
    simp [br2CameraBracketIncidence, hleft, hright, hcenter, hij]

/-- Every injectively indexed finite family of bracket incidences is linearly
independent. -/
theorem br2CameraBracketIncidence_linearIndependent_of_injective
    {ι : Type*} [Fintype ι]
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (index : ι → ℕ) (hindex : Function.Injective index) :
    LinearIndependent ℝ
      (fun i : ι => br2CameraBracketIncidence camera radius (index i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  have hdiag : ∀ j : ι,
      br2CameraBracketIncidence camera radius (index j)
          (alignedCenter camera (index i)) =
        if j = i then (-2 : ℝ) else 0 := by
    intro j
    rw [br2CameraBracketIncidence_apply_alignedCenter hcamera hradius]
    by_cases hji : j = i
    · simp [hji]
    · have hne : index j ≠ index i := fun h => hji (hindex h)
      simp [hji, hne]
  have heval :
      (∑ j : ι,
        coeff j *
          br2CameraBracketIncidence camera radius (index j)
            (alignedCenter camera (index i))) = 0 := by
    simpa using congrArg
      (fun v : ℕ →₀ ℝ => v (alignedCenter camera (index i))) hsum
  simp_rw [hdiag] at heval
  simp at heval
  linarith

/-- Even parity indices are injective. -/
theorem br2EvenParityIndex_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => 2 * (i : ℕ)) := by
  intro i j hij
  have hij' : 2 * (i : ℕ) = 2 * (j : ℕ) := by
    simpa using hij
  apply Fin.ext
  omega

/-- Odd parity indices are injective. -/
theorem br2OddParityIndex_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => 2 * (i : ℕ) + 1) := by
  intro i j hij
  have hij' : 2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1 := by
    simpa using hij
  apply Fin.ext
  omega

/-- Even bracket-incidence prefixes are linearly independent. -/
theorem br2EvenCameraBracketIncidence_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N =>
        br2CameraBracketIncidence camera radius (2 * (i : ℕ))) :=
  br2CameraBracketIncidence_linearIndependent_of_injective
    hcamera hradius _ (br2EvenParityIndex_injective N)

/-- Odd bracket-incidence prefixes are linearly independent. -/
theorem br2OddCameraBracketIncidence_linearIndependent
    {camera radius : ℕ}
    (hcamera : 2 ≤ camera)
    (hradius : radius ∈ radiusSet camera)
    (N : ℕ) :
    LinearIndependent ℝ
      (fun i : Fin N =>
        br2CameraBracketIncidence camera radius (2 * (i : ℕ) + 1)) :=
  br2CameraBracketIncidence_linearIndependent_of_injective
    hcamera hradius _ (br2OddParityIndex_injective N)

end

end CarrySelfAdjointOperator
