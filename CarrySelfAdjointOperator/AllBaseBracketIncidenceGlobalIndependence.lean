import CarrySelfAdjointOperator.AllBaseBracketIncidenceIndependence

/-!
# Independence of the complete all-base bracket families

Every finite subfamily is independent by its distinct aligned-center pivots.
The finite-subfamily criterion extends this to the complete parity families.
-/

namespace CarrySelfAdjointOperator

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The complete even bracket-incidence family is linearly independent. -/
theorem evenCameraBracketIncidence_linearIndependent_global
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ => cameraBracketIncidence base radius (2 * n)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hindex : Function.Injective (fun i : s => 2 * (i : ℕ)) := by
    intro i j hij
    dsimp only at hij
    apply Subtype.ext
    omega
  exact cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius (fun i : s => 2 * (i : ℕ)) hindex

/-- The complete odd bracket-incidence family is linearly independent. -/
theorem oddCameraBracketIncidence_linearIndependent_global
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    LinearIndependent ℝ
      (fun n : ℕ => cameraBracketIncidence base radius (2 * n + 1)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have hindex : Function.Injective (fun i : s => 2 * (i : ℕ) + 1) := by
    intro i j hij
    dsimp only at hij
    apply Subtype.ext
    omega
  exact cameraBracketIncidence_linearIndependent_of_injective
    hbase hradius (fun i : s => 2 * (i : ℕ) + 1) hindex

end

end CarrySelfAdjointOperator
