import CarrySelfAdjointOperator.CompletedNativeCausalLegChiralBridge
import Mathlib.Tactic

/-!
# Native Dirichlet chiral cross ledger

A single native Dirichlet atom and its logarithmic jet have zero scalar
boundary wedge: multiplication by the real frequency `log n` cannot create a
signed chiral imbalance.  Consequently, for every finite family of native
atoms, the complete chiral boundary is carried entirely by ordered
cross-frequency provenance.

This is an exact finite identity.  It introduces no positivity, zero-set, or
spectral hypothesis and does not discard any ordered pair.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- One native Dirichlet atom has no signed chiral imbalance by itself. -/
@[simp] theorem scalarBoundaryWedge_natDirichletTerm_eq_zero
    (s : ℂ) (n : ℕ) :
    scalarBoundaryWedge
        (natDirichletTerm s n)
        (natLogDirichletTerm s n) = 0 := by
  unfold scalarBoundaryWedge natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Every ordered pair is the frequency difference times the Hermitian
product of its two native atoms. -/
theorem scalarBoundaryPairCell_natDirichletTerm
    (s : ℂ) (i j : ℕ) :
    scalarBoundaryPairCell
        (fun n : ℕ => natDirichletTerm s n)
        (fun n : ℕ => natLogDirichletTerm s n) i j =
      (((Real.log (j : ℝ) - Real.log (i : ℝ) : ℝ) : ℂ) *
        (starRingEnd ℂ) (natDirichletTerm s i) *
        natDirichletTerm s j) := by
  unfold scalarBoundaryPairCell natLogDirichletTerm
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- In a finite native family all diagonal wedges vanish, so the synthesized
boundary is exactly its cross-frequency provenance. -/
theorem scalarBoundaryWedge_sum_natDirichletTerm_eq_crossProvenance
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    scalarBoundaryWedge
        (∑ i : ι, natDirichletTerm s (index i))
        (∑ i : ι, natLogDirichletTerm s (index i)) =
      scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) := by
  rw [scalarBoundaryWedge_sum_eq_local_add_crossProvenance]
  simp

/-- Fully expanded ordered-pair formula for the native cross provenance. -/
theorem scalarBoundaryCrossProvenance_natDirichletTerm_eq_pairwise
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) =
      ∑ i : ι, ∑ j : ι,
        (((Real.log (index j : ℝ) - Real.log (index i : ℝ) : ℝ) : ℂ) *
          (starRingEnd ℂ) (natDirichletTerm s (index i)) *
          natDirichletTerm s (index j)) := by
  unfold scalarBoundaryCrossProvenance scalarBoundaryPairwiseLedger
  simp only [scalarBoundaryWedge_natDirichletTerm_eq_zero,
    Finset.sum_const_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact scalarBoundaryPairCell_natDirichletTerm s (index i) (index j)

/-- The global scalar chiral difference of a finite native family is therefore
exactly `i` times its explicit cross-frequency ledger. -/
theorem scalarChiralDifference_sum_natDirichletTerm_eq_crossProvenance
    {ι : Type*} [Fintype ι]
    (index : ι → ℕ) (s : ℂ) :
    Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))
            (completedScalarBoundaryPositivePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i)))) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))
            (completedScalarBoundaryNegativePolarization
              (WithLp.toLp 2
                (∑ i : ι, natLogDirichletTerm s (index i),
                  ∑ i : ι, natDirichletTerm s (index i))))) =
      scalarBoundaryCrossProvenance
        (fun i : ι => natDirichletTerm s (index i))
        (fun i : ι => natLogDirichletTerm s (index i)) := by
  rw [← scalarBoundaryWedge_eq_scalarChiralDifference]
  exact scalarBoundaryWedge_sum_natDirichletTerm_eq_crossProvenance index s

end

end CarrySelfAdjointOperator
