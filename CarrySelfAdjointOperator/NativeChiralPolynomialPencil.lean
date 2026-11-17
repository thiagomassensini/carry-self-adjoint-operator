import CarrySelfAdjointOperator.CompletedNativeProjectiveChiralForwardDifference
import Mathlib.Topology.Algebra.Monoid
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Signed vector-jet pencil: first source-preserving formalization candidate

This module is intentionally limited to a pointwise, fixed-size determinant
limit.  It DOES NOT assert a Hilbert Gram, positivity, self-adjointness,
real/positive roots, spectral convergence as N grows, or RH.

The two finite matrices are defined from the *existing* projective/chiral
vectors before any moment sequence is read out.  The target matrices are the
geometric moments, with canonical identification postponed.

Compiled: kernel-checked via `lake env lean`. All theorems verified.
Axiom footprint: propext, Classical.choice, Quot.sound (inherited from
  projectiveChiralDifferenceJet_even_even_tendsto / odd_odd_tendsto,
  which depend on primeDepthGeometricMoment_eq_canonical).
-/

namespace CarrySelfAdjointOperator

open Filter
open scoped BigOperators

noncomputable section

/-- Even-even channel, built from literal vector differences. -/
def chiralEvenMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => canonicalCompletedNativeProjectiveChiralForm
    (projectiveChiralDifferenceJet k (2 * i.val))
    (projectiveChiralDifferenceJet k (2 * j.val))

/-- Odd-odd channel, built from literal vector differences. -/
def chiralOddMatrix (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => canonicalCompletedNativeProjectiveChiralForm
    (projectiveChiralDifferenceJet k (2 * i.val + 1))
    (projectiveChiralDifferenceJet k (2 * j.val + 1))

/-- Only the *target* of the limit uses a scalar moment readout. -/
def geometricEvenMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (primeDepthGeometricMoment (i.val + j.val) : ℂ)

def geometricOddMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (primeDepthGeometricMoment (i.val + j.val + 1) : ℂ)

theorem chiralEvenMatrix_entry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k : ℕ => chiralEvenMatrix k N i j) atTop
      (nhds (geometricEvenMatrix N i j)) := by
  simpa only [chiralEvenMatrix, geometricEvenMatrix] using
    projectiveChiralDifferenceJet_even_even_tendsto i.val j.val

theorem chiralOddMatrix_entry_tendsto (N : ℕ) (i j : Fin N) :
    Tendsto (fun k : ℕ => chiralOddMatrix k N i j) atTop
      (nhds (geometricOddMatrix N i j)) := by
  simpa only [chiralOddMatrix, geometricOddMatrix] using
    projectiveChiralDifferenceJet_odd_odd_tendsto i.val j.val

/-- This is a signed pencil, NOT a positive Gram pencil. -/
def chiralVectorPencil (k N : ℕ) (t : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => t * chiralOddMatrix k N i j - chiralEvenMatrix k N i j

def geometricMomentPencil (N : ℕ) (t : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => t * geometricOddMatrix N i j - geometricEvenMatrix N i j

def chiralVectorPencilDet (k N : ℕ) (t : ℂ) : ℂ :=
  (chiralVectorPencil k N t).det

def geometricMomentPencilDet (N : ℕ) (t : ℂ) : ℂ :=
  (geometricMomentPencil N t).det

theorem chiralPencil_entry_tendsto (N : ℕ) (t : ℂ) (i j : Fin N) :
    Tendsto (fun k : ℕ => chiralVectorPencil k N t i j) atTop
      (nhds (geometricMomentPencil N t i j)) := by
  have hodd := chiralOddMatrix_entry_tendsto N i j
  have heven := chiralEvenMatrix_entry_tendsto N i j
  simpa only [chiralVectorPencil, geometricMomentPencil] using
    (hodd.const_mul t).sub heven

/-- Finite determinants commute with entrywise limits over the complex field.
Proof deliberately expands the Leibniz sum instead of assuming continuity
of a determinant on an infinite-dimensional matrix space. -/
theorem finiteDet_tendsto_of_entries (N : ℕ)
    (A : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ)
    (hentry : ∀ i j : Fin N,
      Tendsto (fun k : ℕ => A k i j) atTop (nhds (B i j))) :
    Tendsto (fun k : ℕ => (A k).det) atTop (nhds B.det) := by
  have hsum :
      Tendsto
        (fun k : ℕ =>
          ∑ σ : Equiv.Perm (Fin N),
            (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i : Fin N, A k (σ i) i)
        atTop
        (nhds (∑ σ : Equiv.Perm (Fin N),
          (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i : Fin N, B (σ i) i)) := by
    apply tendsto_finsetSum Finset.univ
    intro σ _
    apply Filter.Tendsto.mul tendsto_const_nhds
    apply tendsto_finsetProd Finset.univ
    intro i _
    exact hentry (σ i) i
  simpa only [Matrix.det_apply'] using hsum

/-- The source-preserving chiral pencil has the same finite-size limit
as the geometric Hankel pencil, for every complex evaluation t. -/
theorem chiralVectorPencilDet_tendsto (N : ℕ) (t : ℂ) :
    Tendsto (fun k : ℕ => chiralVectorPencilDet k N t) atTop
      (nhds (geometricMomentPencilDet N t)) := by
  unfold chiralVectorPencilDet geometricMomentPencilDet
  exact finiteDet_tendsto_of_entries N
    (fun k => chiralVectorPencil k N t)
    (geometricMomentPencil N t)
    (chiralPencil_entry_tendsto N t)

/-- Canonical identification is LAST, not part of the finite vector definition. -/
theorem geometricMomentPencil_entry_eq_canonical (N : ℕ) (t : ℂ)
    (i j : Fin N) :
    geometricMomentPencil N t i j =
      t * (canonicalCompletedNativeLogDerivativeMoment (i.val + j.val + 1) : ℂ) -
          (canonicalCompletedNativeLogDerivativeMoment (i.val + j.val) : ℂ) := by
  simp only [geometricMomentPencil, geometricEvenMatrix, geometricOddMatrix,
    primeDepthGeometricMoment_eq_canonical]

/-!
## Axiom audit for the chiral pencil module

The entrywise tendsto theorems depend on `projectiveChiralDifferenceJet_even_even_tendsto`
and `projectiveChiralDifferenceJet_odd_odd_tendsto`, which in turn depend on
`projectiveChiralDifferenceJet_pairing_tendsto_primeDepthCoefficient`, which uses
`primeDepthGeometricMoment_eq_canonical`. This is the known dependency noted in the
README: the chiral route is NOT independent of canonical comparison in its proof
dependencies.

The determinant limit theorem `finiteDet_tendsto_of_entries` depends only on
`Matrix.det_apply'`, `tendsto_finsetSum`, and `tendsto_finsetProd` (algebraic/analytic).

The canonical identification theorem `geometricMomentPencil_entry_eq_canonical` depends
on `primeDepthGeometricMoment_eq_canonical` (the same canonical identification).
-/

#print axioms CarrySelfAdjointOperator.chiralEvenMatrix_entry_tendsto
#print axioms CarrySelfAdjointOperator.chiralOddMatrix_entry_tendsto
#print axioms CarrySelfAdjointOperator.chiralPencil_entry_tendsto
#print axioms CarrySelfAdjointOperator.finiteDet_tendsto_of_entries
#print axioms CarrySelfAdjointOperator.chiralVectorPencilDet_tendsto
#print axioms CarrySelfAdjointOperator.geometricMomentPencil_entry_eq_canonical

end
end CarrySelfAdjointOperator
