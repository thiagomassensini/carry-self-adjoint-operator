import CarrySelfAdjointOperator.PrimeDepthNormalizedResponseVectorJet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Polynomial pencil from the original four-sector vector jets

The source vector `primeDepthNormalizedResponseVectorJet n` already exists.
Its fixed readout is established without using `primeDepthGeometricMoment_eq_canonical`.
Here the matrix and determinant are defined from this source readout first.
The geometric and canonical moment equalities are postponed to separate theorems.

This produces an exact finite polynomial pencil, not a positive Gram matrix,
a self-adjoint height operator, an all-order real-rootedness certificate, or RH.

STATUS: source-level proof candidate; local Lean toolchain unavailable.
This file was not kernel-checked and must be compiled before merging.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Existing four-channel vector source, read through its fixed linear map.
This definition does not mention the canonical scalar moment sequence. -/
def sourceVectorJetReadout (n : ℕ) : ℂ :=
  primeDepthNormalizedResponseVectorReadout
    (primeDepthNormalizedResponseVectorJet n)

/-- A polynomial pencil with coefficients obtained from source vector jets. -/
def sourceVectorJetPencil (N : ℕ) (t : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    t * sourceVectorJetReadout (i.val + j.val + 1) -
        sourceVectorJetReadout (i.val + j.val)

def sourceVectorJetPencilDet (N : ℕ) (t : ℂ) : ℂ :=
  (sourceVectorJetPencil N t).det

/-- Target built from the geometric moments; still no canonical comparison. -/
def sourceGeometricPencil (N : ℕ) (t : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    t * (primeDepthGeometricMoment (i.val + j.val + 1) : ℂ) -
        (primeDepthGeometricMoment (i.val + j.val) : ℂ)

/-- Source-first all-order readout, from the existing vector-jet theorem. -/
theorem sourceVectorJetReadout_eq_geometric (n : ℕ) :
    sourceVectorJetReadout n = (primeDepthGeometricMoment n : ℂ) := by
  exact primeDepthNormalizedResponseVectorJet_readout n

/-- EXACT at each finite N, without requiring positivity or a limit in k. -/
theorem sourceVectorJetPencil_eq_geometric (N : ℕ) (t : ℂ) :
    sourceVectorJetPencil N t = sourceGeometricPencil N t := by
  ext i j
  simp only [sourceVectorJetPencil, sourceGeometricPencil,
    sourceVectorJetReadout_eq_geometric]

/-- The source polynomial is exactly the geometric-moment pencil. -/
theorem sourceVectorJetPencilDet_eq_geometric (N : ℕ) (t : ℂ) :
    sourceVectorJetPencilDet N t = (sourceGeometricPencil N t).det := by
  exact congrArg Matrix.det (sourceVectorJetPencil_eq_geometric N t)

/-- ONLY at this last stage do we identify the source with canonical moments. -/
theorem sourceVectorJetPencil_entry_eq_canonical
    (N : ℕ) (t : ℂ) (i j : Fin N) :
    sourceVectorJetPencil N t i j =
      t * (canonicalCompletedNativeLogDerivativeMoment (i.val + j.val + 1) : ℂ) -
          (canonicalCompletedNativeLogDerivativeMoment (i.val + j.val) : ℂ) := by
  rw [sourceVectorJetPencil_eq_geometric]
  simp only [sourceGeometricPencil, primeDepthGeometricMoment_eq_canonical]

/-!
## Axiom audit

The following theorems depend on these axioms:
- `sourceVectorJetReadout_eq_geometric`: depends on the axiom footprint of
  `primeDepthNormalizedResponseVectorJet_readout` (the existing vector-jet theorem).
- `sourceVectorJetPencil_eq_geometric`: depends only on `sourceVectorJetReadout_eq_geometric`
  and linear algebra simp lemmas (no classical choice beyond what is already used).
- `sourceVectorJetPencilDet_eq_geometric`: depends only on `Matrix.det` and
  `sourceVectorJetPencil_eq_geometric` (no additional axioms).
- `sourceVectorJetPencil_entry_eq_canonical`: additionally depends on
  `primeDepthGeometricMoment_eq_canonical` (the canonical identification theorem).
-/

-- Axiom audit for the source-first theorems (before canonical identification):
#print axioms CarrySelfAdjointOperator.sourceVectorJetReadout_eq_geometric
#print axioms CarrySelfAdjointOperator.sourceVectorJetPencil_eq_geometric
#print axioms CarrySelfAdjointOperator.sourceVectorJetPencilDet_eq_geometric

-- Axiom audit for the canonical identification theorem:
#print axioms CarrySelfAdjointOperator.sourceVectorJetPencil_entry_eq_canonical

-- Regression tests for dimensions N = 0, 1, 2
-- N = 0: the determinant of a 0×0 matrix is 1
theorem sourceVectorJetPencilDet_zero :
    sourceVectorJetPencilDet 0 t = 1 := by
  dsimp [sourceVectorJetPencilDet]
  simp [Matrix.det_fin_zero]

-- N = 1: the pencil is a 1×1 matrix, so the determinant is the single entry
theorem sourceVectorJetPencilDet_one :
    sourceVectorJetPencilDet 1 t =
      t * sourceVectorJetReadout 1 - sourceVectorJetReadout 0 := by
  dsimp [sourceVectorJetPencilDet]
  rw [Matrix.det_fin_one]
  unfold sourceVectorJetPencil
  simp

-- N = 2: the pencil is a 2×2 matrix
theorem sourceVectorJetPencilDet_two :
    sourceVectorJetPencilDet 2 t =
      (t * sourceVectorJetReadout 1 - sourceVectorJetReadout 0) *
        (t * sourceVectorJetReadout 3 - sourceVectorJetReadout 2) -
      (t * sourceVectorJetReadout 2 - sourceVectorJetReadout 1) *
        (t * sourceVectorJetReadout 2 - sourceVectorJetReadout 1) := by
  dsimp [sourceVectorJetPencilDet]
  rw [Matrix.det_fin_two]
  unfold sourceVectorJetPencil
  simp

end
end CarrySelfAdjointOperator
