import CarrySelfAdjointOperator.CompletedNativeSeededClockTfvdSixSource
import CarrySelfAdjointOperator.CompletedNativeSeededClockAtomicGate

/-!
# No-go for the uncorrected native seeded-clock atlas

The material enriched TFVD boundary observation reaches the corrected chiral
first column.  This file decides the remaining comparison for the canonical
uncentered positive atlas consisting of the first `M + 1` native seeded
blocks.  Its central Gram entry is a sum of nonnegative nodal energies and
already contains the unit seed of block zero.  It therefore cannot equal the
corrected enriched boundary jet at index zero.

This is a no-go only for this literal positive atlas.  It does not exclude a
centered, signed, Green-corrected, or defect-complemented material carrier.
-/

open scoped ComplexConjugate InnerProductSpace BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-- The canonical uncentered native material atlas: the complete blocks
`0, ..., M`, all carrying the same native parameter `s`. -/
def nativeC3SeededClockMaterialAtlas (M : ℕ) (s : ℂ) :
    Fin (M + 1) → SeededClockBlock :=
  fun m => nativeC3SeededClockMaterialBlock (m : ℕ) s

/-- The central raw first-column entry of the literal native atlas is exactly
the sum of its reconstructed nodal energies. -/
theorem nativeC3SeededClockMaterialAtlas_zero_zero_eq_energySum
    (M : ℕ) (s : ℂ) :
    seededClockAtlasCoefficient (nativeC3SeededClockMaterialAtlas M s) 0 0 =
      ∑ m : Fin (M + 1),
        (↑(‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2) : ℂ) := by
  simp [nativeC3SeededClockMaterialAtlas, seededClockAtlasCoefficient,
    seededClockMaterialCoefficient, seededClockMaterialRawJet,
    nativeC3SeededClockMaterialBlock, inner_self_eq_norm_sq_to_K]

/-- The energy sum contains block zero and is therefore at least one. -/
theorem one_le_nativeC3SeededClockMaterialAtlas_energySum
    (M : ℕ) (s : ℂ) :
    (1 : ℝ) ≤ ∑ m : Fin (M + 1),
      ‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2 := by
  let m0 : Fin (M + 1) := ⟨0, Nat.succ_pos M⟩
  have hnonneg : ∀ m : Fin (M + 1),
      0 ≤ ‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2 := by
    intro m
    exact sq_nonneg _
  calc
    (1 : ℝ) ≤ ‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2 :=
      nativeBlockSeededData_zero_energy_ge_one s
    _ = ‖seededRecover (nativeBlockSeededData (m0 : ℕ) s)‖ ^ 2 := by
      rfl
    _ ≤ ∑ m : Fin (M + 1),
        ‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2 := by
      exact Finset.single_le_sum (fun m hm => hnonneg m) (Finset.mem_univ m0)

/-- The raw central energy sum cannot equal the zeroth completed-native
moment.  The moment appears only in this final calibration contradiction. -/
theorem nativeC3SeededClockMaterialAtlas_energySum_ne_canonicalMoment_zero
    (M : ℕ) (s : ℂ) :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) ≠
      ∑ m : Fin (M + 1),
        ‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2 := by
  intro h
  have hsum := one_le_nativeC3SeededClockMaterialAtlas_energySum M s
  have hmoment := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- Exact no-go at the last interface: the positive raw central entry of the
canonical native atlas cannot equal the index-zero jet of the enriched TFVD
material observation. -/
theorem nativeC3SeededClockMaterialAtlas_zero_zero_ne_tfvdSixSourceJet_zero
    (M : ℕ) (s : ℂ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    seededClockAtlasCoefficient (nativeC3SeededClockMaterialAtlas M s) 0 0 ≠
      nativeC3SeededClockTfvdSixSourceJetCoefficient M 0 q hqpos.le hq1 S := by
  intro h
  have hraw := nativeC3SeededClockMaterialAtlas_zero_zero_eq_energySum M s
  have hjet := nativeC3SeededClockTfvdSixSourceJet_zero_eq_canonicalMoment
    M q hqpos hq1 S
  have hsumcomplex :
      (∑ m : Fin (M + 1),
        (↑(‖seededRecover (nativeBlockSeededData (m : ℕ) s)‖ ^ 2) : ℂ)) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
    hraw.symm.trans (h.trans hjet)
  norm_cast at hsumcomplex
  exact nativeC3SeededClockMaterialAtlas_energySum_ne_canonicalMoment_zero M s
    hsumcomplex.symm

/-- Consequently the canonical uncentered native positive atlas cannot
satisfy the original same-edge Green-to-clock transport. -/
theorem nativeC3SeededClockMaterialAtlas_not_sameEdgeTransport
    (M : ℕ) (s : ℂ) :
    ¬ HasSameEdgeGreenToClockBoundaryTransport M
        (nativeC3SeededClockMaterialAtlas M s) := by
  intro htransport
  have hraw :
      seededClockAtlasCoefficient (nativeC3SeededClockMaterialAtlas M s) 0 0 =
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M 0 :=
    seededClockAtlasCoefficient_firstColumn_eq_correctedNativeChiralBoundaryCoefficient_of_sameEdgeTransport
      M (nativeC3SeededClockMaterialAtlas M s) 0 htransport
  have hjet := canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_seededClockTfvdSixSourceJet
    M 0 (1 / 2 : ℝ) (by norm_num) (by norm_num) ∅
  exact nativeC3SeededClockMaterialAtlas_zero_zero_ne_tfvdSixSourceJet_zero
    M s (1 / 2 : ℝ) (by norm_num) (by norm_num) ∅
    (hraw.trans hjet)

end

end CarrySelfAdjointOperator
