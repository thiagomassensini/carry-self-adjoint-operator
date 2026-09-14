import CarrySelfAdjointOperator.CompletedNativeSameEdgeGreenClockTransport
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-!
# Atomic form of the seeded-clock boundary gate

The material-clock shift is already exact.  This file exposes the remaining
first-column calibration before any Hankel or Jacobi construction: the atlas
coefficient is a finite atomic moment sum over reconstructed nodal values and
the four real clock frequencies of each block.
-/

/-- The seeded clock atlas coefficient is literally a finite atomic moment
sum.  This is a pre-Hankel identity; no positivity or moment identification
is assumed. -/
theorem seededClockAtlasCoefficient_eq_finiteAtomicMoment
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (p q : ℕ) :
    seededClockAtlasCoefficient block p q =
      ∑ b : ι, ∑ r : Fin 4,
        (starRingEnd ℂ) (seededRecover (block b).state r) *
          seededRecover (block b).state r *
          (((![ (block b).d, (block b).a, (block b).b, (block b).c] r : ℝ) : ℂ) ^
            (p + q)) := by
  unfold seededClockAtlasCoefficient seededClockMaterialCoefficient
    seededClockMaterialRawJet
  apply Finset.sum_congr rfl
  intro b hb
  exact inner_seededRecover_clock_iterate
    (block b).d (block b).a (block b).b (block b).c
    (block b).state (block b).state p q

/-- The central entry of the clock boundary transport is exactly the
zeroth completed-native moment.  This is the mass calibration test for any
candidate atlas. -/
theorem seededClockAtlasCoefficient_zero_zero_eq_nativeMoment_zero_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa using
    (htransport 0).trans
      (canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment
        M 0)

/-- The raw native block at material index zero fails the central calibration
already at the zeroth entry.  This is a no-go for the naive one-block atlas,
not for a future centered or defect-complemented carrier. -/
def nativeZeroSeededClockBlock (s : ℂ) : SeededClockBlock where
  d := Real.log (1 : ℕ)
  a := Real.log (2 : ℕ)
  b := Real.log (3 : ℕ)
  c := Real.log (4 : ℕ)
  state := nativeBlockSeededData 0 s

theorem nativeZeroSeededClockBlock_zero_zero_eq_energy (s : ℂ) :
    seededClockAtlasCoefficient
        (fun _ : Fin 1 => nativeZeroSeededClockBlock s) 0 0 =
      (↑(‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2) : ℂ) := by
  simp [seededClockAtlasCoefficient, seededClockMaterialCoefficient,
    seededClockMaterialRawJet, nativeZeroSeededClockBlock,
    inner_self_eq_norm_sq_to_K]

theorem nativeZeroSeededClockBlock_not_sameEdgeTransport
    (M : ℕ) (s : ℂ) :
    ¬ HasSameEdgeGreenToClockBoundaryTransport M
        (fun _ : Fin 1 => nativeZeroSeededClockBlock s) := by
  intro htransport
  have hmass :=
    seededClockAtlasCoefficient_zero_zero_eq_nativeMoment_zero_of_sameEdgeTransport
      M (fun _ : Fin 1 => nativeZeroSeededClockBlock s) htransport
  have henergy := nativeZeroSeededClockBlock_zero_zero_eq_energy s
  have hcomplex :
      (↑(‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2) : ℂ) =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    rw [← henergy, hmass]
  exact nativeBlockSeededData_zero_energy_ne_nativeMoment s
    (Complex.ofReal_injective hcomplex)

end

end CarrySelfAdjointOperator
