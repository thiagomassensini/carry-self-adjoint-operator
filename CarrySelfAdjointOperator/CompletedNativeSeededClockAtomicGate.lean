import CarrySelfAdjointOperator.CompletedNativeSameEdgeGreenClockTransport
import CarrySelfAdjointOperator.CompletedNativeCentralChiralEnergyFlow
import CarrySelfAdjointOperator.CompletedNativeChiralBlockMomentProbe
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

/-! The central clock gate can be read directly as the signed chiral
energy flow.  This is the existing Green/chiral polarization, not a new
Gram or a mirrored clock normalization. -/

/-- Under the exact same-edge transport, the central seeded-clock mass is
the first-order variation of the positive chiral energy. -/
theorem seededClockAtlasCoefficient_zero_zero_eq_positiveChiralDerivative_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block 0 0 =
      ((deriv completedNativeCentralPositiveChiralEnergy 0 : ℝ) : ℂ) := by
  calc
    seededClockAtlasCoefficient block 0 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
      seededClockAtlasCoefficient_zero_zero_eq_nativeMoment_zero_of_sameEdgeTransport
        M block htransport
    _ = ((deriv completedNativeCentralPositiveChiralEnergy 0 : ℝ) : ℂ) := by
      rw [deriv_completedNativeCentralPositiveChiralEnergy_zero]

/-- The same central mass is the opposite of the first-order variation of
the negative chiral energy. -/
theorem seededClockAtlasCoefficient_zero_zero_eq_negNegativeChiralDerivative_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block 0 0 =
      ((-deriv completedNativeCentralNegativeChiralEnergy 0 : ℝ) : ℂ) := by
  calc
    seededClockAtlasCoefficient block 0 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
      seededClockAtlasCoefficient_zero_zero_eq_nativeMoment_zero_of_sameEdgeTransport
        M block htransport
    _ = ((-deriv completedNativeCentralNegativeChiralEnergy 0 : ℝ) : ℂ) := by
      simp [deriv_completedNativeCentralNegativeChiralEnergy_zero]

/-! ## All-order first-column chiral readout

The exact boundary transport is now exposed through the existing chiral block
signature.  This is the causal/Green readout of the complete Wronskian; it is
not a new positive carrier or a reconstruction from Hankel/Jacobi data. -/

/-- Every transported clock first-column coefficient is the corresponding
Taylor coefficient of the signed positive-minus-negative chiral readout. -/
theorem seededClockAtlasCoefficient_firstColumn_eq_chiralBlockSignature_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) (p : ℕ)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block p 0 =
      canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (p + 1) := by
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (p + 1) := htransport p
    _ = canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (p + 1) :=
      (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient_eq_response
        M (p + 1)).symm

/-- The same first-column coefficient is the polarized Green moment with
the second index fixed at zero. -/
theorem seededClockAtlasCoefficient_firstColumn_eq_polarizedGreenMoment_of_sameEdgeTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) (p : ℕ)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    seededClockAtlasCoefficient block p 0 =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p 0 := by
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (p + 1) :=
      seededClockAtlasCoefficient_firstColumn_eq_chiralBlockSignature_of_sameEdgeTransport
        M block p htransport
    _ = polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p 0 := by
      simpa using
        (canonicalCompletedC3ChiralBlockSignature_succ_eq_polarizedMoment
          M p 0)

end

end CarrySelfAdjointOperator
