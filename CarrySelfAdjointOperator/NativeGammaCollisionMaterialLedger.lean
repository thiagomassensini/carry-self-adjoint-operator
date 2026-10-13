import CarrySelfAdjointOperator.NativeGammaConjugateCollisionObstruction
import CarrySelfAdjointOperator.NativeGammaMaterialHeadTailLedger
import CarrySelfAdjointOperator.NativeGammaMixedResolventCapstone

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped ComplexConjugate InnerProductSpace
open PhysicalSewing NativeLaguerre CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- The literal corrected ledger, not a correction fitted to the target. -/
def nativeGammaMaterialLedgerTotal (C k : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  -nativeGammaMetricDefect C z w hz hw - nativeGammaReferenceDefect C k z w -
    matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialFirstPort C z)
      (nativeGammaMaterialGraphDefect C k w hw) +
    matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialGraphDefect C k z hz)
      (nativeGammaMaterialFirstPort C w) -
    2 * canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

/-- The same ledger keeps both mixed physical head/tail products and the graph form. -/
def nativeGammaMaterialHeadTailLedgerTotal (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  -nativeGammaMetricDefect C z w hz hw -
    (gammaPhysicalGreenScale k * twoPortPolarizedHeadTail (materialCameraWindow C) k R
      (nativeGammaMaterialFirstPort C z)
      (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j)
      (nativeGammaMaterialFirstPort C w)
      (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C w j) -
      canonicalCompletedC3NativeSourceLocusScalarGreenForm z w) -
    gammaPhysicalPairHeadTail (materialCameraWindow C) R (nativeGammaMaterialFirstPort C z)
      (nativeGammaMaterialGraphDefect C k w hw) +
    gammaPhysicalPairHeadTail (materialCameraWindow C) R (nativeGammaMaterialGraphDefect C k z hz)
      (nativeGammaMaterialFirstPort C w) - 2 * canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

theorem nativeGammaMaterialLedgerTotal_eq_mismatch (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nativeGammaMaterialLedgerTotal C k z w hz hw =
      canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw :=
  (nativeGammaMismatch_materialDefectLedger C k z w hz hw).symm

theorem nativeGammaMaterialHeadTailLedgerTotal_eq_mismatch (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nativeGammaMaterialHeadTailLedgerTotal C k R z w hz hw =
      canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw :=
  (nativeGammaMismatch_materialHeadTailLedger C k R z w hz hw).symm

theorem nativeGammaCollision_materialLedgers_eq_Wronskian (C k R : ℕ) (t : ℝ)
    (ht : 0 < |t|) (hsmall : |t| < 1/2)
    (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0) :
    nativeGammaMaterialLedgerTotal C k (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw =
      -nativeConjugateWronskian t ∧
    nativeGammaMaterialHeadTailLedgerTotal C k R (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw =
      -nativeConjugateWronskian t := by
  rw [nativeGammaMaterialLedgerTotal_eq_mismatch, nativeGammaMaterialHeadTailLedgerTotal_eq_mismatch,
    nativeSourceLocusMismatch_imaginaryCollision t ht hsmall]
  exact ⟨rfl, rfl⟩

theorem nativeGammaCollision_materialCounterexampleFamily :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ ∀ t : ℝ, 0 < t → t < ε →
      ∃ (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0),
        operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        operatorHeightParameter (-Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        canonicalCompletedC3NativeSourceLocusProjectionMismatch
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 ∧
        ∀ C k R : ℕ,
          nativeGammaMaterialLedgerTotal C k (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 ∧
          nativeGammaMaterialHeadTailLedgerTotal C k R
            (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 := by
  obtain ⟨ε, hε, hhalf, hf⟩ := nativeSourceLocusMismatch_conjugateCounterexampleFamily
  refine ⟨ε, hε, hhalf, ?_⟩
  intro t ht hte
  obtain ⟨hz, hw, hs, hws, hne⟩ := hf t ht hte
  refine ⟨hz, hw, hs, hws, hne, ?_⟩
  intro C k R
  rw [nativeGammaMaterialLedgerTotal_eq_mismatch, nativeGammaMaterialHeadTailLedgerTotal_eq_mismatch]
  exact ⟨hne, hne⟩

/-- The original vector transport still reconstructs both whole pairs at
every counterexample; the obstruction is a readout comparison, not lost data. -/
theorem nativeGammaCollision_transportCounterexampleFamily :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ ∀ t : ℝ, 0 < t → t < ε →
      ∃ (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0),
        canonicalCompletedC3NativeSourceLocusProjectionMismatch
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 ∧
        ∀ C k R : ℕ, 1 ≤ C →
          gammaMaterialReconstruct C k (gammaMaterialTransport C k
            (canonicalCompletedC3GammaBoundaryState (Complex.I * (t : ℂ)) hz)) =
              canonicalCompletedC3GammaBoundaryState (Complex.I * (t : ℂ)) hz ∧
          gammaMaterialReconstruct C k (gammaMaterialTransport C k
            (canonicalCompletedC3GammaBoundaryState (-Complex.I * (t : ℂ)) hw)) =
              canonicalCompletedC3GammaBoundaryState (-Complex.I * (t : ℂ)) hw ∧
          nativeGammaMaterialLedgerTotal C k (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 ∧
          nativeGammaMaterialHeadTailLedgerTotal C k R
            (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 := by
  obtain ⟨ε, hε, hhalf, hf⟩ := nativeGammaCollision_materialCounterexampleFamily
  refine ⟨ε, hε, hhalf, ?_⟩
  intro t ht hte
  obtain ⟨hz, hw, _, _, hne, hledger⟩ := hf t ht hte
  refine ⟨hz, hw, hne, ?_⟩
  intro C k R hC
  exact ⟨canonicalGammaMaterialTransport_reconstruct C k hC _ hz,
    canonicalGammaMaterialTransport_reconstruct C k hC _ hw,
    (hledger C k R).1, (hledger C k R).2⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing
