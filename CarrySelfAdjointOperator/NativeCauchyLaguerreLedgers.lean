import CarrySelfAdjointOperator.NativeCauchyLaguerreSources

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped InnerProductSpace lp
open GammaMaterialSewing PhysicalSewing ChiralReturn CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

theorem physicalFiniteSynthesis_inner (N : ℕ) (v w : Fin N → ℂ) :
    inner ℂ (physicalFiniteSynthesis N v) (physicalFiniteSynthesis N w) =
      matrixPairing (cauchyMatrix N) v w := by
  change inner ℂ (physicalFiniteSynthesis N v : CanonicalCompletedNativeChiralCauchyCarrier)
    (physicalFiniteSynthesis N w : CanonicalCompletedNativeChiralCauchyCarrier) = _
  rw [physicalFiniteSynthesis_coe, physicalFiniteSynthesis_coe, incident_inner_eq_matrixPairing]
  simp

def laguerreFinitePair (N : ℕ) (v w : Fin N → ℂ) : ℂ :=
  inner ℂ (cauchyLaguerreIsometry (physicalFiniteSynthesis N v))
    (cauchyLaguerreIsometry (physicalFiniteSynthesis N w))

theorem laguerreFinitePair_eq_original (N : ℕ) (v w : Fin N → ℂ) :
    laguerreFinitePair N v w = matrixPairing (cauchyMatrix N) v w := by
  rw [laguerreFinitePair, cauchyLaguerreIsometry.inner_map_map, physicalFiniteSynthesis_inner]

def laguerreFiniteHeadTailPair (N R : ℕ) (v w : Fin N → ℂ) : ℂ :=
  inner ℂ (laguerreHead R (cauchyLaguerreIsometry (physicalFiniteSynthesis N v)))
    (laguerreHead R (cauchyLaguerreIsometry (physicalFiniteSynthesis N w))) +
  inner ℂ (physicalCauchyShift (R+1) (physicalFiniteSynthesis N v))
    (physicalCauchyShift (R+1) (physicalFiniteSynthesis N w))

theorem laguerreFiniteHeadTailPair_eq_original (N R : ℕ) (v w : Fin N → ℂ) :
    laguerreFiniteHeadTailPair N R v w = matrixPairing (cauchyMatrix N) v w := by
  rw [laguerreFiniteHeadTailPair, ← physicalCauchy_head_tail_inner, physicalFiniteSynthesis_inner]

theorem laguerreFiniteHeadTailPair_eq_old_ledger (N R : ℕ) (v w : Fin N → ℂ) :
    laguerreFiniteHeadTailPair N R v w = gammaPhysicalPairHeadTail N R v w := by
  rw [laguerreFiniteHeadTailPair_eq_original, gammaPhysicalPair_headTail]

/-- The old reference defect after transporting BOTH Cauchy products. -/
def laguerreMaterialReferenceDefect (C k R : ℕ) (z w : ℂ) : ℂ :=
  laguerreFiniteHeadTailPair (materialCameraWindow C) R (nativeGammaMaterialFirstPort C z)
    (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C w j) -
  laguerreFiniteHeadTailPair (materialCameraWindow C) R
    (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j)
    (nativeGammaMaterialFirstPort C w) - canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

theorem laguerreMaterialReferenceDefect_eq_original (C k R : ℕ) (z w : ℂ) :
    laguerreMaterialReferenceDefect C k R z w = nativeGammaReferenceDefect C k z w := by
  unfold laguerreMaterialReferenceDefect nativeGammaReferenceDefect
  rw [laguerreFiniteHeadTailPair_eq_original, laguerreFiniteHeadTailPair_eq_original,
    gammaPhysicalGreenScale_form]

/-- Literal existing ledger: metric mismatch, reference defect, and both mixed physical tails. -/
def laguerreMaterialLedger (C k R : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  -nativeGammaMetricDefect C z w hz hw - laguerreMaterialReferenceDefect C k R z w -
    laguerreFiniteHeadTailPair (materialCameraWindow C) R (nativeGammaMaterialFirstPort C z)
      (nativeGammaMaterialGraphDefect C k w hw) +
    laguerreFiniteHeadTailPair (materialCameraWindow C) R (nativeGammaMaterialGraphDefect C k z hz)
      (nativeGammaMaterialFirstPort C w) - 2 * canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

theorem laguerreMaterialLedger_eq_original (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    laguerreMaterialLedger C k R z w hz hw = nativeGammaMaterialLedgerTotal C k z w hz hw := by
  unfold laguerreMaterialLedger nativeGammaMaterialLedgerTotal
  rw [laguerreMaterialReferenceDefect_eq_original, laguerreFiniteHeadTailPair_eq_original,
    laguerreFiniteHeadTailPair_eq_original]

theorem laguerreMaterialLedger_eq_mismatch (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    laguerreMaterialLedger C k R z w hz hw =
      canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw := by
  rw [laguerreMaterialLedger_eq_original, nativeGammaMaterialLedgerTotal_eq_mismatch]

/-- An internal isometry does not remove the REFUTED Gamma/native metric mismatch. -/
theorem laguerreMaterialLedger_counterexampleFamily :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ ∀ t : ℝ, 0 < t → t < ε →
      ∃ (hz : (Complex.I * (t : ℂ)).im ≠ 0) (hw : (-Complex.I * (t : ℂ)).im ≠ 0),
        operatorHeightParameter (Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        operatorHeightParameter (-Complex.I * (t : ℂ)) ∈ genuineCriticalStrip ∧
        canonicalCompletedC3NativeSourceLocusProjectionMismatch
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 ∧
        ∀ C k R : ℕ, laguerreMaterialLedger C k R
          (Complex.I * (t : ℂ)) (-Complex.I * (t : ℂ)) hz hw ≠ 0 := by
  obtain ⟨ε, hε, hhalf, hf⟩ := nativeGammaCollision_materialCounterexampleFamily
  refine ⟨ε, hε, hhalf, ?_⟩
  intro t ht hte
  obtain ⟨hz, hw, hs, hws, hne, _⟩ := hf t ht hte
  refine ⟨hz, hw, hs, hws, hne, ?_⟩
  intro C k R
  rw [laguerreMaterialLedger_eq_mismatch]
  exact hne

/-- The original native orientation retains both exterior sectors and the named metric defect. -/
theorem laguerreNativeOrientation_materialLedger (C R : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    inner ℂ p.2 t.1 - inner ℂ p.1 t.2 =
      laguerreFiniteHeadTailPair (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.2))
        (materialCameraLift C (nativeSixCameraCoordinates t.1)) -
      laguerreFiniteHeadTailPair (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.1))
        (materialCameraLift C (nativeSixCameraCoordinates t.2)) -
      gammaMaterialMetricFormDefect C p t +
      (inner ℂ (nativeSixCameraExterior p.2) (nativeSixCameraExterior t.1) -
        inner ℂ (nativeSixCameraExterior p.1) (nativeSixCameraExterior t.2)) := by
  rw [laguerreFiniteHeadTailPair_eq_old_ledger, laguerreFiniteHeadTailPair_eq_old_ledger]
  exact nativeGammaNativeOrientation_materialHeadTailLedger C R p t

end
end CarrySelfAdjointOperator.NativeLaguerre
