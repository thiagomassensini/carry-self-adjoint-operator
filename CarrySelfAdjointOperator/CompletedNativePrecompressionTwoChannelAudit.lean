import CPFormal.Analytic.CpTfvdSameEdgeCompletedPrecompressionCollapse

/-!
# Audit of the native completed precompression pair

`primos` already contains an exact two-channel completed precompression
construction.  This module records precisely what it supplies on the
canonical ordinary/log-jet inputs, so that it is not mistaken for the pending
projective/chiral lossless dilation.

The construction retains a genuine Green-energy residual channel, but its
visible first channel is identically zero on these inputs.  It is therefore a
useful provenance/energy completion, not a certified realization whose first
output is the nontrivial chiral multiplier output `Q v`.  No positivity,
Hankel, Stieltjes, or abstract defect factorization occurs here.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The first output of the already-native completed precompression pair is
literally zero on the canonical same-edge ordinary/log-jet inputs. -/
theorem canonicalCompletedPrecompression_visibleChannel_eq_zero
    (M : ℕ) (s : ℂ) :
    (seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s).1 = 0 := by
  rw [seededTfvdGpreCompletedPrecompressionSource_sameEdge]

/-- Its second output is not manufactured from a target moment: it is the
existing first-level Green-energy state. -/
theorem canonicalCompletedPrecompression_residualChannel_eq_greenEnergy
    (M : ℕ) (s : ℂ) :
    (seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s).2 = nativeGpreGreenEnergyFirstLevelState (3 * M) s := by
  rw [seededTfvdGpreCompletedPrecompressionSource_sameEdge]

/-- At every nonempty genuine cutoff this candidate separates a zero visible
slot from a nonzero residual Green state.  Thus, at the exact stage where a
lossless chiral dilation would need a demonstrated main output, this native
two-channel construction has only a residual-energy channel. -/
theorem canonicalCompletedPrecompression_visible_zero_residual_nonzero
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    (seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s).1 = 0 ∧
      (seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s).2 ≠ 0 := by
  constructor
  · exact canonicalCompletedPrecompression_visibleChannel_eq_zero M s
  · rw [canonicalCompletedPrecompression_residualChannel_eq_greenEnergy]
    exact nativeGpreGreenEnergyFirstLevelState_ne_zero (by omega) hs

end

end CarrySelfAdjointOperator
