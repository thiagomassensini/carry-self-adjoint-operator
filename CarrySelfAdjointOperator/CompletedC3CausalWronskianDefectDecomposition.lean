import CarrySelfAdjointOperator.CompletedC3CausalGammaEnergyDefect
import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import Mathlib.Tactic

/-!
# Canonical decomposition of the C3 Green--Wronskian defect

The normalized causal Green limit, the canonical Gamma/Cauchy boundary, and
the completed `(F,-F')` Wronskian are three independently constructed scalar
readouts.  The first two already differ by the causal--Gamma energy defect;
the last two already differ by the raw Gamma--Wronskian defect.

This file records the exact telescoping decomposition.  It introduces no new
positivity, zero, confinement, or sewing hypothesis.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The global Cauchy boundary trace is exactly the diagonal polarized Gamma
boundary readout.  The two objects occur in different parts of the development
but are the same canonical Cauchy skew with the same `-2 i` orientation. -/
theorem canonicalCompletedC3GlobalBoundaryGreenTrace_eq_polarizedGammaBoundaryReadout
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3GlobalBoundaryGreenTrace z hz =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z z hz hz := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_eq_cauchySkew]
  unfold canonicalCompletedC3GlobalBoundaryGreenTrace
  rw [canonicalCompletedC3GlobalCauchyBoundarySkew_eq_gammaCauchySkew]

/-- Pointwise final defect written as the sum of its two canonical seams:
causal Green versus Gamma energy, and Gamma boundary versus completed
Wronskian. -/
def canonicalCompletedC3CausalWronskianDefect
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) : ℂ :=
  let z := centeredHeightParameter s
  let hz : z.im ≠ 0 := centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  (z - (starRingEnd ℂ) z) *
      (canonicalCompletedC3CausalGammaEnergyDefect hbase s hs : ℂ) +
    canonicalCompletedC3RawGammaWronskianDefect z z hz hz

/-- Exact decomposition of the remaining scalar Green--Wronskian mismatch.
Every normalization and spectral factor is explicit: the first summand is the
causal/Gamma energy mismatch and the second is the already isolated raw
Gamma/Wronskian defect. -/
theorem canonicalCompletedC3NormalizedGreenLimit_sub_wronskian_eq_causalWronskianDefect
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    let z := centeredHeightParameter s
    canonicalCompletedC3NormalizedGreenLimitTrace s -
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z =
      canonicalCompletedC3CausalWronskianDefect hbase s hs hoff := by
  dsimp only [canonicalCompletedC3CausalWronskianDefect]
  let z := centeredHeightParameter s
  let hz : z.im ≠ 0 := centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hcausal :=
    canonicalCompletedC3NormalizedGreenLimitTrace_sub_globalBoundary_eq_centeredFactor_mul_energyDefect
      hbase hs hoff
  have hgamma :=
    canonicalCompletedC3GlobalBoundaryGreenTrace_eq_polarizedGammaBoundaryReadout
      z hz
  unfold canonicalCompletedC3RawGammaWronskianDefect
  dsimp only at hcausal
  rw [hgamma] at hcausal
  linear_combination hcausal

/-- At an off-critical strip point, the desired Green--Wronskian sewing is
exactly vanishing of the single canonical total defect. -/
theorem canonicalCompletedC3NormalizedGreenLimit_eq_wronskian_iff_causalWronskianDefect_eq_zero
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    let z := centeredHeightParameter s
    canonicalCompletedC3NormalizedGreenLimitTrace s =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3CausalWronskianDefect hbase s hs hoff = 0 := by
  dsimp only
  rw [← sub_eq_zero,
    canonicalCompletedC3NormalizedGreenLimit_sub_wronskian_eq_causalWronskianDefect
      hbase hs hoff]

end

end CarrySelfAdjointOperator
