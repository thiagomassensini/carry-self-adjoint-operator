import CarrySelfAdjointOperator.CompletedC3CausalGreenGramSewing
import Mathlib.Tactic

/-!
# Exact causal--Gamma energy defect

The completed C3 causal Green construction and the global Gamma/Cauchy
construction already have the same centered spectral factor.  Their remaining
mismatch is therefore a difference of two positive, independently constructed
energies.

This file names that difference and records the exact factorization of every
remaining scalar readout through it.  No positivity, zero, confinement,
scalarization, or new carrier hypothesis is introduced.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The canonical pointwise mismatch between the channel-complete causal
adjoint-square energy and the Gamma resolvent energy built from the same
completed C3 source. -/
def canonicalCompletedC3CausalGammaEnergyDefect
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : s ∈ genuineCriticalStrip) : ℝ :=
  canonicalCompletedC3CausalAdjointSquareRadialEnergy hbase s hs -
    canonicalCompletedC3GammaEnergy (centeredHeightParameter s)

/-- The defect is independent of which supported base is used to present the
causal response/boundary carrier. -/
theorem canonicalCompletedC3CausalGammaEnergyDefect_base_independent
    {base₁ base₂ : ℕ}
    (hbase₁ : FiniteNativeCarryOperator.Camera.IsSupported base₁)
    (hbase₂ : FiniteNativeCarryOperator.Camera.IsSupported base₂)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3CausalGammaEnergyDefect hbase₁ s hs =
      canonicalCompletedC3CausalGammaEnergyDefect hbase₂ s hs := by
  unfold canonicalCompletedC3CausalGammaEnergyDefect
  rw [canonicalCompletedC3CausalAdjointSquareRadialEnergy_base_independent
    hbase₁ hbase₂ hs]

/-- The entire scalar mismatch is the centered spectral skew multiplied by
one real energy defect.  All phase, chart, reflection, radial-cofactor, and
Cauchy normalizations have already been discharged by the existing bridges. -/
theorem
    canonicalCompletedC3NormalizedGreenLimitTrace_sub_globalBoundary_eq_centeredFactor_mul_energyDefect
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    let z := centeredHeightParameter s
    let hz : z.im ≠ 0 :=
      centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
    canonicalCompletedC3NormalizedGreenLimitTrace s -
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz =
      (z - (starRingEnd ℂ) z) *
        (canonicalCompletedC3CausalGammaEnergyDefect hbase s hs : ℂ) := by
  dsimp only
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_causalSpectralForm
      hbase hs,
    canonicalCompletedC3GlobalBoundaryGreenTrace_eq_energy]
  unfold canonicalCompletedC3CausalGammaEnergyDefect
  push_cast
  ring

/-- At one off-critical strip point, vanishing of the energy defect is exactly
pointwise equality of the normalized C3 Green limit and the Gamma/Cauchy
boundary readout. -/
theorem
    canonicalCompletedC3CausalGammaEnergyDefect_eq_zero_iff_globalBoundary
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3CausalGammaEnergyDefect hbase s hs = 0 ↔
      let z := centeredHeightParameter s
      let hz : z.im ≠ 0 :=
        centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
      canonicalCompletedC3NormalizedGreenLimitTrace s =
        canonicalCompletedC3GlobalBoundaryGreenTrace z hz := by
  dsimp only
  have hiff :=
    canonicalCompletedC3NormalizedGreenLimitTrace_eq_globalBoundary_iff_causalEnergy
      hbase hs hoff
  constructor
  · intro hzero
    apply hiff.mpr
    unfold canonicalCompletedC3CausalGammaEnergyDefect at hzero
    exact sub_eq_zero.mp hzero
  · intro hreadout
    unfold canonicalCompletedC3CausalGammaEnergyDefect
    exact sub_eq_zero.mpr (hiff.mp hreadout)

/-- Global Green-readout intertwining is precisely the assertion that the
single causal--Gamma energy defect vanishes at every off-critical point. -/
theorem canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_energyDefect_zero
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    CanonicalCompletedC3GlobalGreenReadoutIntertwining ↔
      ∀ {s : ℂ}, ∀ hs : s ∈ genuineCriticalStrip,
        ∀ _hoff : s.re ≠ (1 : ℝ) / 2,
          canonicalCompletedC3CausalGammaEnergyDefect hbase s hs = 0 := by
  rw [canonicalCompletedC3GlobalGreenReadoutIntertwining_iff_causalEnergy hbase]
  constructor
  · intro henergy s hs hoff
    unfold canonicalCompletedC3CausalGammaEnergyDefect
    exact sub_eq_zero.mpr (henergy hs hoff)
  · intro hdefect s hs hoff
    have hzero := hdefect hs hoff
    unfold canonicalCompletedC3CausalGammaEnergyDefect at hzero
    exact sub_eq_zero.mp hzero

end

end CarrySelfAdjointOperator
