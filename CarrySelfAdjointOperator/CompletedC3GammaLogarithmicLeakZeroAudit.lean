import CarrySelfAdjointOperator.CompletedC3CompressedGammaGramCorrection
import CarrySelfAdjointOperator.CompletedC3MixedChannelNoCancellation
import Mathlib.Tactic

/-!
# Gamma logarithmic leak on the off-critical zero locus

This module records the exact zero-locus audit for the logarithmic escape
balance.  At a hypothetical off-critical Genuine zero, the scalar Wronskian
and the complete finite scalar ledger vanish, while both the Gamma boundary
and the uncollapsed finite channel state remain nonzero.  The response-level
Pythagorean identity is still exactly the logarithmic leak balance, but the
zero condition does not select either side of that equivalence.
-/

open scoped ComplexConjugate Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Exact audit of the logarithmic leak criterion at a hypothetical
off-critical Genuine zero.  It packages, in the same centered parameter, the
vanishing scalar Wronskian, the nonvanishing Gamma boundary, the exact
Pythagorean criterion, and the eventual scalar-zero/vector-nonzero ledger.

In particular, scalar vanishing is compatible with a nonzero uncollapsed
state; no injectivity of the final scalar readout is implicit here. -/
theorem canonicalCompletedC3OffCriticalGenuineZero_logarithmicLeakAudit
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCompletedC3RawHeightMixedWronskian
          (centeredHeightParameter s) (centeredHeightParameter s) = 0 ∧
      canonicalCompletedC3PolarizedGammaBoundaryReadout
          (centeredHeightParameter s) (centeredHeightParameter s)
          (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
          (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff) ≠ 0 ∧
      (‖canonicalCompletedC3AmbientResponseState
              (centeredHeightParameter s) (by simpa using hs.1)‖ ^ 2 =
            ‖canonicalCompletedC3PolarizedGammaState
              (centeredHeightParameter s)
              (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)‖ ^ 2 +
              ‖canonicalCompletedC3AmbientTfvdResolvedCorrectionState
                (centeredHeightParameter s)
                (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
                (by simpa using hs.1)‖ ^ 2 ↔
        ‖centeredHeightParameter s‖ ^ 2 *
            (inner ℂ
              (canonicalCompletedC3GammaCameraView
                (allBasesCauchyBlock
                  (centeredHeightParameter s)
                  (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
                  (canonicalCompletedC3SixCameraSource
                    (centeredHeightParameter s))))
              (canonicalCompletedC3GammaCameraView
                (completedC3SymplecticCameraState s hs.1 -
                  allBasesCauchyBlock
                    (centeredHeightParameter s)
                    (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)
                    (canonicalCompletedC3SixCameraSource
                      (centeredHeightParameter s))))).re =
          ‖canonicalCompletedC3GammaLogarithmicLeakState
            (centeredHeightParameter s)
            (centeredHeightParameter_im_ne_zero_of_re_ne_half hoff)‖ ^ 2) ∧
      ∀ᶠ M : ℕ in atTop,
        canonicalC3MixedRawNoLeakScalarReadout
            (canonicalC3FiniteMixedRawNoLeakChannelState M
              (centeredHeightParameter s) (centeredHeightParameter s)) = 0 ∧
          canonicalC3FiniteMixedRawNoLeakChannelState M
              (centeredHeightParameter s) (centeredHeightParameter s) ≠ 0 := by
  have hz : (centeredHeightParameter s).im ≠ 0 :=
    centeredHeightParameter_im_ne_zero_of_re_ne_half hoff
  have hzStrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hzHalf :
      0 < (operatorHeightParameter (centeredHeightParameter s)).re := by
    simpa using hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      canonicalCompletedC3RawHeightMixedWronskian_self_eq_zero_of_genuine_zero
        hs hzero
  · exact canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
      hzStrip hz
  · simpa only [operatorHeightParameter_centeredHeightParameter] using
      (canonicalCompletedC3AmbientResponse_pythagoras_iff_logarithmicLeakBalance
        (centeredHeightParameter s) hz hzHalf)
  · exact
      canonicalC3MixedRawNoLeak_scalarZero_but_channelStateEventuallyNonzero_of_offCritical_genuineZero
        hs hzero hoff

end

end CarrySelfAdjointOperator
