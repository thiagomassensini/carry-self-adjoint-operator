import CarrySelfAdjointOperator.CompletedC3FNegFPrimeMixedKernel
import CarrySelfAdjointOperator.CompletedC3RawSpectralTraceTransport
import CarrySelfAdjointOperator.UnconditionalLimitConfinementProbe
import Mathlib.Tactic

/-!
# Minimal reflected C3 confinement seam

The public diagonal seam asks for a diagonal raw Gamma Gram.  The finite C3
Green boundary naturally produced by the reflected construction instead has a
reflected second parameter.  This file records the smaller interface actually
needed for confinement: the scalar completed Wronskian agrees with that
reflected finite Green boundary.

The proof below deliberately never transports a reflected Gram to a diagonal
Gram.  Its only nondegeneracy input is the already proved nonvanishing of the
finite reflected pairing in the Genuine strip.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The minimal scalar-to-boundary interface sufficient for C3 Genuine-zero
confinement.  Unlike `MinimalPublicC3ConfinementSeam`, it retains the
geometrically natural reflected finite Green boundary and contains no diagonal
raw Gamma Gram. -/
def MinimalReflectedC3ConfinementSeam : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) =
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s))

/-- The reflected finite C3 seam already suffices for public Genuine-zero
confinement.  No reflected-to-diagonal Gram identification is used: after the
existing spectral factorization, the positive radial cofactor and the finite
reflected pairing are both nonzero in the Genuine strip. -/
theorem finalGenuineZeroConfinement_of_minimalReflectedC3ConfinementSeam
    (hseam : MinimalReflectedC3ConfinementSeam) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  by_cases hhalf : s.re = (1 : ℝ) / 2
  · exact hhalf
  have hboundaryZero :
      genuineComplexTimeBoundaryValue (carryComplexTimeOfParameter s) = 0 := by
    unfold genuineComplexTimeBoundaryValue
    rw [carryComplexTimeParameter_ofParameter]
    exact hzero
  have hwronskian :
      scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) = 0 := by
    unfold scalarGreenWronskian
    rw [hboundaryZero]
    simp
  have hgreen :
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s)) = 0 := by
    rw [← hseam hs hhalf]
    exact hwronskian
  have hspectral :
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s)) =
        (carryComplexTimeOfParameter s -
            (starRingEnd ℂ) (carryComplexTimeOfParameter s)) *
          (Complex.I *
            ((cpRadialCofactor 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
            c3RawGammaGram 1 s (reflectedParameter s)) := by
    rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
      canonicalC3MixedRadialCoefficient_self_eq_radialDifference,
      radialDifference_eq_i_mul_centeredFactor_mul_cofactor]
    simp only [carryComplexTimeOfParameter_eq_centeredHeightParameter]
    ring
  rw [hspectral] at hgreen
  have hpair : finiteReflectedGradientPairing 1 s ≠ 0 :=
    finiteReflectedGradientPairing_ne_zero (by norm_num) hs
  have hgram : c3RawGammaGram 1 s (reflectedParameter s) ≠ 0 := by
    change c3RawGammaGram 1 s (reflectedParameter s) ≠ 0 at hpair
    exact hpair
  have hcofactorReal :
      cpRadialCofactor 3 (criticalDisplacement s.re) ≠ 0 :=
    ne_of_gt (cpRadialCofactor_pos 3 (by norm_num)
      (criticalDisplacement s.re))
  have hcofactor :
      ((cpRadialCofactor 3 (criticalDisplacement s.re) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hcofactorReal
  have hreflected :
      Complex.I *
          ((cpRadialCofactor 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
          c3RawGammaGram 1 s (reflectedParameter s) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hcofactor) hgram
  have htime :
      carryComplexTimeOfParameter s -
          (starRingEnd ℂ) (carryComplexTimeOfParameter s) = 0 :=
    (mul_eq_zero.mp hgreen).resolve_right hreflected
  have htimeReal :
      carryComplexTimeOfParameter s =
        (starRingEnd ℂ) (carryComplexTimeOfParameter s) :=
    sub_eq_zero.mp htime
  have him : (carryComplexTimeOfParameter s).im = 0 :=
    Complex.conj_eq_iff_im.mp htimeReal.symm
  rw [carryComplexTimeOfParameter_im] at him
  unfold criticalDisplacement at him
  linarith

/-! ## The remaining scalarization frontier

The preceding theorem consumes only the reflected seam.  The existing
completed-TFVD factorization is a different, but fully explicit presentation:
at cutoff `3 * M` it identifies a *weighted* completed
Wronskian with the corresponding reflected bracket Green readout plus the
five retained channels `greenProvenance`, `offDiagonal`, `readoutResidual`,
`tailCompletion`, and `archimedeanChart`.

Consequently it does not itself inhabit
`MinimalReflectedC3ConfinementSeam`: the latter uses the genuine carry-time
boundary and the one-block finite pair.  The exact open comparison is solely
the scalar boundary-form preservation asserted by the definition above; no
reflected-to-diagonal Gram transport occurs in that comparison.
-/

end

end CarrySelfAdjointOperator
