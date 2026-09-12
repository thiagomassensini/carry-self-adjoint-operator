import CarrySelfAdjointOperator.CompletedNativePolarizedTfvdGreenMomentKernel
import CarrySelfAdjointOperator.CompletedC3FourCornerGreenCell
import Mathlib.Tactic

/-!
# Native four-corner / same-edge bridge for the polarized TFVD--Green ledger

The native four-corner development already constructs, before scalar Green or
Wronskian readout, a two-variable positive kernel

`nativeGpreFourCornerPolarizedDirichletPrefix`.

It is proved there to be simultaneously

* the complete provenance-preserving four-corner synthesis;
* the raw C3 gamma Gram of ordinary Dirichlet-gradient prefixes;
* a positive-semidefinite finite Gram kernel;
* and, on a reflected second leg, the exact Primus same-edge reconstruction
  from the ordinary gradient and logarithmic jet.

The current polarized TFVD--Green ledger was developed later and exposes the
completed mixed Wronskian as finite reflected Green plus an explicit total
defect.  This module is the missing adapter between those two layers.  It does
not define another carrier.  Instead, it rewrites the Green term and the named
ledger defect directly through the already-formalized native four-corner
kernel and its same-edge ordinary/log-jet realization.

No moment sequence, Hankel matrix, fixed-time transport, fitted metric, or
vanishing of the ledger defect is assumed.
-/

open scoped BigOperators ComplexConjugate ComplexOrder Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The finite mixed Green term in the new polarized ledger is exactly the
native four-corner kernel multiplied by the already-fixed mixed radial
coefficient.  Thus the carrier on the right predates the ledger and is not
defined from the desired Wronskian identity. -/
theorem
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_nativeFourCorner
    (M : ℕ) (z w : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M w)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z)) =
      canonicalC3MixedRadialCoefficient z w *
        nativeGpreFourCornerPolarizedDirichletPrefix
          M w (reflectedParameter z) := by
  rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_gram,
    nativeGpreFourCornerPolarizedDirichletPrefix_eq_rawGammaGram]

/-- The same finite Green term written entirely from the unreflected ordinary
and log-jet source on the reflected leg.  This is the direct Primus
same-edge reconstruction before scalar synthesis. -/
theorem
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_logJetReconstruction
    (M : ℕ) (z w : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M w)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter z)) =
      canonicalC3MixedRadialCoefficient z w *
        (∑ n ∈ Finset.range M,
          (starRingEnd ℂ) (positiveDirichletGradient w n) *
            sameEdgeRecoveredReflectedGradient n
              (positiveDirichletGradient z n)
              (positiveLogDirichletGradient z n)) := by
  rw [greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_nativeFourCorner,
    nativeGpreFourCornerPolarizedDirichletPrefix_reflected_eq_logJetReconstruction]

/-- Exact finite crosswalk from the completed mixed Wronskian ledger to the
pre-existing native four-corner Gram.  The existing total defect is kept
unchanged and visible. -/
theorem canonicalCompletedC3RawMixedWronskian_eq_nativeFourCorner_add_totalDefect
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      canonicalC3MixedRadialCoefficient z w *
          nativeGpreFourCornerPolarizedDirichletPrefix
            (3 * M) w (reflectedParameter z) +
        canonicalC3FiniteMixedTotalDefect M z w := by
  rw [canonicalCompletedC3RawMixedWronskian_eq_green_add_totalDefect
      M hz hw,
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_nativeFourCorner]

/-- The named polarized TFVD--Green defect is literally the completed mixed
Wronskian minus the finite native four-corner Green term.  This connects the
new ledger to the old native positive carrier without redefining the defect. -/
theorem
    canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_wronskian_sub_nativeFourCorner
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w =
      canonicalCompletedC3RawMixedWronskian z w -
        canonicalC3MixedRadialCoefficient z w *
          nativeGpreFourCornerPolarizedDirichletPrefix
            (3 * M) w (reflectedParameter z) := by
  rw [canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_wronskian_sub_green
      M hz hw,
    greenForm_finiteC3GenuineBracket_twoParameter_eq_coefficient_mul_nativeFourCorner]

/-- Along the native `3M` cutoffs, the native four-corner term converges to the
same completed mixed radial Green kernel already used by the polarized ledger. -/
theorem nativeFourCornerMixedGreen_tendsto_completed
    {z w : ℂ} (hw : 0 < w.re)
    (hzReflected : 0 < (reflectedParameter z).re) :
    Tendsto
      (fun M : ℕ =>
        canonicalC3MixedRadialCoefficient z w *
          nativeGpreFourCornerPolarizedDirichletPrefix
            (3 * M) w (reflectedParameter z))
      atTop
      (nhds
        (canonicalCompletedC3MixedRadialGreenKernel
          z w hw hzReflected)) := by
  have hprefix :=
    nativeGpreFourCornerPolarizedDirichletPrefix_tendsto_completed
      (r := w) (s := reflectedParameter z) hw hzReflected
  have hprefixThree := hprefix.comp tendsto_three_mul_atTop
  have hscaled :=
    hprefixThree.const_mul (canonicalC3MixedRadialCoefficient z w)
  simpa [canonicalCompletedC3MixedRadialGreenKernel] using hscaled

/-- The limit statement for the current named defect can therefore be stated
entirely in the old native four-corner kernel language. -/
theorem
    canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto_nativeFourCornerLimit
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
    (hw : 0 < w.re) :
    Tendsto
      (fun M : ℕ =>
        canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w)
      atTop
      (nhds
        (canonicalCompletedC3RawMixedWronskian z w -
          canonicalC3MixedRadialCoefficient z w *
            canonicalCompletedC3RawGammaGram
              w (reflectedParameter z) hw
              (by simpa [reflectedParameter] using sub_pos.mpr hzUpper))) := by
  simpa [canonicalCompletedC3MixedRadialGreenKernel] using
    (canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto
      hz hzUpper hw)

/-- Consequently the current completed Wronskian/Green sewing gate is exactly
the statement that the explicit TFVD/Green defect tends to zero, with the
Green side now identified as the completion of the native four-corner Gram. -/
theorem
    canonicalNativePolarizedTfvdGreenMomentKernel_eq_nativeFourCorner_iff_defect_limit_zero
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
    (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
        canonicalC3MixedRadialCoefficient z w *
          canonicalCompletedC3RawGammaGram
            w (reflectedParameter z) hw
            (by simpa [reflectedParameter] using sub_pos.mpr hzUpper) ↔
      Tendsto
        (fun M : ℕ =>
          canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w)
        atTop (nhds 0) := by
  simpa [canonicalCompletedC3MixedRadialGreenKernel] using
    (canonicalNativePolarizedTfvdGreenMomentKernel_eq_iff_defect_limit_zero
      hz hzUpper hw)

/-- The raw native source used on the Green side is positive semidefinite at
every finite cutoff.  This is inherited from the pre-existing four-corner
carrier, not from the mixed Wronskian or its defect. -/
theorem nativePolarizedFourCornerSource_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    (Matrix.of fun i j =>
      nativeGpreFourCornerPolarizedDirichletPrefix M
        (point i) (point j)).PosSemidef := by
  exact nativeGpreFourCornerPolarizedDirichletPrefix_posSemidef M point

end

end CarrySelfAdjointOperator
