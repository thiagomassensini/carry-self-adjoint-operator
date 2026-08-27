import CarrySelfAdjointOperator.CompletedC3EnrichedSymplecticNoLeakBridge
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceGramBridge
import Mathlib.Tactic

/-!
# Completed C3 final-readout kernel bridge

The enriched all-cutoff C3 ledger retains the radial, structural, tail, and
archimedean channels until its final scalar readout.  This file normalizes
that readout only after the exact vector ledger has been assembled.

Off the diagonal, cancellation of the nonzero chart, characteristic, and
spectral-separation factors gives the divided difference of the completed
normalized response.  On the real diagonal, the canonical removable value
is its derivative.  Thus every cutoff gives the same total real-axis scalar
kernel, and its mixed forward differences converge to the already-derived
completed native moments.

This is a scalar readout theorem.  It does not assert that the final readout
is an inner product or that the resulting kernel is positive semidefinite.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- Normalize the final enriched ledger readout at a separated pair.  The
arguments are ordered so that `x` is the first argument of the resulting
divided-difference kernel and `z` is the second. -/
def canonicalCompletedC3AllCutoffOffDiagonalKernelReadout
    (M : ℕ) (x z : ℂ) : ℂ :=
  (canonicalCompletedC3AllCutoffKernelLedgerState M z x).finalReadout /
    (mixedHermitianWeight canonicalC3ChartFactorHeight z x *
      ((2 : ℂ) *
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
        completedNativeOperatorCharacteristic z) *
      (z - (starRingEnd ℂ) x))

/-- Before any real specialization, the normalized final ledger readout is
exactly the conjugate-polarized response quotient. -/
theorem canonicalCompletedC3AllCutoffOffDiagonalKernelReadout_eq
    (M : ℕ) {x z : ℂ}
    (hxStrip : operatorHeightParameter x ∈ genuineCriticalStrip)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hxF : completedNativeOperatorCharacteristic x ≠ 0)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hsep : z ≠ (starRingEnd ℂ) x) :
    canonicalCompletedC3AllCutoffOffDiagonalKernelReadout M x z =
      (z - (starRingEnd ℂ) x)⁻¹ *
        (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z -
          (starRingEnd ℂ)
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion x)) := by
  have hxChart : canonicalC3ChartFactorHeight x ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hxStrip
  have hzChart : canonicalC3ChartFactorHeight z ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hzStrip
  have hxChartStar :
      (starRingEnd ℂ) (canonicalC3ChartFactorHeight x) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hxChart
  have hxFStar :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hxF
  have hchartWeight :
      mixedHermitianWeight canonicalC3ChartFactorHeight z x ≠ 0 := by
    exact mul_ne_zero hzChart hxChartStar
  have hcharacteristicWeight :
      (2 : ℂ) *
          (starRingEnd ℂ) (completedNativeOperatorCharacteristic x) *
          completedNativeOperatorCharacteristic z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hxFStar) hzF
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [canonicalCompletedC3AllCutoffOffDiagonalKernelReadout,
    canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian
      M hzStrip hxStrip,
    hcompanion,
    completedGreenWronskian_eq_normalizedResponse_cross_mul
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion z x hzF hxF]
  field_simp [hchartWeight, hcharacteristicWeight,
    sub_ne_zero.mpr hsep]

/-- Canonical removable closure of the concrete final ledger readout on the
real height axis. -/
def canonicalCompletedC3AllCutoffRealKernelReadout
    (M : ℕ) (x z : ℝ) : ℂ :=
  if x = z then
    deriv
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) (x : ℂ)
  else
    canonicalCompletedC3AllCutoffOffDiagonalKernelReadout M (x : ℂ) (z : ℂ)

/-- Every cutoff of the enriched C3 ledger yields the same total real-axis
kernel after the final normalization: the `dslope` of the completed response.
-/
theorem canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope
    (M : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3AllCutoffRealKernelReadout M x z =
      dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (x : ℂ) (z : ℂ) := by
  by_cases hxz : x = z
  · subst z
    simp [canonicalCompletedC3AllCutoffRealKernelReadout, dslope_same]
  · have hxStrip : operatorHeightParameter (x : ℂ) ∈ genuineCriticalStrip := by
      constructor <;> norm_num [operatorHeightParameter]
    have hzStrip : operatorHeightParameter (z : ℂ) ∈ genuineCriticalStrip := by
      constructor <;> norm_num [operatorHeightParameter]
    have hsep : (z : ℂ) ≠ (starRingEnd ℂ) (x : ℂ) := by
      simpa using
        (show (z : ℂ) ≠ (x : ℂ) by exact_mod_cast (Ne.symm hxz))
    have hxStar : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by
      simp
    rw [canonicalCompletedC3AllCutoffRealKernelReadout, if_neg hxz,
      canonicalCompletedC3AllCutoffOffDiagonalKernelReadout_eq
        M hxStrip hzStrip hxF hzF hsep,
      completedNativeGreenNormalizedResponse_ofReal_conj,
      dslope_of_ne]
    · rw [hxStar, slope_def_module]
      simp only [smul_eq_mul]
    · exact_mod_cast (Ne.symm hxz)

/-- Complex-argument wrapper used by the existing mixed forward-difference
API.  Only the real coordinates are read. -/
def canonicalCompletedC3AllCutoffRealAxisKernelReadout
    (M : ℕ) (x z : ℂ) : ℂ :=
  canonicalCompletedC3AllCutoffRealKernelReadout M x.re z.re

/-- The normalized real-axis scalar kernel is independent of the cutoff at
every pair where the completed characteristic is nonzero. -/
theorem canonicalCompletedC3AllCutoffRealKernelReadout_cutoff_independent
    (M N : ℕ) (x z : ℝ)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hzF : completedNativeOperatorCharacteristic (z : ℂ) ≠ 0) :
    canonicalCompletedC3AllCutoffRealKernelReadout M x z =
      canonicalCompletedC3AllCutoffRealKernelReadout N x z := by
  rw [canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope M x z hxF hzF,
    canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope N x z hxF hzF]

/-- On each finite sampling rectangle, the concrete normalized ledger
kernel eventually agrees exactly with the scalar `dslope` kernel. -/
theorem canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_eventuallyEq_dslope
    (M p q : ℕ) :
    (fun k ↦ completedGreenKernelForwardDifference
      (canonicalCompletedC3AllCutoffRealAxisKernelReadout M)
      (canonicalGreenJetStep k) p q) =ᶠ[atTop]
    (fun k ↦ completedGreenKernelForwardDifference
      (fun x z ↦ dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) x z)
      (canonicalGreenJetStep k) p q) := by
  have hp : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  have hq : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        completedNativeOperatorCharacteristic
          (j • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero j
  filter_upwards [hp, hq] with k hkP hkQ
  apply completedGreenKernelForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [nsmul_canonicalGreenJetStep_eq_ofReal,
    nsmul_canonicalGreenJetStep_eq_ofReal]
  exact
    canonicalCompletedC3AllCutoffRealKernelReadout_eq_dslope M
      ((i : ℝ) * ((k : ℝ) + 1)⁻¹)
      ((j : ℝ) * ((k : ℝ) + 1)⁻¹)
      (by simpa [canonicalGreenJetStep] using hkP i hi)
      (by simpa [canonicalGreenJetStep] using hkQ j hj)

/-- All mixed forward differences of the concrete enriched C3 final readout
converge to the canonical polarized completed-native moments. -/
theorem canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_tendsto_moment
    (M p q : ℕ) :
    Tendsto
      (fun k ↦ completedGreenKernelForwardDifference
        (canonicalCompletedC3AllCutoffRealAxisKernelReadout M)
        (canonicalGreenJetStep k) p q)
      atTop
      (nhds
        (polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p q)) := by
  exact
    (completedNativeGreenKernelForwardDifference_dslope_tendsto p q).congr'
      (canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_eventuallyEq_dslope
        M p q).symm

/-- The same limit in the four even/odd blocks used by the completed Green
Hankel kernel.  This is the direct scalar bridge from the concrete enriched
ledger to the matrix entries used by the Jacobi construction. -/
theorem canonicalCompletedC3AllCutoffRealAxisKernelParityForwardDifference_tendsto
    (M : ℕ) (i j : ℕ ⊕ ℕ) :
    Tendsto
      (fun k ↦
        (completedGreenKernelForwardDifference
          (canonicalCompletedC3AllCutoffRealAxisKernelReadout M)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re)
      atTop
      (nhds
        (greenWronskianMomentKernel
          canonicalCompletedNativeLogDerivativeMoment i j)) := by
  have heq :=
    canonicalCompletedC3AllCutoffRealAxisKernelForwardDifference_eventuallyEq_dslope
      M (completedGreenParityOrder i) (completedGreenParityOrder j)
  have hre :
      (fun k ↦
        (completedGreenKernelForwardDifference
          (canonicalCompletedC3AllCutoffRealAxisKernelReadout M)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re) =ᶠ[atTop]
      (fun k ↦
        (completedGreenKernelForwardDifference
          (fun x z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) x z)
          (canonicalGreenJetStep k)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re) := by
    filter_upwards [heq] with k hk
    exact congrArg Complex.re hk
  exact
    (completedNativeGreenKernelForwardDifference_dslope_re_tendsto i j).congr'
      hre.symm

end

end CarrySelfAdjointOperator
