import CarrySelfAdjointOperator.CompletedOperatorCharacteristic
import CPFormal.Analytic.CpGenuineRiemannZetaIdentification
import NativeCarrySpectralWeyl.Camera.BracketProfileFactorization
import Mathlib.Tactic

/-!
# Identification of the native scalar with the genuine zeta continuation

The camera-3 bracket characteristic and the canonical Cp bracketed chart are
constructed independently, but they are analytic on the same half-plane and
agree on `re s > 1`.  Analytic-continuation uniqueness therefore identifies
them on the full bracket half-plane.  Dividing by their literally identical
camera-3 factor then identifies the native scalar with the canonical Genuine
continuation, and hence with Mathlib's `riemannZeta`, on the open critical
strip.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The two independently constructed camera-3 bracket charts are the same
analytic function on their common half-plane. -/
theorem bracketCharacteristic_three_eq_bracketedDirichletChart
    {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    bracketCharacteristic 3 s = bracketedDirichletChart 3 s := by
  have hanalytic :
      AnalyticOnNhd ℂ (bracketCharacteristic 3) bracketHalfPlane := by
    have hdiff :
        DifferentiableOn ℂ (bracketCharacteristic 3) bracketHalfPlane := by
      simpa [bracketHalfPlane, bracketDomain] using
        (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3))
    exact hdiff.analyticOnNhd isOpen_bracketHalfPlane
  have hagree : ∀ z : ℂ, 1 < z.re →
      bracketCharacteristic 3 z =
        (1 - (3 : ℂ) ^ (1 - z)) * genuineDirichlet z := by
    intro z hz
    rw [bracketCharacteristic_eq_factor_mul_riemannZeta
      (by omega : 2 ≤ 3) hz]
    rw [← genuineDirichlet_eq_riemannZeta hz]
    rw [factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3)]
    rfl
  exact bracketedDirichletChart_unique_analytic_continuation
    3 (by norm_num) (by norm_num) (bracketCharacteristic 3)
    hanalytic hagree hs

/-- On the open critical strip, the quotient canonically extracted from the
native carry camera is the canonical Genuine analytic continuation. -/
theorem nativeScalar_eq_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeScalar s = genuineContinuation s := by
  have hhalf : s ∈ bracketHalfPlane := by
    change -1 < s.re
    linarith [hs.1]
  have hfactor : factor 3 s = cpChartFactor 3 s := by
    rw [factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3)]
    rfl
  rw [nativeScalar, genuineContinuation, cpGenuineQuotient,
    bracketCharacteristic_three_eq_bracketedDirichletChart hhalf]
  rw [hfactor]

/-- Consequently, the native scalar is literally Mathlib's Riemann zeta on
the open critical strip. -/
theorem nativeScalar_eq_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    nativeScalar s = riemannZeta s := by
  rw [nativeScalar_eq_genuineContinuation hs,
    genuineContinuation_eq_riemannZeta hs]

/-- The completed operator characteristic from the native script is the
standard completed zeta expression wherever its height parameter lies in the
open critical strip. -/
theorem completedNativeOperatorCharacteristic_eq_completedRiemannZeta
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z *
        riemannZeta (operatorHeightParameter z) := by
  rw [completedNativeOperatorCharacteristic,
    nativeScalar_eq_riemannZeta hs]

end

end CarrySelfAdjointOperator
