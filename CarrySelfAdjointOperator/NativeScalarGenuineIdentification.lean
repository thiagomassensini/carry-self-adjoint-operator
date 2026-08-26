import CPFormal.Analytic.CpAngularPort
import CPFormal.Analytic.CpGenuineCompatibility
import NativeCarrySpectralWeyl.Camera.CommonZeroSet
import Mathlib.Tactic

/-!
# Native scalar and Genuine chart identification

The native camera-3 bracket and the canonical Genuine chart are the same
series.  Their seed terms coincide, and every aligned camera-3 center block
is literally the same centered second difference.  On the explicit half-plane
`-1 < re s`, both series are absolutely summable in norm.

This gives the native-to-Genuine identification directly from the carry
geometry, without passing through any external meromorphic function.
-/

open scoped BigOperators

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- A native camera-3 center block is exactly the corresponding Genuine
camera-3 saturated bracket. -/
theorem centerBracketTerm_three_eq_realCpSaturatedBracket
    (index : ℕ) (s : ℂ) :
    centerBracketTerm 3 s index = realCpSaturatedBracket 3 index s := by
  rw [realCpSaturatedBracket_three_eq_values]
  norm_num [centerBracketTerm, radiusSet,
    FiniteNativeCarryOperator.Camera.halfRange, alignedCenter,
    centeredBracketTerm, dirichletValue, natDirichletTerm, dirichletTerm]
  ring_nf

/-- Absolute summability of the native camera-3 center blocks on the explicit
half-plane `-1 < re s`. -/
theorem centerBracketTerm_three_norm_summable_of_neg_one_lt_re
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun index : ℕ => ‖centerBracketTerm 3 s index‖) :=
  centerBracketTerm_norm_summable (camera := 3) (by norm_num) hs

/-- The corresponding Genuine/TFVD camera-3 blocks are absolutely summable
on the same half-plane, transported through the literal block identity. -/
theorem realCpSaturatedBracket_three_norm_summable_of_neg_one_lt_re
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun index : ℕ => ‖realCpSaturatedBracket 3 index s‖) := by
  simpa only [centerBracketTerm_three_eq_realCpSaturatedBracket] using
    centerBracketTerm_three_norm_summable_of_neg_one_lt_re hs

/-- The finite seed of the native camera-3 series is the Genuine camera-3
seed. -/
theorem seedDirichletTerm_three_eq_genuineSeed (s : ℂ) :
    seedDirichletTerm 3 s =
      CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm s) := by
  norm_num [seedDirichletTerm, radiusSet,
    FiniteNativeCarryOperator.Camera.halfRange, dirichletValue,
    CPFormal.Genuine.Cp.seedSum, CPFormal.Genuine.Cp.halfRange,
    dirichletTerm]

/-- The two camera-3 bracket charts are definitionally the same seed plus
the same absolutely summable center-block series. -/
theorem bracketCharacteristic_three_eq_bracketedDirichletChart_native
    (s : ℂ) :
    bracketCharacteristic 3 s = bracketedDirichletChart 3 s := by
  rw [bracketCharacteristic, bracketedDirichletChart,
    seedDirichletTerm_three_eq_genuineSeed]
  congr 1
  exact tsum_congr (fun index =>
    centerBracketTerm_three_eq_realCpSaturatedBracket index s)

/-- On `-1 < re s`, the native and Genuine camera-3 charts are explicitly
the same absolutely convergent series: both norm series are summable and the
resulting chart values coincide. -/
theorem cameraThreeBracketCharts_absoluteSummability_and_eq
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun index : ℕ => ‖centerBracketTerm 3 s index‖) ∧
      Summable (fun index : ℕ => ‖realCpSaturatedBracket 3 index s‖) ∧
      bracketCharacteristic 3 s = bracketedDirichletChart 3 s :=
  ⟨centerBracketTerm_three_norm_summable_of_neg_one_lt_re hs,
    realCpSaturatedBracket_three_norm_summable_of_neg_one_lt_re hs,
    bracketCharacteristic_three_eq_bracketedDirichletChart_native s⟩

/-- Every finite camera-3 prefix is also literally the corresponding finite
Genuine bracket prefix. -/
theorem finiteBracketCharacteristic_three_eq_finiteBracketedDirichletChart
    (cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic 3 cutoff s =
      finiteBracketedDirichletChart 3 cutoff s := by
  unfold finiteBracketCharacteristic finiteBracketedDirichletChart
  rw [seedDirichletTerm_three_eq_genuineSeed]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  exact centerBracketTerm_three_eq_realCpSaturatedBracket index s

/-- Domain-compatible API for earlier downstream uses. -/
theorem bracketCharacteristic_three_eq_bracketedDirichletChart
    {s : ℂ} (_hs : s ∈ bracketHalfPlane) :
    bracketCharacteristic 3 s = bracketedDirichletChart 3 s :=
  bracketCharacteristic_three_eq_bracketedDirichletChart_native s

/-- The native scalar and the canonical Genuine continuation are the same
quotient for every complex parameter. -/
theorem nativeScalar_eq_genuineContinuation_unconditional (s : ℂ) :
    nativeScalar s = genuineContinuation s := by
  have hfactor : factor 3 s = cpChartFactor 3 s := by
    rw [factor_of_odd (by norm_num : 3 ≠ 2) (by norm_num : Odd 3)]
    rfl
  rw [nativeScalar, genuineContinuation, cpGenuineQuotient,
    bracketCharacteristic_three_eq_bracketedDirichletChart_native,
    hfactor]

/-- Strip-compatible API for downstream modules.  The strip witness is kept
only for compatibility; the identification itself is unconditional. -/
theorem nativeScalar_eq_genuineContinuation
    {s : ℂ} (_hs : s ∈ genuineCriticalStrip) :
    nativeScalar s = genuineContinuation s :=
  nativeScalar_eq_genuineContinuation_unconditional s

end

end CarrySelfAdjointOperator
