import CPFormal.Analytic.CpAngularPort
import CPFormal.Analytic.CpGenuineCompatibility
import NativeCarrySpectralWeyl.Camera.CommonZeroSet
import Mathlib.Tactic

/-!
# Native scalar and Genuine chart identification

The native camera-3 bracket and the canonical Genuine chart are the same
absolutely summable series.  Their seed terms coincide, and every aligned
camera-3 center block is literally the same centered second difference.

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
