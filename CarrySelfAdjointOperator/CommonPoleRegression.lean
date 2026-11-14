import CarrySelfAdjointOperator.CompletedNativeCommonPoleAdapter

/-! Small algebraic canaries; all-order theorems live in the imported modules. -/
namespace CarrySelfAdjointOperator

open scoped BigOperators

example : commonPoleOddCoefficient 0 = -2 := by
  norm_num [commonPoleOddCoefficient]

example : commonPoleOddCoefficient 1 = 8 := by
  norm_num [commonPoleOddCoefficient]

example (a : ℝ) :
    (∑ i : Fin 1, ∑ j : Fin 1,
      a * a * commonPoleOddCoefficient (i.val + j.val)) = -2 * a ^ 2 := by
  have h := commonPoleOddCoefficient_quadratic 0 1 (fun _ => a)
  simpa [commonPoleOddCoefficient] using h

example :
    (commonPoleOddResponse 0 - commonPoleOddResponse 0) *
        ((1 + 4 * (0 : ℂ) ^ 2) * (1 + 4 * (0 : ℂ) ^ 2)) =
      (0 - 0) * (-2 + 8 * (0 : ℂ) * 0) := by
  simp only [commonPoleOddResponse_dividedDifference_mul
    (0 : ℂ) 0 (by norm_num) (by norm_num)]

end CarrySelfAdjointOperator
