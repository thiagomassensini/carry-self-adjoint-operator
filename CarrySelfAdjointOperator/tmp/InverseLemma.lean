import CarrySelfAdjointOperator.SixCameraIntrinsicWeylHighEnergyReturn
open scoped BigOperators ENNReal MeasureTheory RealInnerProductSpace Matrix MatrixOrder ComplexConjugate
open Set MeasureTheory Filter
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

 theorem inverse_one_add_exact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N W : E →L[ℝ] E)
    (hWN : ∀ z, N (W z) = z) (z : E) :
    W z = z - (N - ContinuousLinearMap.id ℝ E) z +
      (N - ContinuousLinearMap.id ℝ E)
        ((N - ContinuousLinearMap.id ℝ E) (W z)) := by
  let K : E →L[ℝ] E := N - ContinuousLinearMap.id ℝ E
  have h := hWN z
  have hrewrite : N = ContinuousLinearMap.id ℝ E + K := by
    ext x
    simp [K]
  rw [hrewrite, add_apply, id_apply] at h
  have hK := congrArg K h
  rw [map_add] at hK
  change W z = z - K z + K (K (W z))
  change W z + K (W z) = z at h
  abel

end
end CarrySelfAdjointOperator
