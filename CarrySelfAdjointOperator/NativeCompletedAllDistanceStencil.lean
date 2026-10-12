import CarrySelfAdjointOperator.FirstEdgeChiralStateComparison

/-! All-distance second differences of the ORIGINAL completed two-leg state.
The geometric, amplitude and quotient channels are retained before readout. -/
namespace CarrySelfAdjointOperator.FirstEdgeSewing
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem edge_telescope {E : Type*} [AddCommGroup E] (V : ℕ → E) (p d : ℕ) :
    (∑ t ∈ Finset.range d, (V (p+t+1) - V (p+t))) = V (p+d) - V p := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show p + (d+1) = p+d+1 by omega]
    abel

theorem completed_stencil_all_distance (k p d : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k p -
      2 • canonicalCompletedNativeRadialProjectiveChiralState k (p+d) +
      canonicalCompletedNativeRadialProjectiveChiralState k (p+2*d) =
    ∑ t ∈ Finset.range d, ∑ γ : Fin 3,
      (radialChiralEdgeChannels k (p+d+t) γ - radialChiralEdgeChannels k (p+t) γ) := by
  simp_rw [Finset.sum_sub_distrib, ← radialProjectiveEdge_eq_threeChannels]
  rw [edge_telescope, edge_telescope]
  rw [show p+2*d = (p+d)+d by omega]
  abel

/-- Any independently typed linear readout preserves the whole stencil.
This does not assert the existence of a material/radial sewing map. -/
theorem completed_stencil_linear_transport {E : Type*} [AddCommGroup E]
    [Module ℂ E] (T : CanonicalCompletedNativeProjectiveChiralCarrier →ₗ[ℂ] E)
    (k p d : ℕ) :
    T (canonicalCompletedNativeRadialProjectiveChiralState k p -
      2 • canonicalCompletedNativeRadialProjectiveChiralState k (p+d) +
      canonicalCompletedNativeRadialProjectiveChiralState k (p+2*d)) =
    ∑ t ∈ Finset.range d, ∑ γ : Fin 3,
      (T (radialChiralEdgeChannels k (p+d+t) γ) - T (radialChiralEdgeChannels k (p+t) γ)) := by
  rw [completed_stencil_all_distance]
  simp only [map_sum, map_sub]

end
end CarrySelfAdjointOperator.FirstEdgeSewing
