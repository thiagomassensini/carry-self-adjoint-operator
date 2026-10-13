import CarrySelfAdjointOperator.NativeCauchyLaguerreColumns
import Mathlib.Analysis.Normed.Operator.Extend

namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate lp
open Filter Topology
noncomputable section
set_option autoImplicit false

def physicalCauchySpan : Submodule ℂ CanonicalCompletedNativeChiralCauchyCarrier :=
  physicalCauchySynthesis.range

theorem physicalCauchySpan_eq_span : physicalCauchySpan =
    Submodule.span ℂ (Set.range completedNativeChiralCauchyFeature) :=
  Finsupp.range_linearCombination ℂ

/-- The closure is in the unchanged physical interval carrier, not a new completion metric. -/
def physicalCauchyClosure : Submodule ℂ CanonicalCompletedNativeChiralCauchyCarrier :=
  physicalCauchySpan.topologicalClosure

abbrev PhysicalCauchySpace := ↥physicalCauchyClosure

instance physicalCauchySpaceComplete : CompleteSpace PhysicalCauchySpace := by
  unfold PhysicalCauchySpace physicalCauchyClosure
  infer_instance

def physicalCauchyEmbedding : (ℕ →₀ ℂ) →ₗ[ℂ] PhysicalCauchySpace :=
  physicalCauchySynthesis.codRestrict physicalCauchyClosure fun c =>
    physicalCauchySpan.le_topologicalClosure (LinearMap.mem_range_self _ c)

@[simp] theorem physicalCauchyEmbedding_coe (c : ℕ →₀ ℂ) :
    (physicalCauchyEmbedding c : CanonicalCompletedNativeChiralCauchyCarrier) =
      physicalCauchySynthesis c := rfl

theorem physicalCauchyEmbedding_dense : DenseRange physicalCauchyEmbedding := by
  have hi : DenseRange (Set.inclusion physicalCauchySpan.le_topologicalClosure) :=
    (denseRange_inclusion_iff physicalCauchySpan.le_topologicalClosure).mpr (by rfl)
  change DenseRange ((Set.inclusion physicalCauchySpan.le_topologicalClosure) ∘
    physicalCauchySynthesis.rangeRestrict)
  exact hi.comp physicalCauchySynthesis.surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

private theorem physicalCauchyEmbedding_columnBound (c : ℕ →₀ ℂ) :
    ‖laguerreColumnSynthesis c‖ ≤ 1 * ‖physicalCauchyEmbedding c‖ := by
  rw [one_mul]
  change ‖laguerreColumnSynthesis c‖ ≤ ‖physicalCauchySynthesis c‖
  exact (laguerreColumnSynthesis_norm c).le

/-- Standard extension of the literal column map along the dense physical synthesis. -/
def cauchyLaguerreExtension : PhysicalCauchySpace →L[ℂ] ℓ²(ℕ, ℂ) :=
  laguerreColumnSynthesis.extendOfNorm physicalCauchyEmbedding

theorem cauchyLaguerreExtension_synthesis (c : ℕ →₀ ℂ) :
    cauchyLaguerreExtension (physicalCauchyEmbedding c) = laguerreColumnSynthesis c :=
  LinearMap.extendOfNorm_eq physicalCauchyEmbedding_dense
    ⟨1, physicalCauchyEmbedding_columnBound⟩ c

theorem cauchyLaguerreExtension_norm (x : PhysicalCauchySpace) :
    ‖cauchyLaguerreExtension x‖ = ‖x‖ := by
  refine physicalCauchyEmbedding_dense.induction_on x
    (isClosed_eq cauchyLaguerreExtension.continuous.norm continuous_norm) ?_
  intro c
  rw [cauchyLaguerreExtension_synthesis, laguerreColumnSynthesis_norm]
  rfl

def cauchyLaguerreIsometry : PhysicalCauchySpace →ₗᵢ[ℂ] ℓ²(ℕ, ℂ) :=
  { cauchyLaguerreExtension.toLinearMap with norm_map' := cauchyLaguerreExtension_norm }

theorem cauchyLaguerreIsometry_synthesis (c : ℕ →₀ ℂ) :
    cauchyLaguerreIsometry (physicalCauchyEmbedding c) = laguerreColumnSynthesis c :=
  cauchyLaguerreExtension_synthesis c

def physicalCauchyFeature (j : ℕ) : PhysicalCauchySpace :=
  physicalCauchyEmbedding (Finsupp.single j 1)

@[simp] theorem physicalCauchyFeature_coe (j : ℕ) :
    (physicalCauchyFeature j : CanonicalCompletedNativeChiralCauchyCarrier) =
      completedNativeChiralCauchyFeature j := by
  simp [physicalCauchyFeature, physicalCauchySynthesis]

/-- The all-order dictionary is applied to the ORIGINAL half-density columns. -/
theorem cauchyLaguerreIsometry_feature (j : ℕ) :
    cauchyLaguerreIsometry (physicalCauchyFeature j) = laguerreColumn j := by
  rw [physicalCauchyFeature, cauchyLaguerreIsometry_synthesis]
  simp [laguerreColumnSynthesis]

theorem laguerreColumnSynthesis_apply (c : ℕ →₀ ℂ) (r : ℕ) :
    laguerreColumnSynthesis c r = c.sum (fun j a => a * (feature r j : ℂ)) := by
  classical
  simp only [laguerreColumnSynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    laguerreColumn_apply]

theorem physicalCauchySynthesis_laguerreMode (c : ℕ →₀ ℂ) (r : ℕ) :
    inner ℂ (laguerreMode r) (physicalCauchySynthesis c) =
      c.sum (fun j a => a * (feature r j : ℂ)) := by
  classical
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    inner_sum, inner_smul_right, laguerreMode_feature]

/-- Coordinate observations are the old continuous functional moments on the whole closure. -/
theorem cauchyLaguerreIsometry_coordinate (x : PhysicalCauchySpace) (r : ℕ) :
    cauchyLaguerreIsometry x r =
      inner ℂ (laguerreMode r) (x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  have hc : Continuous (fun x : PhysicalCauchySpace => cauchyLaguerreIsometry x r) :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 r).continuous.comp cauchyLaguerreIsometry.continuous
  have hm : Continuous (fun x : PhysicalCauchySpace =>
      inner ℂ (laguerreMode r) (x : CanonicalCompletedNativeChiralCauchyCarrier)) := by
    fun_prop
  refine physicalCauchyEmbedding_dense.induction_on x (isClosed_eq hc hm) ?_
  intro c
  rw [cauchyLaguerreIsometry_synthesis, physicalCauchyEmbedding_coe,
    laguerreColumnSynthesis_apply, physicalCauchySynthesis_laguerreMode]

theorem cauchyLaguerreIsometry_inner (x y : PhysicalCauchySpace) :
    inner ℂ (cauchyLaguerreIsometry x) (cauchyLaguerreIsometry y) =
      inner ℂ (x : CanonicalCompletedNativeChiralCauchyCarrier)
        (y : CanonicalCompletedNativeChiralCauchyCarrier) :=
  cauchyLaguerreIsometry.inner_map_map x y

theorem cauchyLaguerreIsometry_range_isClosed :
    IsClosed (cauchyLaguerreIsometry.toLinearMap.range : Set ℓ²(ℕ, ℂ)) :=
  cauchyLaguerreIsometry.isometry.isClosedEmbedding.isClosed_range

end
end CarrySelfAdjointOperator.NativeLaguerre
