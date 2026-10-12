import CarrySelfAdjointOperator.NativeIntervalMultiplier
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Compression of the actual physical radial operator onto certified modes. -/
namespace CarrySelfAdjointOperator.NativeLaguerre
open scoped unitInterval InnerProductSpace
noncomputable section
set_option autoImplicit false

def firstThreeLaguerreSpan : Submodule ℂ CanonicalCompletedNativeChiralCauchyCarrier :=
  Submodule.span ℂ (Set.range (fun r : Fin 3 => laguerreMode r.val))

instance firstThreeLaguerreSpan_finiteDimensional : FiniteDimensional ℂ firstThreeLaguerreSpan :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

def firstThreeLaguerreProjection := firstThreeLaguerreSpan.starProjection

theorem firstThreeLaguerreProjection_idempotent :
    firstThreeLaguerreProjection * firstThreeLaguerreProjection = firstThreeLaguerreProjection :=
  firstThreeLaguerreSpan.isIdempotentElem_starProjection

theorem firstThreeLaguerreProjection_isSelfAdjoint : IsSelfAdjoint firstThreeLaguerreProjection :=
  isSelfAdjoint_starProjection _

theorem firstThreeLaguerreProjection_mode (r : Fin 3) :
    firstThreeLaguerreProjection (laguerreMode r.val) = laguerreMode r.val := by
  apply firstThreeLaguerreSpan.starProjection_eq_self_iff.mpr
  exact Submodule.subset_span (Set.mem_range_self r)

/-- The actual loss through the orthogonal complement of the three modes. -/
def physicalFirstThreeLeakage :=
  firstThreeLaguerreProjection * physicalRadialAdvance * (1-firstThreeLaguerreProjection) *
    physicalRadialAdvance * firstThreeLaguerreProjection

theorem physicalFirstThree_compression_square :
    firstThreeLaguerreProjection * physicalRadialAdvance^2 * firstThreeLaguerreProjection =
      (firstThreeLaguerreProjection * physicalRadialAdvance * firstThreeLaguerreProjection)^2 +
        physicalFirstThreeLeakage := by
  have hs : (firstThreeLaguerreProjection * physicalRadialAdvance *
      firstThreeLaguerreProjection)^2 =
      firstThreeLaguerreProjection * physicalRadialAdvance *
      (firstThreeLaguerreProjection * firstThreeLaguerreProjection) *
      physicalRadialAdvance * firstThreeLaguerreProjection := by noncomm_ring
  rw [hs, firstThreeLaguerreProjection_idempotent]
  unfold physicalFirstThreeLeakage
  noncomm_ring

theorem physicalFirstThreeLeakage_eq_gram :
    physicalFirstThreeLeakage =
      star ((1-firstThreeLaguerreProjection)*physicalRadialAdvance*firstThreeLaguerreProjection) *
        ((1-firstThreeLaguerreProjection)*physicalRadialAdvance*firstThreeLaguerreProjection) := by
  have hc : (1-firstThreeLaguerreProjection)*(1-firstThreeLaguerreProjection) =
      1-firstThreeLaguerreProjection := by
    calc
      _ = 1-firstThreeLaguerreProjection-firstThreeLaguerreProjection+
        firstThreeLaguerreProjection*firstThreeLaguerreProjection := by noncomm_ring
      _ = _ := by rw [firstThreeLaguerreProjection_idempotent]; noncomm_ring
  simp only [star_mul, star_sub, star_one,
    physicalRadialAdvance_isSelfAdjoint.star_eq,
    firstThreeLaguerreProjection_isSelfAdjoint.star_eq]
  calc
    physicalFirstThreeLeakage = firstThreeLaguerreProjection*physicalRadialAdvance*
      ((1-firstThreeLaguerreProjection)*(1-firstThreeLaguerreProjection))*
      physicalRadialAdvance*firstThreeLaguerreProjection := by rw [hc]; rfl
    _ = _ := by noncomm_ring

theorem physicalFirstThreeLeakage_isPositive : physicalFirstThreeLeakage.IsPositive := by
  rw [physicalFirstThreeLeakage_eq_gram]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The input outside the compression is retained explicitly, for every physical h. -/
theorem physicalFirstThree_outside_input
    (h : CanonicalCompletedNativeChiralCauchyCarrier) :
    firstThreeLaguerreProjection ((physicalRadialAdvance^2) h) =
      ((firstThreeLaguerreProjection*physicalRadialAdvance*firstThreeLaguerreProjection)^2) h +
      physicalFirstThreeLeakage h +
      (firstThreeLaguerreProjection*physicalRadialAdvance^2*(1-firstThreeLaguerreProjection) :
        CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier) h := by
  have he : firstThreeLaguerreProjection*physicalRadialAdvance^2 =
      firstThreeLaguerreProjection*physicalRadialAdvance^2*firstThreeLaguerreProjection +
      firstThreeLaguerreProjection*physicalRadialAdvance^2*(1-firstThreeLaguerreProjection) := by
    noncomm_ring
  rw [physicalFirstThree_compression_square] at he
  exact congrArg (fun T => T h) he

end
end CarrySelfAdjointOperator.NativeLaguerre
