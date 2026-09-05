import CarrySelfAdjointOperator.PositiveObservableParityKernel
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The actual diagonal of the positive-observable kernel

The division-free identity at equal parameters would only say `0 = 0`.
Here the concrete resolvent vector is continuous on its Neumann domain.
The polarized identity then identifies the limit of every punctured slope
with the diagonal Gram, giving an actual derivative at each domain point.
-/

open Filter
open scoped Topology

namespace CarrySelfAdjointOperator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H]

/-- Continuity of the actual Neumann resolvent vector at every point of its
explicit local domain.  No symmetry is needed for this analytic statement. -/
theorem positiveObservableResolventVector_continuousAt
    (S : H →L[ℝ] H) (u : H) (x : ℝ) (hx : |x| * ‖S‖ < 1) :
    ContinuousAt (positiveObservableResolventVector S u) x := by
  have hunit : IsUnit (1 - x ^ 2 • (S * S)) :=
    isUnit_one_sub_of_norm_lt_one (positiveObservable_neumannBound S x hx)
  have hinverse : ContinuousAt Ring.inverse
      (1 - x ^ 2 • (S * S)) := by
    obtain ⟨v, hv⟩ := hunit
    simpa only [hv] using NormedRing.inverse_continuousAt v
  have hoperator : ContinuousAt
      (fun t : ℝ => (1 : H →L[ℝ] H) - t ^ 2 • (S * S)) x :=
    continuousAt_const.sub ((continuousAt_id.pow 2).smul continuousAt_const)
  have hfamily : ContinuousAt
      (fun t : ℝ => Ring.inverse ((1 : H →L[ℝ] H) - t ^ 2 • (S * S))) x :=
    hinverse.comp (f := fun t : ℝ => (1 : H →L[ℝ] H) - t ^ 2 • (S * S)) hoperator
  exact hfamily.clm_apply continuousAt_const

/-- Both coordinates of the same positive parity state are continuous. -/
theorem positiveObservableResolventParityState_continuousAt
    (S : H →L[ℝ] H) (u : H) (x : ℝ) (hx : |x| * ‖S‖ < 1) :
    ContinuousAt (positiveObservableResolventParityState S u) x := by
  have hr := positiveObservableResolventVector_continuousAt S u x hx
  have hpair : ContinuousAt
      (fun t : ℝ => (positiveObservableResolventVector S u t,
        t • S (positiveObservableResolventVector S u t))) x :=
    hr.prodMk (continuousAt_id.smul (S.continuous.continuousAt.comp hr))
  exact (WithLp.prod_continuous_toLp 2 H H).continuousAt.comp hpair

/-- The diagonal is the derivative of the scalar response, established by
continuity of the polarized kernel on punctured neighborhoods. -/
theorem positiveObservableResolventResponse_hasDerivAt
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (x : ℝ) (hx : |x| * ‖S‖ < 1) :
    HasDerivAt (positiveObservableResolventResponse S u)
      (inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u x)) x := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hstate := positiveObservableResolventParityState_continuousAt S u x hx
  have hkernel : ContinuousAt
      (fun z : ℝ => inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u z)) x :=
    continuousAt_const.inner hstate
  have hlocal : ∀ᶠ z in 𝓝 x, |z| * ‖S‖ < 1 :=
    (continuous_abs.continuousAt.mul continuousAt_const).eventually (gt_mem_nhds hx)
  have hslope : slope (positiveObservableResolventResponse S u) x =ᶠ[𝓝[≠] x]
      (fun z : ℝ => inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u z)) := by
    filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzx
    have hne : z ≠ x := by simpa using hzx
    rw [slope_def_field]
    apply (div_eq_iff (sub_ne_zero.mpr hne)).2
    simpa only [mul_comm] using
      (positiveObservableResolventParityState_polarized S hS u x z hx hz).symm
  exact (hkernel.tendsto.mono_left nhdsWithin_le_nhds).congr' hslope.symm

/-- The effective diagonal kernel equality on the Neumann domain. -/
theorem positiveObservableResolventResponse_deriv_eq_inner
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (x : ℝ) (hx : |x| * ‖S‖ < 1) :
    deriv (positiveObservableResolventResponse S u) x =
      inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u x) :=
  (positiveObservableResolventResponse_hasDerivAt S hS u x hx).deriv

/-- In particular, the derivative on the real resolvent domain is nonnegative. -/
theorem positiveObservableResolventResponse_deriv_nonneg
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (x : ℝ) (hx : |x| * ‖S‖ < 1) :
    0 ≤ deriv (positiveObservableResolventResponse S u) x := by
  rw [positiveObservableResolventResponse_deriv_eq_inner S hS u x hx]
  exact real_inner_self_nonneg

/-- The complete local kernel identity includes the genuine derivative
on the diagonal, using the same state at each point. -/
theorem positiveObservableResolventParityState_inner_eq_dslope
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric)
    (u : H) (x z : ℝ) (hx : |x| * ‖S‖ < 1) (hz : |z| * ‖S‖ < 1) :
    inner ℝ (positiveObservableResolventParityState S u x)
        (positiveObservableResolventParityState S u z) =
      dslope (positiveObservableResolventResponse S u) x z := by
  by_cases hzx : z = x
  · subst z
    rw [dslope_same]
    exact (positiveObservableResolventResponse_deriv_eq_inner S hS u x hx).symm
  · rw [dslope_of_ne _ hzx, slope_def_field]
    apply (eq_div_iff (sub_ne_zero.mpr hzx)).2
    simpa only [mul_comm] using
      positiveObservableResolventParityState_polarized S hS u x z hx hz

/-- Every finite divided-difference section is positive semidefinite,
including repeated parameters and hence diagonal derivative entries. -/
theorem positiveObservableResolventResponse_dslope_posSemidef
    (S : H →L[ℝ] H) (hS : S.toLinearMap.IsSymmetric) (u : H)
    {index : Type*} [Fintype index] (point : index → ℝ)
    (hpoint : ∀ i, |point i| * ‖S‖ < 1) :
    (Matrix.of fun i j => dslope (positiveObservableResolventResponse S u)
      (point i) (point j)).PosSemidef := by
  have hmatrix :
      (Matrix.of fun i j => dslope (positiveObservableResolventResponse S u)
        (point i) (point j)) =
      Matrix.gram ℝ (fun i => positiveObservableResolventParityState S u (point i)) := by
    ext i j
    exact (positiveObservableResolventParityState_inner_eq_dslope S hS u
      (point i) (point j) (hpoint i) (hpoint j)).symm
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℝ _

end

end CarrySelfAdjointOperator
