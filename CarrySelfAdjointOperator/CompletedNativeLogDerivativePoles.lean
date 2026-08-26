import CarrySelfAdjointOperator.GlobalKernelProbe
import Mathlib.Analysis.Meromorphic.Order

/-!
# Poles of the completed native logarithmic derivative

This file records the global analytic half of the native height construction.
Inside the natural centered-height domain, every zero of the completed native
characteristic is a pole of its concrete logarithmic derivative.  Multiplicity
is retained in the characteristic and cancels in the quotient exactly enough
to leave meromorphic order `-1`.

No zero list, prime hypothesis, Euler product, or classical zeta comparison is
used here.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

/-- Global logarithmic derivative of the actual completed native
characteristic.  This is distinct from the local even-coordinate germ used by
the moment construction. -/
def completedNativeOperatorLogDerivative (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z /
    completedNativeOperatorCharacteristic z

/-- The completed native characteristic is not identically zero in any
neighborhood of a point of its natural centered-height domain. -/
theorem completedNativeOperatorCharacteristic_not_eventually_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    ¬ ∀ᶠ w in nhds z, completedNativeOperatorCharacteristic w = 0 := by
  have hclosure :=
    completedNativeHeightDomain_subset_closure_nonzeroLocus hz
  rw [mem_closure_iff_frequently] at hclosure
  intro hzero
  exact hclosure (hzero.mono fun w hw hnonzero => hnonzero.2 hw)

/-- The analytic order of the completed native characteristic is finite at
every point of its natural domain. -/
theorem completedNativeOperatorCharacteristic_analyticOrderAt_ne_top
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    analyticOrderAt completedNativeOperatorCharacteristic z ≠ ⊤ := by
  intro htop
  exact completedNativeOperatorCharacteristic_not_eventually_zero hz
    (analyticOrderAt_eq_top.mp htop)

/-- A zero of the completed native characteristic has a positive finite
analytic multiplicity. -/
theorem completedNativeOperatorCharacteristic_analyticOrderNatAt_ne_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    analyticOrderNatAt completedNativeOperatorCharacteristic z ≠ 0 := by
  have hfinite :=
    completedNativeOperatorCharacteristic_analyticOrderAt_ne_top hz
  have hpositive :
      analyticOrderAt completedNativeOperatorCharacteristic z ≠ 0 :=
    (completedNativeOperatorCharacteristic_analyticAt hz).analyticOrderAt_ne_zero.mpr
      hzero
  intro hn
  apply hpositive
  rw [← Nat.cast_analyticOrderNatAt hfinite, hn]
  simp

/-- Every completed native zero is a simple pole of the logarithmic
derivative, independently of the zero's multiplicity in the characteristic. -/
theorem completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    meromorphicOrderAt completedNativeOperatorLogDerivative z =
      ((-1 : ℤ) : WithTop ℤ) := by
  let n := analyticOrderNatAt completedNativeOperatorCharacteristic z
  have hf := completedNativeOperatorCharacteristic_analyticAt hz
  have hfinite :=
    completedNativeOperatorCharacteristic_analyticOrderAt_ne_top hz
  have hn : n ≠ 0 :=
    completedNativeOperatorCharacteristic_analyticOrderNatAt_ne_zero hz hzero
  have hanalyticOrder :
      analyticOrderAt completedNativeOperatorCharacteristic z = (n : ℕ∞) := by
    exact (Nat.cast_analyticOrderNatAt hfinite).symm
  have hmeromorphicOrder :
      meromorphicOrderAt completedNativeOperatorCharacteristic z =
        ((n : ℤ) : WithTop ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hanalyticOrder]
    simp
  have hnComplex : ((n : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast hn
  have hderivOrder :
      meromorphicOrderAt (deriv completedNativeOperatorCharacteristic) z =
        (((n : ℤ) - 1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_deriv_eq_sub_one hnComplex hmeromorphicOrder
  have hnegDerivOrder :
      meromorphicOrderAt
          (-deriv completedNativeOperatorCharacteristic) z =
        (((n : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [← meromorphicOrderAt_neg]
    exact hderivOrder
  change meromorphicOrderAt
      ((-deriv completedNativeOperatorCharacteristic) /
        completedNativeOperatorCharacteristic) z =
      ((-1 : ℤ) : WithTop ℤ)
  rw [meromorphicOrderAt_div hf.deriv.neg.meromorphicAt hf.meromorphicAt,
    hnegDerivOrder, hmeromorphicOrder]
  change (((n : ℤ) - 1 - (n : ℤ) : ℤ) : WithTop ℤ) =
    ((-1 : ℤ) : WithTop ℤ)
  congr 1
  ring

/-- Exact zero--pole identification on the natural centered-height domain.
The forward implication uses analyticity at a nonzero characteristic value;
the reverse implication is the order computation above. -/
theorem completedNativeOperatorLogDerivative_meromorphicOrderAt_neg_iff_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    meromorphicOrderAt completedNativeOperatorLogDerivative z < 0 ↔
      completedNativeOperatorCharacteristic z = 0 := by
  constructor
  · intro hpole
    by_contra hnonzero
    have hf := completedNativeOperatorCharacteristic_analyticAt hz
    have hlog : AnalyticAt ℂ completedNativeOperatorLogDerivative z := by
      change AnalyticAt ℂ
        ((-deriv completedNativeOperatorCharacteristic) /
          completedNativeOperatorCharacteristic) z
      exact hf.deriv.neg.div hf hnonzero
    exact (not_lt_of_ge hlog.meromorphicOrderAt_nonneg) hpole
  · intro hzero
    rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
      hz hzero]
    show ((-1 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
    exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

/-- Equivalent exact form: the completed native logarithmic derivative has
meromorphic order `-1` precisely at completed native zeros. -/
theorem completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one_iff_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain) :
    meromorphicOrderAt completedNativeOperatorLogDerivative z =
        ((-1 : ℤ) : WithTop ℤ) ↔
      completedNativeOperatorCharacteristic z = 0 := by
  constructor
  · intro horder
    rw [← completedNativeOperatorLogDerivative_meromorphicOrderAt_neg_iff_zero hz]
    rw [horder]
    show ((-1 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
    exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
  · exact completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one hz

/-- Analytic formulation of the pole statement: approaching a completed
native zero through the punctured plane makes the logarithmic derivative
escape every bounded set. -/
theorem completedNativeOperatorLogDerivative_tendsto_cobounded_at_zero
    {z : ℂ} (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    Tendsto completedNativeOperatorLogDerivative (nhdsWithin z {z}ᶜ)
      (Bornology.cobounded ℂ) := by
  apply tendsto_cobounded_of_meromorphicOrderAt_neg
  rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one hz hzero]
  show ((-1 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ)
  exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

end

end CarrySelfAdjointOperator
