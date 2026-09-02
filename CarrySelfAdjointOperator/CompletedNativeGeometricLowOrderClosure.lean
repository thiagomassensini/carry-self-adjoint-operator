import CarrySelfAdjointOperator.CompletedNativeXiCosineMomentHerglotzGate
import CarrySelfAdjointOperator.CompletedNativeCentralChiralVariation
import CarrySelfAdjointOperator.CompletedNativeChiralHankelDominance
import Mathlib.Tactic

/-!
# Geometric spelling of the unconditional low-order closure

The theta-tail argument proves positivity of the first two canonical
logarithmic moments.  The geometric construction had already identified
those same scalars with

* the first transverse variation of the signed central chiral energy;
* the first and third variations of the full Wronskian chiral signature; and
* the two one-dimensional expanded structural Loewner defects.

This file records the resulting unconditional geometric statements.  Its
dependency on `CompletedNativeXiCosineMomentHerglotzGate` is intentional and
visible: these are geometric realizations of the theorem proved by the theta
route, not a second theta-free proof.  A genuinely independent defect proof
would still have to realize the signed pre-scalarized difference as a positive
defect Gram, after the completion/product channels have been dressed.
-/

namespace CarrySelfAdjointOperator

open scoped ComplexOrder MatrixOrder

noncomputable section

/-- The first two completed-native moments are strictly positive.  This
private extraction keeps every geometric consequence below tied to the one
public unconditional low-order curvature theorem. -/
private theorem canonicalCompletedNativeFirstTwoMoments_pos :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 ∧
      0 < canonicalCompletedNativeLogDerivativeMoment 1 :=
  canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive

/-- Unconditional strict infinitesimal Hermite--Biehler dominance of the
central signed chiral energy. -/
theorem deriv_completedNativeCentralChiralEnergyDifference_zero_pos :
    0 < deriv completedNativeCentralChiralEnergyDifference 0 :=
  deriv_completedNativeCentralChiralEnergyDifference_zero_pos_iff.mpr
    canonicalCompletedNativeFirstTwoMoments_pos.1

/-- At every carrier cutoff, the first geometric chiral-signature variation
is strictly positive. -/
theorem canonicalCompletedC3ChiralBlockSignature_firstVariation_re_pos
    (M : ℕ) :
    0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re := by
  rw [canonicalCompletedC3ChiralBlockSignature_firstVariation_eq_moment_zero]
  simpa using canonicalCompletedNativeFirstTwoMoments_pos.1

/-- At every carrier cutoff, the third geometric chiral-signature variation
is strictly positive.  This is the geometric fourth-order-curvature
observable needed by the first polarized Herglotz section. -/
theorem canonicalCompletedC3ChiralBlockSignature_thirdVariation_re_pos
    (M : ℕ) :
    0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re := by
  rw [canonicalCompletedC3ChiralBlockSignature_thirdVariation_eq_moment_one]
  simpa using canonicalCompletedNativeFirstTwoMoments_pos.2

/-- The first and third chiral variations are simultaneously positive at
every cutoff. -/
theorem
    canonicalCompletedC3ChiralBlockSignature_firstAndThirdVariations_re_pos
    (M : ℕ) :
    0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re ∧
      0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re :=
  ⟨canonicalCompletedC3ChiralBlockSignature_firstVariation_re_pos M,
    canonicalCompletedC3ChiralBlockSignature_thirdVariation_re_pos M⟩

/-- The first nonempty even and shifted-odd geometric Loewner defects are
both positive definite. -/
theorem
    canonicalCompletedC3ExpandedStructuralLoewnerDefects_one_posDef :
    (canonicalCompletedC3ExpandedStructuralEvenLoewnerDefect 0 1).PosDef ∧
      (canonicalCompletedC3ExpandedStructuralOddLoewnerDefect 0 1).PosDef :=
  canonicalCompletedC3ExpandedStructuralStrictChiralDominance_one_iff.mpr
    canonicalCompletedNativeFirstTwoMoments_pos

/-- Geometric factorization of the already closed analytic gate: positivity
of the two chiral variations supplies the literal two-point radial Herglotz
section. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_geometricChiralVariations
    (M : ℕ)
    (hgeom :
      0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re ∧
        0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef := by
  apply
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
  exact
    (canonicalCompletedC3ChiralBlockSignature_firstAndThirdVariations_re_pos_iff_lowOrderHerglotzCurvature
      M).mp hgeom

/-- The same geometric low-order data supplies the two-point chiral Pick
section through the exact Cayley congruence. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_geometricChiralVariations
    (M : ℕ)
    (hgeom :
      0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1).re ∧
        0 < (canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3).re) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef := by
  apply
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
  exact
    (canonicalCompletedC3ChiralBlockSignature_firstAndThirdVariations_re_pos_iff_lowOrderHerglotzCurvature
      M).mp hgeom

end

end CarrySelfAdjointOperator
