import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import Mathlib.Tactic

/-!
# Canonical polarization of the full completed Wronskian operator

The full completed Wronskian operator is a skew-adjoint complex structure.
Multiplication by `-i` therefore turns it into a self-adjoint involution.  Its
two canonical polarizations split every Wronskian readout into the difference
of two honest Hilbert Gram channels.

This is an algebraic decomposition only.  It does not assume that either
polarization vanishes on the completed-native state family.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

noncomputable section

/-! ## Skew-adjointness -/

/-- The scalar boundary rotation is skew-adjoint. -/
theorem inner_completedScalarBoundarySymplecticRotation_left
    (x y : CompletedScalarBoundaryTraceCarrier) :
    inner ℂ (completedScalarBoundarySymplecticRotation x) y =
      -inner ℂ x (completedScalarBoundarySymplecticRotation y) := by
  rw [completedScalarBoundarySymplecticRotation_apply,
    completedScalarBoundarySymplecticRotation_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    inner ℂ (-x.snd) y.fst + inner ℂ x.fst y.snd =
      -(inner ℂ x.fst (-y.snd) + inner ℂ x.snd y.fst)
  rw [inner_neg_left, inner_neg_right]
  ring

/-- The crossed archimedean/chart complex structure is skew-adjoint. -/
theorem inner_canonicalCompletedC3ArchimedeanChartOperator_left
    (x y : CanonicalCompletedC3ArchimedeanChartOperatorCarrier) :
    inner ℂ (canonicalCompletedC3ArchimedeanChartOperator x) y =
      -inner ℂ x (canonicalCompletedC3ArchimedeanChartOperator y) := by
  rw [canonicalCompletedC3ArchimedeanChartOperator_apply,
    WithLp.prod_inner_apply,
    canonicalCompletedC3ArchimedeanChartOperator_inner]
  change
    inner ℂ (completedScalarBoundarySymplecticRotation x.fst) y.fst +
        inner ℂ (-completedScalarBoundarySymplecticRotation x.snd) y.snd =
      -(inner ℂ x.fst
          (completedScalarBoundarySymplecticRotation y.fst) -
        inner ℂ x.snd
          (completedScalarBoundarySymplecticRotation y.snd))
  rw [inner_neg_left,
    inner_completedScalarBoundarySymplecticRotation_left,
    inner_completedScalarBoundarySymplecticRotation_left]
  ring

/-- The full completed Wronskian operator is skew-adjoint. -/
theorem inner_canonicalCompletedC3FullWronskianOperator_left
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    inner ℂ (canonicalCompletedC3FullWronskianOperator x) y =
      -inner ℂ x (canonicalCompletedC3FullWronskianOperator y) := by
  rw [canonicalCompletedC3FullWronskianOperator_apply]
  change
    inner ℂ (completedScalarBoundarySymplecticRotation x.fst) y.fst +
        inner ℂ (canonicalCompletedC3ArchimedeanChartOperator x.snd) y.snd =
      -(inner ℂ x.fst (completedScalarBoundarySymplecticRotation y.fst) +
        inner ℂ x.snd (canonicalCompletedC3ArchimedeanChartOperator y.snd))
  rw [inner_completedScalarBoundarySymplecticRotation_left,
    inner_canonicalCompletedC3ArchimedeanChartOperator_left]
  ring

/-! ## Hermitian involution and its polarizations -/

/-- Hermitian involution obtained from the full symplectic operator by the
canonical quarter turn `H = -i T`. -/
def canonicalCompletedC3FullWronskianHermitianInvolution
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (-Complex.I) • canonicalCompletedC3FullWronskianOperator state

/-- The quarter-turned operator squares to the identity. -/
@[simp] theorem canonicalCompletedC3FullWronskianHermitianInvolution_sq
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianHermitianInvolution
        (canonicalCompletedC3FullWronskianHermitianInvolution state) =
      state := by
  unfold canonicalCompletedC3FullWronskianHermitianInvolution
  rw [map_smul, smul_smul,
    canonicalCompletedC3FullWronskianOperator_sq]
  simp

/-- The quarter-turned involution is Hermitian at the inner-product level. -/
theorem inner_canonicalCompletedC3FullWronskianHermitianInvolution_left
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    inner ℂ (canonicalCompletedC3FullWronskianHermitianInvolution x) y =
      inner ℂ x
        (canonicalCompletedC3FullWronskianHermitianInvolution y) := by
  unfold canonicalCompletedC3FullWronskianHermitianInvolution
  calc
    inner ℂ ((-Complex.I) • canonicalCompletedC3FullWronskianOperator x) y =
        (starRingEnd ℂ) (-Complex.I) *
          inner ℂ (canonicalCompletedC3FullWronskianOperator x) y := by
      rw [inner_smul_left]
    _ = Complex.I *
          (-inner ℂ x (canonicalCompletedC3FullWronskianOperator y)) := by
      rw [inner_canonicalCompletedC3FullWronskianOperator_left]
      congr 1
      norm_num [Complex.star_def]
    _ = inner ℂ x
          ((-Complex.I) • canonicalCompletedC3FullWronskianOperator y) := by
      rw [inner_smul_right]
      ring

/-- Positive-chirality polarization of the full Wronskian carrier. -/
def canonicalCompletedC3FullWronskianPositivePolarization
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (2 : ℂ)⁻¹ •
    (state + canonicalCompletedC3FullWronskianHermitianInvolution state)

/-- Negative-chirality polarization of the full Wronskian carrier. -/
def canonicalCompletedC3FullWronskianNegativePolarization
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (2 : ℂ)⁻¹ •
    (state - canonicalCompletedC3FullWronskianHermitianInvolution state)

/-- The two canonical polarizations reconstruct the original state. -/
theorem canonicalCompletedC3FullWronskianPolarization_add
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianPositivePolarization state +
        canonicalCompletedC3FullWronskianNegativePolarization state =
      state := by
  unfold canonicalCompletedC3FullWronskianPositivePolarization
    canonicalCompletedC3FullWronskianNegativePolarization
  module

/-- Positive and negative polarizations are orthogonal. -/
theorem inner_canonicalCompletedC3FullWronskianPolarizations_eq_zero
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    inner ℂ
        (canonicalCompletedC3FullWronskianPositivePolarization x)
        (canonicalCompletedC3FullWronskianNegativePolarization y) = 0 := by
  unfold canonicalCompletedC3FullWronskianPositivePolarization
    canonicalCompletedC3FullWronskianNegativePolarization
  simp only [inner_smul_left, inner_smul_right, inner_add_left,
    inner_sub_right]
  have hisometry :
      inner ℂ
          (canonicalCompletedC3FullWronskianHermitianInvolution x)
          (canonicalCompletedC3FullWronskianHermitianInvolution y) =
        inner ℂ x y := by
    rw [inner_canonicalCompletedC3FullWronskianHermitianInvolution_left,
      canonicalCompletedC3FullWronskianHermitianInvolution_sq]
  rw [inner_canonicalCompletedC3FullWronskianHermitianInvolution_left,
    hisometry]
  ring

/-- The original skew operator is the canonical quarter turn of its Hermitian
involution. -/
theorem canonicalCompletedC3FullWronskianOperator_eq_i_smul_involution
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianOperator state =
      Complex.I •
        canonicalCompletedC3FullWronskianHermitianInvolution state := by
  unfold canonicalCompletedC3FullWronskianHermitianInvolution
  rw [smul_smul]
  simp

/-- Exact polarization of the full Wronskian operator readout: the raw
symplectic form is `i` times positive Gram minus negative Gram. -/
theorem inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    inner ℂ x (canonicalCompletedC3FullWronskianOperator y) =
      Complex.I *
        (inner ℂ
            (canonicalCompletedC3FullWronskianPositivePolarization x)
            (canonicalCompletedC3FullWronskianPositivePolarization y) -
          inner ℂ
            (canonicalCompletedC3FullWronskianNegativePolarization x)
            (canonicalCompletedC3FullWronskianNegativePolarization y)) := by
  have hdiff :
      inner ℂ
          (canonicalCompletedC3FullWronskianPositivePolarization x)
          (canonicalCompletedC3FullWronskianPositivePolarization y) -
        inner ℂ
          (canonicalCompletedC3FullWronskianNegativePolarization x)
          (canonicalCompletedC3FullWronskianNegativePolarization y) =
      inner ℂ x
        (canonicalCompletedC3FullWronskianHermitianInvolution y) := by
    unfold canonicalCompletedC3FullWronskianPositivePolarization
      canonicalCompletedC3FullWronskianNegativePolarization
    simp only [inner_smul_left, inner_smul_right, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right]
    have hisometry :
        inner ℂ
            (canonicalCompletedC3FullWronskianHermitianInvolution x)
            (canonicalCompletedC3FullWronskianHermitianInvolution y) =
          inner ℂ x y := by
      rw [inner_canonicalCompletedC3FullWronskianHermitianInvolution_left,
        canonicalCompletedC3FullWronskianHermitianInvolution_sq]
    rw [inner_canonicalCompletedC3FullWronskianHermitianInvolution_left,
      hisometry]
    have hhalf :
        (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      norm_num [starRingEnd_apply, Complex.star_def]
    rw [hhalf]
    ring
  rw [canonicalCompletedC3FullWronskianOperator_eq_i_smul_involution,
    inner_smul_right, hdiff]

/-! ## Concrete completed C3 kernels -/

/-- The concrete full Wronskian kernel is the exact difference of its two
orthogonal polarized Gram kernels. -/
theorem canonicalCompletedC3FullWronskianOperatorKernel_eq_polarizationDifference
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3FullWronskianOperatorKernel M w z =
      Complex.I *
        (inner ℂ
            (canonicalCompletedC3FullWronskianPositivePolarization
              (canonicalCompletedC3FullWronskianOperatorState M w))
            (canonicalCompletedC3FullWronskianPositivePolarization
              (canonicalCompletedC3FullWronskianOperatorState M z)) -
          inner ℂ
            (canonicalCompletedC3FullWronskianNegativePolarization
              (canonicalCompletedC3FullWronskianOperatorState M w))
            (canonicalCompletedC3FullWronskianNegativePolarization
              (canonicalCompletedC3FullWronskianOperatorState M z))) := by
  exact
    inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference
      (canonicalCompletedC3FullWronskianOperatorState M w)
      (canonicalCompletedC3FullWronskianOperatorState M z)

/-- The same exact polarization after canonical removal of the chart weight. -/
theorem canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_polarizationDifference
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3NormalizedFullWronskianOperatorKernel M w z =
      Complex.I *
        (inner ℂ
            (canonicalCompletedC3FullWronskianPositivePolarization
              (canonicalCompletedC3NormalizedFullWronskianOperatorState M w))
            (canonicalCompletedC3FullWronskianPositivePolarization
              (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)) -
          inner ℂ
            (canonicalCompletedC3FullWronskianNegativePolarization
              (canonicalCompletedC3NormalizedFullWronskianOperatorState M w))
            (canonicalCompletedC3FullWronskianNegativePolarization
              (canonicalCompletedC3NormalizedFullWronskianOperatorState M z))) := by
  exact
    inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)

end

end CarrySelfAdjointOperator
