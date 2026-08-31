import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization

/-!
# Completed-native chiral block moment probe

This file keeps the two Hilbert-positive chiral channels separate and records
the exact scalar readout used by the completed-native moments.  The full block
kernel is positive semidefinite, but the logarithmic response is obtained from
its diagonal by the signature `(+1, -1)`, followed by the canonical quarter
turn.  Thus block positivity alone does not identify the scalar moment kernel
with a positive compression or a Schur complement.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

noncomputable section

/-- The two canonical eigenspaces of the quarter-turned full Wronskian
operator. -/
inductive CanonicalCompletedC3ChiralChannel
  | positive
  | negative
  deriving DecidableEq, Fintype

/-- The normalized full Wronskian state in one fixed chiral channel. -/
def canonicalCompletedC3NormalizedFullWronskianChiralState
    (M : ℕ) (channel : CanonicalCompletedC3ChiralChannel) (z : ℂ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  match channel with
  | .positive =>
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z
  | .negative =>
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z

/-- The uncollapsed two-channel Gram kernel. -/
def canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel
    (M : ℕ) (w z : ℂ) :
    Matrix CanonicalCompletedC3ChiralChannel
      CanonicalCompletedC3ChiralChannel ℂ :=
  fun left right =>
    inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianChiralState M left w)
      (canonicalCompletedC3NormalizedFullWronskianChiralState M right z)

@[simp] theorem
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_positive_positive
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M w z
        .positive .positive =
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M w z :=
  rfl

@[simp] theorem
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_negative_negative
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M w z
        .negative .negative =
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M w z :=
  rfl

/-- Orthogonality is retained after the common characteristic
normalization. -/
@[simp] theorem
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_positive_negative
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M w z
        .positive .negative = 0 := by
  change inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M w)
      (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z) = 0
  unfold
    canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
    canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
  simp only [inner_smul_left, inner_smul_right]
  rw [inner_canonicalCompletedC3FullWronskianPolarizations_eq_zero]
  simp

/-- The reverse mixed block vanishes as well. -/
@[simp] theorem
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_negative_positive
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M w z
        .negative .positive = 0 := by
  change inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M w)
      (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z) = 0
  have hcross :
      inner ℂ
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z)
        (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M w) = 0 := by
    change canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M z w
      .positive .negative = 0
    exact
      canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_positive_negative
        M z w
  calc
    _ = (starRingEnd ℂ) (inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z)
          (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M w)) :=
      (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) 0 := by
      rw [hcross]
    _ = 0 := map_zero (starRingEnd ℂ)

/-- Every finite point/channel sample of the complete block kernel is one
Hilbert Gram matrix and is therefore positive semidefinite. -/
theorem canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    Matrix.PosSemidef ((fun (left right : ι × CanonicalCompletedC3ChiralChannel) =>
      canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel
        M (point left.1) (point right.1) left.2 right.2) :
      Matrix (ι × CanonicalCompletedC3ChiralChannel)
        (ι × CanonicalCompletedC3ChiralChannel) ℂ) := by
  change (Matrix.gram ℂ (fun index : ι × CanonicalCompletedC3ChiralChannel =>
    canonicalCompletedC3NormalizedFullWronskianChiralState
      M index.2 (point index.1))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- The scalar functional selected by the Hermitian involution: positive
diagonal minus negative diagonal. -/
def canonicalCompletedC3ChiralSignatureReadout
    (block : Matrix CanonicalCompletedC3ChiralChannel
      CanonicalCompletedC3ChiralChannel ℂ) : ℂ :=
  block .positive .positive - block .negative .negative

@[simp] theorem
    canonicalCompletedC3ChiralSignatureReadout_blockKernel
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3ChiralSignatureReadout
        (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M w z) =
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M w z -
        canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M w z :=
  rfl

/-- The completed logarithmic response is a signed block readout, not the
positive trace of the block. -/
theorem canonicalCompletedC3FullWronskianChiralBalanceResponse_eq_blockSignature
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3FullWronskianChiralBalanceResponse M z =
      Complex.I * canonicalCompletedC3ChiralSignatureReadout
        (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M 0 z) :=
  rfl

/-- On the diagonal, the signature readout is exactly the difference of the
two squared chiral norms. -/
theorem canonicalCompletedC3ChiralSignatureReadout_diagonal_re
    (M : ℕ) (z : ℂ) :
    (canonicalCompletedC3ChiralSignatureReadout
      (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M z z)).re =
        ‖canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z‖ ^ 2 -
          ‖canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z‖ ^ 2 := by
  change (inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z)
      (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z) -
    inner ℂ
      (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z)
      (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z)).re = _
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.ofReal_re, Complex.ofReal_pow]
  norm_cast

/-- Consequently, positivity of the scalar signature is precisely a dominance
statement between the two positive channels; it does not follow from the
positive semidefiniteness of their block Gram matrix. -/
theorem canonicalCompletedC3ChiralSignatureReadout_diagonal_re_nonneg_iff
    (M : ℕ) (z : ℂ) :
    0 ≤ (canonicalCompletedC3ChiralSignatureReadout
      (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M z z)).re ↔
      ‖canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z‖ ^ 2 ≤
        ‖canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z‖ ^ 2 := by
  rw [canonicalCompletedC3ChiralSignatureReadout_diagonal_re]
  exact sub_nonneg

/-- Taylor coefficient of the quarter-turned signature readout. -/
def canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient
    (M order : ℕ) : ℂ :=
  iteratedDeriv order
      (fun z => Complex.I * canonicalCompletedC3ChiralSignatureReadout
        (canonicalCompletedC3NormalizedFullWronskianChiralBlockKernel M 0 z)) 0 /
    order.factorial

/-- The block-signature coefficient is definitionally the previously
identified signed chiral response coefficient. -/
theorem canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient_eq_response
    (M order : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M order =
      canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient M order := by
  rfl

/-- At every odd order, the signature readout returns the canonical
completed-native logarithmic moment. -/
theorem canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment
    (M n : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient_eq_response]
  exact canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment M n

/-- Low-order probe: the first variation is `h₀`. -/
theorem canonicalCompletedC3ChiralBlockSignature_firstVariation_eq_moment_zero
    (M : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 1 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa using
    canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment M 0

/-- Low-order probe: the third variation is `h₁`. -/
theorem canonicalCompletedC3ChiralBlockSignature_thirdVariation_eq_moment_one
    (M : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M 3 =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  simpa using
    canonicalCompletedC3ChiralBlockSignature_odd_eq_canonicalMoment M 1

/-- The same signed block readout supplies every polarized moment coefficient,
not merely the first two probes. -/
theorem canonicalCompletedC3ChiralBlockSignature_succ_eq_polarizedMoment
    (M p q : ℕ) :
    canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient M (p + q + 1) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [canonicalCompletedC3ChiralBlockSignatureTaylorCoefficient_eq_response]
  exact canonicalCompletedC3FullWronskianChiralResponse_succ_eq_polarizedMoment M p q

end

end CarrySelfAdjointOperator
