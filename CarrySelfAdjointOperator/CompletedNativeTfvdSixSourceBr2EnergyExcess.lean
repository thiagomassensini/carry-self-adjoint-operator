import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceCenterLegBridge
import CarrySelfAdjointOperator.ProjectiveValveMomentFrontier
import Mathlib.Tactic

/-!
# Positive-orientation audit for the literal BR2 center--leg seam

The six-source coefficient is already fixed by the completed TFVD ledger.
For a literal BR2 projective jet, this file reverses the sign of the old
center--leg defect:

`E(i,j) = <B_i,B_j> - C₆(i,j)`.

Thus `E` is an actual excess of the BR2 Hilbert Gram over the completed
six-source coefficient, not a moment-defined replacement carrier.  The
order-zero C3 entry is computed exactly and is strictly positive.  The finite
two- and three-vector calculations below make the next PSD obligation
explicit: on the literal C3 samples the BR2 Gram is `6 I`, whereas the
subtracted term is the existing canonical Hankel moment matrix.

No corrected all-order jet, compression, or HP certificate is asserted here:
the operator upper bound `H_N ≤ 6 I` is now proved unconditionally in
`CompletedNativeSixFrameUpperBound`, using the existing canonical theta
representation and recurrence. A compatible geometric realization of the
defect factor remains open; a target-defined Gram factor is not such a
realization.
-/

open scoped ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The positive orientation of the literal BR2 center--leg discrepancy:
the actual projective-Hilbert Gram minus the already synthesized six-source
coefficient. -/
def nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) : ℂ :=
  inner ℂ (br2CameraBracketProjectiveHilbertParityJet base radius i)
    (br2CameraBracketProjectiveHilbertParityJet base radius j) -
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
      M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j)

/-- The positive orientation is exactly the negative of the prior explicit
center--leg defect.  This is a sign change only; it preserves all source,
provenance, and projective-Hilbert data. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_neg_centerLegDefect
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hq0 hq1 S base radius i j =
      -nativeC3SeededClockTfvdSixSourceCenterLegDefect
        M q hq0 hq1 S base radius i j := by
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    nativeC3SeededClockTfvdSixSourceCenterLegDefect
  ring

/-- Equivalently, the genuine six-source coefficient is the literal BR2
Gram after subtracting the positive-oriented excess. -/
theorem nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_br2Gram_sub_energyExcess
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) :
    nativeC3SeededClockTfvdSixSourceCenterLegCoefficient
        M q hq0 hq1 S (parityJetNumber i) (parityJetNumber j) =
      inner ℂ (br2CameraBracketProjectiveHilbertParityJet base radius i)
        (br2CameraBracketProjectiveHilbertParityJet base radius j) -
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hq0 hq1 S base radius i j := by
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
  ring

/-- After the completed six-source coefficient identification, the excess is
the literal projective Gram minus the canonical polarized Green coefficient.
No moment data have been used to define the BR2 vectors. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius : ℕ) (i j : ℕ ⊕ ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S base radius i j =
      inner ℂ (br2CameraBracketProjectiveHilbertParityJet base radius i)
        (br2CameraBracketProjectiveHilbertParityJet base radius j) -
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment
        (parityJetNumber i) (parityJetNumber j) := by
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
  rw [nativeC3SeededClockTfvdSixSourceCenterLegCoefficient_eq_polarizedGreenMomentCoefficient
    M q hqpos hq1 S]

/-! ## Exact C3 order-zero energy and its scalar factor -/

/-- The order-zero positive orientation before evaluating the literal C3
stencil. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_even_zero_even_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (base radius : ℕ) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S base radius (Sum.inl 0) (Sum.inl 0) =
      inner ℂ
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
          (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0)) -
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_neg_centerLegDefect,
    nativeC3SeededClockTfvdSixSourceCenterLegDefect_even_zero_even_zero
      M q hqpos hq1 S base]
  ring

/-- Every supported literal BR2 order-zero entry has strictly positive
energy excess over the six-source coefficient.  The order is read in the
real Hilbert metric; the complex formulation is its standard complexification.
-/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_even_zero_re_pos_of_supported
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : IsSupported base)
    (hradius : radius ∈ radiusSet base) :
    0 < (nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S base radius (Sum.inl 0) (Sum.inl 0)).re := by
  letI : InnerProductSpace ℝ CanonicalCompletedTfvdGreenHilbertCarrier :=
    InnerProductSpace.rclikeToReal ℂ _
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_even_zero_even_zero
    M q hqpos hq1 S base, Complex.sub_re, Complex.ofReal_re]
  have hstrict := br2CameraBracketProjectiveHilbertParityJet_zeroGram_gt_nativeMoment
    hbase hradius
  have hstrict' : canonicalCompletedNativeLogDerivativeMoment 0 <
      (inner ℂ
        (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))
        (br2CameraBracketProjectiveHilbertParityJet base radius (Sum.inl 0))).re := by
    simpa only [Matrix.gram, Matrix.of_apply, real_inner_eq_re_inner,
      RCLike.re_eq_complex_re] using hstrict
  linarith

/-- The literal C3 stencil has exact order-zero BR2 energy `6`; hence the
actual scalar energy excess is `6 - h₀`. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_eq_six_sub_h0
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S 3 1 (Sum.inl 0) (Sum.inl 0) =
      ((6 - canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_even_zero_even_zero
    M q hqpos hq1 S 3]
  change inner ℂ (br2CameraBracketVerticalState 3 1 0)
      (br2CameraBracketVerticalState 3 1 0) -
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) = _
  simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
    lp.inner_single_left]
  norm_num

/-- The real scalar in the C3 order-zero excess is strictly positive.  The
gap is quantitative: `h₀ < 1/16`, so in particular `6 - h₀ > 0`. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_scalar_pos :
    0 < 6 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h0 := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- The complex C3 order-zero excess has strictly positive real part. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_re_pos
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    0 < (nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S 3 1 (Sum.inl 0) (Sum.inl 0)).re := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_eq_six_sub_h0
    M q hqpos hq1 S]
  simp only [Complex.ofReal_re]
  exact nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_scalar_pos

/-- The canonical nonnegative scalar factor of the first literal BR2 energy
excess.  It factors the actual excess, not a fitted moment target. -/
def nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor : ℝ :=
  Real.sqrt (6 - canonicalCompletedNativeLogDerivativeMoment 0)

/-- First exact defect factorization: at C3 order zero, `E₀₀ = Z* Z` with
`Z = sqrt (6 - h₀)`.  This is a one-dimensional PSD certificate only; it is
not promoted to a fabricated all-order compression. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor_sq :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor ^ 2 =
      6 - canonicalCompletedNativeLogDerivativeMoment 0 := by
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor
  exact Real.sq_sqrt
    (nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_scalar_pos.le)

/-- Complex `Z*Z` form of the first exact excess factorization.  It uses the
literal C3 BR2 energy calculated above, so it supplies no target-defined
correction vector. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factorization
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
        M q hqpos.le hq1 S 3 1 (Sum.inl 0) (Sum.inl 0) =
      star ((nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor : ℝ) : ℂ) *
        ((nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor : ℝ) : ℂ) := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_eq_six_sub_h0
    M q hqpos hq1 S]
  have hfactor :
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor *
          nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor =
        6 - canonicalCompletedNativeLogDerivativeMoment 0 := by
    simpa [pow_two] using
      nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor_sq
  rw [show star ((nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor : ℝ) : ℂ) =
      ((nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_factor : ℝ) : ℂ) by simp,
    ← Complex.ofReal_mul, hfactor]

/-! ## Literal finite C3 blocks -/

/-- The literal even/even restriction of the energy excess. -/
def nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    M q hq0 hq1 S 3 1 (Sum.inl i) (Sum.inl j)

/-- The literal odd/odd restriction of the energy excess. -/
def nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    M q hq0 hq1 S 3 1 (Sum.inr i) (Sum.inr j)

/-- The literal even/odd restriction of the energy excess. -/
def nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => nativeC3SeededClockTfvdSixSourceBr2EnergyExcess
    M q hq0 hq1 S 3 1 (Sum.inl i) (Sum.inr j)

/-- The first restricted energy matrix (one even C3 coordinate) is positive
semidefinite.  This is the matrix form of the certified scalar `Z*Z`
factorization, and is intentionally not extrapolated to larger blocks. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_one_posSemidef
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
      M q hqpos.le hq1 S 1).PosSemidef := by
  have hmatrix : nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
      M q hqpos.le hq1 S 1 =
      Matrix.diagonal (fun _ : Fin 1 =>
        ((6 - canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock,
      Matrix.diagonal_apply_eq]
    exact nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_eq_six_sub_h0
      M q hqpos hq1 S
  rw [hmatrix, Matrix.posSemidef_diagonal_iff]
  intro i
  rw [Complex.nonneg_iff]
  exact ⟨nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_c3_even_zero_scalar_pos.le,
    by simp⟩

private theorem c3_raw_even_three
    (i j : Fin 3) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ))) =
      if i = j then 6 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

private theorem c3_raw_odd_three
    (i j : Fin 3) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ) + 1))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) =
      if i = j then 6 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

private theorem c3_raw_cross_three
    (i j : Fin 3) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

private theorem c3_raw_even_two
    (i j : Fin 2) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ))) =
      if i = j then 6 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

private theorem c3_raw_odd_two
    (i j : Fin 2) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ) + 1))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) =
      if i = j then 6 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

private theorem c3_raw_cross_two
    (i j : Fin 2) :
    inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [br2CameraBracketVerticalState, inner_add_left, inner_add_right,
      lp.inner_single_left] <;> norm_num

/-- Exact even C3 block through order two: the BR2 part is `6 I` and the
subtracted material part is the existing unshifted Hankel array. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_three_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
        M q hqpos.le hq1 S 3 =
      fun (i j : Fin 3) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ)) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ))) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ)) (2 * (j : ℕ)) = _
  rw [c3_raw_even_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Exact odd C3 block through order two: it is `6 I` minus the existing
shifted Hankel array. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_oddBlock_three_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
        M q hqpos.le hq1 S 3 =
      fun (i j : Fin 3) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ) + 1) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ) + 1))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1) = _
  rw [c3_raw_odd_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Exact C3 cross-parity block through order two.  Both the literal BR2
Gram and the canonical polarized coefficient vanish on these samples. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_crossBlock_three_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
        M q hqpos.le hq1 S 3 = 0 := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ)) (2 * (j : ℕ) + 1) = 0
  rw [c3_raw_cross_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Exact even `2 × 2` test.  This is the leading principal literal C3
block: `6 I` minus the first `2 × 2` unshifted Hankel block. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_two_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
        M q hqpos.le hq1 S 2 =
      fun (i j : Fin 2) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ)) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ))) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ)) (2 * (j : ℕ)) = _
  rw [c3_raw_even_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Exact odd `2 × 2` test: the leading literal C3 odd block is `6 I` minus
the first shifted Hankel block. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_oddBlock_two_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
        M q hqpos.le hq1 S 2 =
      fun (i j : Fin 2) => (if i = j then 6 else 0) -
        (canonicalCompletedNativeLogDerivativeMoment ((i : ℕ) + (j : ℕ) + 1) : ℂ) := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessOddBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ) + 1))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1) = _
  rw [c3_raw_odd_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Exact cross-parity `2 × 2` test.  The literal BR2 Gram and the canonical
polarized coefficient both vanish at all four displayed entries. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_crossBlock_two_eq_zero
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
        M q hqpos.le hq1 S 2 = 0 := by
  ext i j
  unfold nativeC3SeededClockTfvdSixSourceBr2EnergyExcessCrossBlock
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_eq_projectiveMinusPolarizedGreen
    M q hqpos hq1 S]
  change inner ℂ (br2CameraBracketVerticalState 3 1 (2 * (i : ℕ)))
      (br2CameraBracketVerticalState 3 1 (2 * (j : ℕ) + 1)) -
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment
        (2 * (i : ℕ)) (2 * (j : ℕ) + 1) = 0
  rw [c3_raw_cross_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient]

/-- Determinant of the explicitly tested even `2 × 2` block.  Its
nonnegativity is the first Schur gate required by a PSD factorization of the
literal excess. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_two_det_eq
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
      M q hqpos.le hq1 S 2).det =
      ((6 - canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) *
        ((6 - canonicalCompletedNativeLogDerivativeMoment 2 : ℝ) : ℂ) -
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ^ 2 := by
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_two_eq
    M q hqpos hq1 S, Matrix.det_fin_two]
  norm_num [pow_two]

/-- Any PSD proof for the exact even `2 × 2` literal excess must discharge
this displayed Schur inequality.  It is recorded as a necessary condition,
not assumed as a new moment bound. -/
theorem nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_two_posSemidef_implies_schur
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (hpsd : (nativeC3SeededClockTfvdSixSourceBr2EnergyExcessEvenBlock
      M q hqpos.le hq1 S 2).PosSemidef) :
    (canonicalCompletedNativeLogDerivativeMoment 1) ^ 2 ≤
      (6 - canonicalCompletedNativeLogDerivativeMoment 0) *
        (6 - canonicalCompletedNativeLogDerivativeMoment 2) := by
  have hdet := hpsd.det_nonneg
  rw [nativeC3SeededClockTfvdSixSourceBr2EnergyExcess_evenBlock_two_det_eq
    M q hqpos hq1 S] at hdet
  have hreal := (Complex.nonneg_iff.mp hdet).1
  norm_num [Complex.mul_re, pow_two] at hreal
  linarith

/-! The finite formulas above deliberately stop before an all-order PSD or
compression claim.  The missing next theorem is a geometrically realized
upper frame bound for the *existing* native Hankel blocks,
`hankelGram h N ≤ 6 I` (and its shifted counterpart) for the C3 literal
blocks; neither strict Hankel
positivity nor the unrelated return/Naimark variance factorization supplies
that inequality or a map from its carrier to the literal BR2 jet. -/

end

end CarrySelfAdjointOperator
