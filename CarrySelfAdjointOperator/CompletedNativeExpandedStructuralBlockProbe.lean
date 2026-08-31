import CarrySelfAdjointOperator.CompletedNativeChiralBlockMomentProbe
import Mathlib.Tactic

/-!
# Expanded structural block probe for the completed-native moments

The full completed Wronskian state is assembled from four concrete channels:
the finite value/log-jet head, its exact completion tail, the xi-factor trace,
and the crossed C3-chart trace.  This module keeps those four channels
separate and then applies both canonical chiral polarizations.

The resulting eight-channel kernel is an honest Hilbert Gram block and is
therefore positive semidefinite.  Summing the four structural channels inside
each fixed chirality recovers the two chiral kernels already known to produce
the completed-native moments.  Consequently the scalar moment readout remains
the positive-chirality compression minus the negative-chirality compression.

No moment positivity, zero condition, spectral input, or confinement theorem
is used.
-/

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

noncomputable section

/-- Four concrete sources of the full completed Wronskian state. -/
inductive CanonicalCompletedC3StructuralChannel
  | head
  | tail
  | xiCompletion
  | chartCorrection
  deriving DecidableEq, Fintype

/-- Boundary trace carried by the finite head before exact tail completion. -/
def canonicalCompletedC3HeadBoundaryTraceState
    (M : ℕ) (z : ℂ) : CompletedScalarBoundaryTraceCarrier :=
  let state := canonicalCompletedC3AllCutoffOnePointState M z
  WithLp.toLp 2
    (Complex.I * state.logJetHead, state.valueHead)

/-- Boundary trace carried by the exact value/log-jet completion tail. -/
def canonicalCompletedC3TailBoundaryTraceState
    (M : ℕ) (z : ℂ) : CompletedScalarBoundaryTraceCarrier :=
  let state := canonicalCompletedC3AllCutoffOnePointState M z
  WithLp.toLp 2
    (Complex.I * state.logJetTail, state.valueTail)

/-- One unnormalized structural component, embedded in the same full carrier
as the completed Wronskian state. -/
def canonicalCompletedC3FullWronskianStructuralState
    (M : ℕ) (channel : CanonicalCompletedC3StructuralChannel) (z : ℂ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  match channel with
  | .head =>
      WithLp.toLp 2
        (nativeXiCompletionFactor z •
            canonicalCompletedC3HeadBoundaryTraceState M z,
          0)
  | .tail =>
      WithLp.toLp 2
        (nativeXiCompletionFactor z •
            canonicalCompletedC3TailBoundaryTraceState M z,
          0)
  | .xiCompletion =>
      WithLp.toLp 2
        (0, WithLp.toLp 2
          ((canonicalCompletedC3ArchimedeanChartOperatorState z).fst, 0))
  | .chartCorrection =>
      WithLp.toLp 2
        (0, WithLp.toLp 2
          (0, (canonicalCompletedC3ArchimedeanChartOperatorState z).snd))

/-- Explicit synthesis of the four structural channels. -/
def canonicalCompletedC3StructuralSynthesis
    {H : Type*} [Add H]
    (state : CanonicalCompletedC3StructuralChannel → H) : H :=
  state .head + state .tail + state .xiCompletion + state .chartCorrection

/-- Fintype summation over the four structural labels is the explicit
synthesis above. -/
theorem sum_canonicalCompletedC3StructuralChannel_eq_synthesis
    {H : Type*} [AddCommMonoid H]
    (state : CanonicalCompletedC3StructuralChannel → H) :
    ∑ channel, state channel =
      canonicalCompletedC3StructuralSynthesis state := by
  classical
  rw [show (Finset.univ : Finset CanonicalCompletedC3StructuralChannel) =
      {.head, .tail, .xiCompletion, .chartCorrection} by decide]
  simp [canonicalCompletedC3StructuralSynthesis]
  ac_rfl

/-- Head and tail reconstruct the completed scalar trace, while the two
crossed product-rule channels reconstruct the archimedean/chart block. -/
theorem canonicalCompletedC3FullWronskianStructuralState_synthesis
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3StructuralSynthesis
        (canonicalCompletedC3FullWronskianStructuralState M · z) =
      canonicalCompletedC3FullWronskianOperatorState M z := by
  unfold canonicalCompletedC3StructuralSynthesis
    canonicalCompletedC3FullWronskianStructuralState
    canonicalCompletedC3FullWronskianOperatorState
    canonicalCompletedC3HeadBoundaryTraceState
    canonicalCompletedC3TailBoundaryTraceState
  rw [canonicalCompletedC3OnePointCompletedTraceProjection_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    apply Prod.ext <;>
      simp [CanonicalCompletedC3AllCutoffOnePointHilbert.completedCompanion,
        CanonicalCompletedC3AllCutoffOnePointHilbert.completedValue]
    <;> ring
  · apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp

/-- The same four-way decomposition after canonical chart normalization. -/
def canonicalCompletedC3NormalizedFullWronskianStructuralState
    (M : ℕ) (channel : CanonicalCompletedC3StructuralChannel) (z : ℂ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  (canonicalC3ChartFactorHeight z)⁻¹ •
    canonicalCompletedC3FullWronskianStructuralState M channel z

/-- Structural synthesis commutes with the common chart normalization. -/
theorem canonicalCompletedC3NormalizedFullWronskianStructuralState_synthesis
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3StructuralSynthesis
        (canonicalCompletedC3NormalizedFullWronskianStructuralState M · z) =
      canonicalCompletedC3NormalizedFullWronskianOperatorState M z := by
  unfold canonicalCompletedC3StructuralSynthesis
    canonicalCompletedC3NormalizedFullWronskianStructuralState
    canonicalCompletedC3NormalizedFullWronskianOperatorState
  rw [← smul_add, ← smul_add, ← smul_add]
  congr 1
  exact canonicalCompletedC3FullWronskianStructuralState_synthesis M z

/-- One structural component after projection to a fixed chirality and the
normalization used by the completed logarithmic response. -/
def canonicalCompletedC3ExpandedStructuralChiralState
    (M : ℕ) (structural : CanonicalCompletedC3StructuralChannel)
    (chiral : CanonicalCompletedC3ChiralChannel) (z : ℂ) :
    CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    match chiral with
    | .positive =>
        canonicalCompletedC3FullWronskianPositivePolarization
          (canonicalCompletedC3NormalizedFullWronskianStructuralState
            M structural z)
    | .negative =>
        canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianStructuralState
            M structural z)

/-- The positive polarization is additive. -/
theorem canonicalCompletedC3FullWronskianPositivePolarization_add
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianPositivePolarization (x + y) =
      canonicalCompletedC3FullWronskianPositivePolarization x +
        canonicalCompletedC3FullWronskianPositivePolarization y := by
  unfold canonicalCompletedC3FullWronskianPositivePolarization
    canonicalCompletedC3FullWronskianHermitianInvolution
  simp only [map_add]
  module

/-- The negative polarization is additive. -/
theorem canonicalCompletedC3FullWronskianNegativePolarization_add
    (x y : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    canonicalCompletedC3FullWronskianNegativePolarization (x + y) =
      canonicalCompletedC3FullWronskianNegativePolarization x +
        canonicalCompletedC3FullWronskianNegativePolarization y := by
  unfold canonicalCompletedC3FullWronskianNegativePolarization
    canonicalCompletedC3FullWronskianHermitianInvolution
  simp only [map_add]
  module

/-- Summing all four structural sources inside one chirality recovers the
pre-existing normalized chiral state exactly. -/
theorem canonicalCompletedC3ExpandedStructuralChiralState_synthesis
    (M : ℕ) (chiral : CanonicalCompletedC3ChiralChannel) (z : ℂ) :
    canonicalCompletedC3StructuralSynthesis
        (fun structural =>
          canonicalCompletedC3ExpandedStructuralChiralState
            M structural chiral z) =
      canonicalCompletedC3NormalizedFullWronskianChiralState M chiral z := by
  cases chiral with
  | positive =>
      have hs :=
        canonicalCompletedC3NormalizedFullWronskianStructuralState_synthesis
          M z
      unfold canonicalCompletedC3StructuralSynthesis at hs
      unfold canonicalCompletedC3StructuralSynthesis
        canonicalCompletedC3ExpandedStructuralChiralState
        canonicalCompletedC3NormalizedFullWronskianChiralState
        canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
      rw [← smul_add, ← smul_add, ← smul_add]
      rw [← canonicalCompletedC3FullWronskianPositivePolarization_add,
        ← canonicalCompletedC3FullWronskianPositivePolarization_add,
        ← canonicalCompletedC3FullWronskianPositivePolarization_add]
      rw [hs]
  | negative =>
      have hs :=
        canonicalCompletedC3NormalizedFullWronskianStructuralState_synthesis
          M z
      unfold canonicalCompletedC3StructuralSynthesis at hs
      unfold canonicalCompletedC3StructuralSynthesis
        canonicalCompletedC3ExpandedStructuralChiralState
        canonicalCompletedC3NormalizedFullWronskianChiralState
        canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
      rw [← smul_add, ← smul_add, ← smul_add]
      rw [← canonicalCompletedC3FullWronskianNegativePolarization_add,
        ← canonicalCompletedC3FullWronskianNegativePolarization_add,
        ← canonicalCompletedC3FullWronskianNegativePolarization_add]
      rw [hs]

/-- Index of the expanded four-structural-by-two-chiral block. -/
abbrev CanonicalCompletedC3ExpandedStructuralChiralIndex :=
  CanonicalCompletedC3StructuralChannel × CanonicalCompletedC3ChiralChannel

/-- Eight-channel Gram block: four structural sources times two
chiralities. -/
def canonicalCompletedC3ExpandedStructuralChiralBlockKernel
    (M : ℕ) (w z : ℂ) :
    Matrix
      CanonicalCompletedC3ExpandedStructuralChiralIndex
      CanonicalCompletedC3ExpandedStructuralChiralIndex ℂ :=
  fun left right =>
    inner ℂ
      (canonicalCompletedC3ExpandedStructuralChiralState
        M left.1 left.2 w)
      (canonicalCompletedC3ExpandedStructuralChiralState
        M right.1 right.2 z)

/-- Every finite point/channel sample of the expanded block is positive
semidefinite because it is one uncollapsed Hilbert Gram matrix. -/
theorem canonicalCompletedC3ExpandedStructuralChiralBlockKernel_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    Matrix.PosSemidef ((fun
          (left right : ι × CanonicalCompletedC3ExpandedStructuralChiralIndex) =>
        canonicalCompletedC3ExpandedStructuralChiralBlockKernel
          M (point left.1) (point right.1) left.2 right.2) :
        Matrix (ι × CanonicalCompletedC3ExpandedStructuralChiralIndex)
          (ι × CanonicalCompletedC3ExpandedStructuralChiralIndex) ℂ) := by
  change (Matrix.gram ℂ
    (fun index : ι × CanonicalCompletedC3ExpandedStructuralChiralIndex =>
      canonicalCompletedC3ExpandedStructuralChiralState
        M index.2.1 index.2.2 (point index.1))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- Opposite chiralities are orthogonal even before structural synthesis. -/
@[simp] theorem
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel_positive_negative
    (M : ℕ) (w z : ℂ)
    (left right : CanonicalCompletedC3StructuralChannel) :
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel M w z
        (left, .positive) (right, .negative) = 0 := by
  unfold canonicalCompletedC3ExpandedStructuralChiralBlockKernel
    canonicalCompletedC3ExpandedStructuralChiralState
  simp only [inner_smul_left, inner_smul_right]
  rw [inner_canonicalCompletedC3FullWronskianPolarizations_eq_zero]
  simp

/-- Reverse opposite-chirality entries vanish as well. -/
@[simp] theorem
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel_negative_positive
    (M : ℕ) (w z : ℂ)
    (left right : CanonicalCompletedC3StructuralChannel) :
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel M w z
        (left, .negative) (right, .positive) = 0 := by
  change inner ℂ
      (canonicalCompletedC3ExpandedStructuralChiralState
        M left .negative w)
      (canonicalCompletedC3ExpandedStructuralChiralState
        M right .positive z) = 0
  have hcross : inner ℂ
      (canonicalCompletedC3ExpandedStructuralChiralState
        M right .positive z)
      (canonicalCompletedC3ExpandedStructuralChiralState
        M left .negative w) = 0 := by
    exact
      canonicalCompletedC3ExpandedStructuralChiralBlockKernel_positive_negative
        M z w right left
  calc
    _ = (starRingEnd ℂ)
        (inner ℂ
          (canonicalCompletedC3ExpandedStructuralChiralState
            M right .positive z)
          (canonicalCompletedC3ExpandedStructuralChiralState
            M left .negative w)) :=
      (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) 0 := by rw [hcross]
    _ = 0 := map_zero (starRingEnd ℂ)

/-- Compression of one fixed chirality along the all-ones structural vector.
This keeps all head-tail and product-rule cross terms. -/
def canonicalCompletedC3ExpandedStructuralChiralCompression
    (block : Matrix
      CanonicalCompletedC3ExpandedStructuralChiralIndex
      CanonicalCompletedC3ExpandedStructuralChiralIndex ℂ)
    (chiral : CanonicalCompletedC3ChiralChannel) : ℂ :=
  ∑ left : CanonicalCompletedC3StructuralChannel,
    ∑ right : CanonicalCompletedC3StructuralChannel,
      block (left, chiral) (right, chiral)

/-- The positive structural compression is exactly the old positive chiral
kernel, now with every structural cross term displayed inside the block. -/
theorem
    canonicalCompletedC3ExpandedStructuralChiralCompression_positive_eq
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3ExpandedStructuralChiralCompression
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M w z)
        .positive =
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
        M w z := by
  unfold canonicalCompletedC3ExpandedStructuralChiralCompression
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel
    canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
  calc
    (∑ left, ∑ right,
        inner ℂ
          (canonicalCompletedC3ExpandedStructuralChiralState
            M left .positive w)
          (canonicalCompletedC3ExpandedStructuralChiralState
            M right .positive z)) =
        inner ℂ
          (∑ left, canonicalCompletedC3ExpandedStructuralChiralState
            M left .positive w)
          (∑ right, canonicalCompletedC3ExpandedStructuralChiralState
            M right .positive z) := by
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]
    _ = inner ℂ
        (canonicalCompletedC3StructuralSynthesis
          (fun structural =>
            canonicalCompletedC3ExpandedStructuralChiralState
              M structural .positive w))
        (canonicalCompletedC3StructuralSynthesis
          (fun structural =>
            canonicalCompletedC3ExpandedStructuralChiralState
              M structural .positive z)) := by
      rw [sum_canonicalCompletedC3StructuralChannel_eq_synthesis,
        sum_canonicalCompletedC3StructuralChannel_eq_synthesis]
    _ = _ := by
      rw [canonicalCompletedC3ExpandedStructuralChiralState_synthesis,
        canonicalCompletedC3ExpandedStructuralChiralState_synthesis]
      rfl

/-- The negative structural compression is exactly the old negative chiral
kernel. -/
theorem
    canonicalCompletedC3ExpandedStructuralChiralCompression_negative_eq
    (M : ℕ) (w z : ℂ) :
    canonicalCompletedC3ExpandedStructuralChiralCompression
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M w z)
        .negative =
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
        M w z := by
  unfold canonicalCompletedC3ExpandedStructuralChiralCompression
    canonicalCompletedC3ExpandedStructuralChiralBlockKernel
    canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
  calc
    (∑ left, ∑ right,
        inner ℂ
          (canonicalCompletedC3ExpandedStructuralChiralState
            M left .negative w)
          (canonicalCompletedC3ExpandedStructuralChiralState
            M right .negative z)) =
        inner ℂ
          (∑ left, canonicalCompletedC3ExpandedStructuralChiralState
            M left .negative w)
          (∑ right, canonicalCompletedC3ExpandedStructuralChiralState
            M right .negative z) := by
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]
    _ = inner ℂ
        (canonicalCompletedC3StructuralSynthesis
          (fun structural =>
            canonicalCompletedC3ExpandedStructuralChiralState
              M structural .negative w))
        (canonicalCompletedC3StructuralSynthesis
          (fun structural =>
            canonicalCompletedC3ExpandedStructuralChiralState
              M structural .negative z)) := by
      rw [sum_canonicalCompletedC3StructuralChannel_eq_synthesis,
        sum_canonicalCompletedC3StructuralChannel_eq_synthesis]
    _ = _ := by
      rw [canonicalCompletedC3ExpandedStructuralChiralState_synthesis,
        canonicalCompletedC3ExpandedStructuralChiralState_synthesis]
      rfl

/-- Each fixed-chirality structural compression is positive on the
diagonal. -/
theorem
    canonicalCompletedC3ExpandedStructuralChiralCompression_diagonal_re_nonneg
    (M : ℕ) (z : ℂ) (chiral : CanonicalCompletedC3ChiralChannel) :
    0 ≤ (canonicalCompletedC3ExpandedStructuralChiralCompression
      (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M z z)
      chiral).re := by
  cases chiral with
  | positive =>
      rw [canonicalCompletedC3ExpandedStructuralChiralCompression_positive_eq]
      unfold canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
      exact inner_self_nonneg (𝕜 := ℂ)
        (x := canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
          M z)
  | negative =>
      rw [canonicalCompletedC3ExpandedStructuralChiralCompression_negative_eq]
      unfold canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
      exact inner_self_nonneg (𝕜 := ℂ)
        (x := canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
          M z)

/-- Scalar readout selected by the full Wronskian operator after every
structural cross term has been retained. -/
def canonicalCompletedC3ExpandedStructuralSignatureReadout
    (block : Matrix
      CanonicalCompletedC3ExpandedStructuralChiralIndex
      CanonicalCompletedC3ExpandedStructuralChiralIndex ℂ) : ℂ :=
  canonicalCompletedC3ExpandedStructuralChiralCompression block .positive -
    canonicalCompletedC3ExpandedStructuralChiralCompression block .negative

/-- Positivity of the scalar structural signature is exactly dominance of
the positive compression over the negative compression.  It is not implied
by positivity of the expanded Gram block itself. -/
theorem
    canonicalCompletedC3ExpandedStructuralSignatureReadout_diagonal_re_nonneg_iff
    (M : ℕ) (z : ℂ) :
    0 ≤ (canonicalCompletedC3ExpandedStructuralSignatureReadout
      (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M z z)).re ↔
      (canonicalCompletedC3ExpandedStructuralChiralCompression
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M z z)
        .negative).re ≤
      (canonicalCompletedC3ExpandedStructuralChiralCompression
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M z z)
        .positive).re := by
  unfold canonicalCompletedC3ExpandedStructuralSignatureReadout
  rw [Complex.sub_re]
  exact sub_nonneg

/-- Structural enlargement does not turn the completed response into the
positive trace of the block: its exact readout remains the chiral signature. -/
theorem canonicalCompletedC3FullWronskianChiralBalanceResponse_eq_expandedSignature
    (M : ℕ) (z : ℂ) :
    canonicalCompletedC3FullWronskianChiralBalanceResponse M z =
      Complex.I * canonicalCompletedC3ExpandedStructuralSignatureReadout
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M 0 z) := by
  rw [canonicalCompletedC3FullWronskianChiralBalanceResponse]
  unfold canonicalCompletedC3ExpandedStructuralSignatureReadout
  rw [canonicalCompletedC3ExpandedStructuralChiralCompression_positive_eq,
    canonicalCompletedC3ExpandedStructuralChiralCompression_negative_eq]

/-- Taylor coefficient of the expanded structural signature response. -/
def canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
    (M order : ℕ) : ℂ :=
  iteratedDeriv order
      (fun z => Complex.I *
        canonicalCompletedC3ExpandedStructuralSignatureReadout
          (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M 0 z)) 0 /
    order.factorial

/-- Every odd coefficient of the fully expanded structural block is the
corresponding completed-native logarithmic moment. -/
theorem canonicalCompletedC3ExpandedStructuralSignature_odd_eq_canonicalMoment
    (M n : ℕ) :
    canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
        M (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  unfold canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
  rw [show (fun z => Complex.I *
      canonicalCompletedC3ExpandedStructuralSignatureReadout
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M 0 z)) =
      canonicalCompletedC3FullWronskianChiralBalanceResponse M by
    funext z
    exact
      (canonicalCompletedC3FullWronskianChiralBalanceResponse_eq_expandedSignature
        M z).symm]
  exact canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment
    M n

/-- The zeroth canonical moment is already a signed compression of the
expanded positive block. -/
theorem
    canonicalCompletedC3ExpandedStructuralSignature_firstVariation_eq_moment_zero
    (M : ℕ) :
    canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient M 1 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa using
    canonicalCompletedC3ExpandedStructuralSignature_odd_eq_canonicalMoment M 0

/-- At every polarized order, the same expanded signature supplies the
canonical moment coefficient. -/
theorem canonicalCompletedC3ExpandedStructuralSignature_succ_eq_polarizedMoment
    (M p q : ℕ) :
    canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
        M (p + q + 1) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  unfold canonicalCompletedC3ExpandedStructuralSignatureTaylorCoefficient
  rw [show (fun z => Complex.I *
      canonicalCompletedC3ExpandedStructuralSignatureReadout
        (canonicalCompletedC3ExpandedStructuralChiralBlockKernel M 0 z)) =
      canonicalCompletedC3FullWronskianChiralBalanceResponse M by
    funext z
    exact
      (canonicalCompletedC3FullWronskianChiralBalanceResponse_eq_expandedSignature
        M z).symm]
  exact canonicalCompletedC3FullWronskianChiralResponse_succ_eq_polarizedMoment
    M p q

end

end CarrySelfAdjointOperator
