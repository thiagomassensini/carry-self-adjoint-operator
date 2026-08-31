import CarrySelfAdjointOperator.CompletedC3FullWronskianOperatorCarrier
import Mathlib.Analysis.InnerProductSpace.GramMatrix
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

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

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

/-- Pythagorean decomposition of the full carrier into its two orthogonal
chiralities.  This is the total Hilbert energy before the Wronskian readout
takes their signed difference. -/
theorem canonicalCompletedC3FullWronskianPolarization_norm_sq
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    ‖state‖ ^ 2 =
      ‖canonicalCompletedC3FullWronskianPositivePolarization state‖ ^ 2 +
        ‖canonicalCompletedC3FullWronskianNegativePolarization state‖ ^ 2 := by
  have horth :=
    inner_canonicalCompletedC3FullWronskianPolarizations_eq_zero state state
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (canonicalCompletedC3FullWronskianPositivePolarization state)
    (canonicalCompletedC3FullWronskianNegativePolarization state)
    horth
  rw [canonicalCompletedC3FullWronskianPolarization_add] at hpyth
  simpa [pow_two] using hpyth

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

/-- After the canonical quarter turn, the scalar Wronskian readout is the
signed difference of the two chiral energies. -/
theorem canonicalCompletedC3FullWronskian_chiralityBalance
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    ((-Complex.I) * inner ℂ state
      (canonicalCompletedC3FullWronskianOperator state)).re =
        ‖canonicalCompletedC3FullWronskianPositivePolarization state‖ ^ 2 -
          ‖canonicalCompletedC3FullWronskianNegativePolarization state‖ ^ 2 := by
  rw [inner_canonicalCompletedC3FullWronskianOperator_eq_polarizationDifference]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_pow]
  norm_cast

/-- A vanishing scalar readout means equality of the two chiral energies,
not vanishing of the underlying state. -/
theorem canonicalCompletedC3FullWronskian_chiralityBalance_eq_zero_iff
    (state : CanonicalCompletedC3FullWronskianOperatorCarrier) :
    ((-Complex.I) * inner ℂ state
        (canonicalCompletedC3FullWronskianOperator state)).re = 0 ↔
      ‖canonicalCompletedC3FullWronskianPositivePolarization state‖ ^ 2 =
        ‖canonicalCompletedC3FullWronskianNegativePolarization state‖ ^ 2 := by
  rw [canonicalCompletedC3FullWronskian_chiralityBalance]
  exact sub_eq_zero

/-- If the total state is nonzero while its scalar balance vanishes, both
orthogonal chiral channels carry strictly positive energy. -/
theorem canonicalCompletedC3FullWronskian_chiralEnergies_pos_of_balance_zero
    {state : CanonicalCompletedC3FullWronskianOperatorCarrier}
    (hstate : state ≠ 0)
    (hbalance :
      ((-Complex.I) * inner ℂ state
        (canonicalCompletedC3FullWronskianOperator state)).re = 0) :
    0 < ‖canonicalCompletedC3FullWronskianPositivePolarization state‖ ^ 2 ∧
      0 < ‖canonicalCompletedC3FullWronskianNegativePolarization state‖ ^ 2 := by
  have htotal : 0 < ‖state‖ ^ 2 := by
    have hnorm : 0 < ‖state‖ := norm_pos_iff.mpr hstate
    positivity
  have hsum := canonicalCompletedC3FullWronskianPolarization_norm_sq state
  have heq :=
    (canonicalCompletedC3FullWronskian_chiralityBalance_eq_zero_iff state).mp
      hbalance
  constructor <;> nlinarith

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

/-- At a zero of the completed characteristic, the normalized full state has
equal positive- and negative-chirality energies.  The scalar Wronskian
vanishes by balance of orthogonal channels; it does not assert that either
channel, or the uncollapsed ledger behind them, vanishes. -/
theorem
    canonicalCompletedC3NormalizedFullWronskian_chiralEnergies_eq_of_characteristicZero
    (M : ℕ) {z : ℂ}
    (hz : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    ‖canonicalCompletedC3FullWronskianPositivePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 =
      ‖canonicalCompletedC3FullWronskianNegativePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  apply
    (canonicalCompletedC3FullWronskian_chiralityBalance_eq_zero_iff
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)).mp
  have hreadout :
      inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)) =
        0 := by
    rw [← completedGreenWronskian_eq_normalizedFullOperatorInner M hz hz]
    simp [completedGreenWronskian, hzero]
  rw [hreadout]
  simp

/-! ## Chiral realization of the completed logarithmic response -/

/-- Canonical normalization shared by the two chiral channels.  Its square
produces exactly the factor `2 * F z * conj (F w)` occurring in the completed
normalized Wronskian response. -/
def canonicalCompletedC3FullWronskianChiralNormalization (z : ℂ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹

/-- Positive-chirality state after the characteristic normalization dictated
by the completed logarithmic response. -/
def canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    canonicalCompletedC3FullWronskianPositivePolarization
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)

/-- Negative-chirality state with the same canonical normalization. -/
def canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
    (M : ℕ) (z : ℂ) : CanonicalCompletedC3FullWronskianOperatorCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    canonicalCompletedC3FullWronskianNegativePolarization
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)

/-- Positive Gram channel of the normalized full Wronskian carrier. -/
def canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
    (M : ℕ) (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M w)
    (canonicalCompletedC3NormalizedFullWronskianPositiveChiralState M z)

/-- Negative Gram channel of the normalized full Wronskian carrier. -/
def canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
    (M : ℕ) (w z : ℂ) : ℂ :=
  inner ℂ
    (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M w)
    (canonicalCompletedC3NormalizedFullWronskianNegativeChiralState M z)

/-- Every finite sample of the positive chiral kernel is positive
semidefinite because it is literally a Hilbert Gram matrix. -/
theorem canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
        M (point i) (point j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
      M (point i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- Every finite sample of the negative chiral kernel is likewise positive
semidefinite. -/
theorem canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel_posSemidef
    {ι : Type*} [Finite ι] (M : ℕ) (point : ι → ℂ) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
        M (point i) (point j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
      M (point i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- After the exact characteristic normalization, the full Wronskian readout
is `i` times the difference of the two positive chiral Gram kernels.  This is
the precise location of the completed logarithmic-derivative information: it
is a signed chiral balance, not the norm of the unpolarized state. -/
theorem canonicalCompletedC3NormalizedFullWronskianKernel_div_eq_chiralDifference
    (M : ℕ) {w z : ℂ}
    (hw : completedNativeOperatorCharacteristic w ≠ 0)
    (hz : completedNativeOperatorCharacteristic z ≠ 0) :
    canonicalCompletedC3NormalizedFullWronskianOperatorKernel M w z /
          ((2 : ℂ) * completedNativeOperatorCharacteristic z *
            (starRingEnd ℂ) (completedNativeOperatorCharacteristic w)) =
      Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M w z -
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M w z) := by
  rw [canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_polarizationDifference]
  unfold canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
    canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
    canonicalCompletedC3NormalizedFullWronskianPositiveChiralState
    canonicalCompletedC3NormalizedFullWronskianNegativeChiralState
    canonicalCompletedC3FullWronskianChiralNormalization
  simp only [inner_smul_left, inner_smul_right, map_inv₀, map_mul,
    Complex.conj_ofReal]
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqrtComplex : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hsqrt
  have hstarW :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic w) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hw
  have hsqrtSq : ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp [hsqrtComplex, hz, hstarW]
  rw [hsqrtSq]

/-- Center-pinned signed chiral response. -/
def canonicalCompletedC3FullWronskianChiralBalanceResponse
    (M : ℕ) (z : ℂ) : ℂ :=
  Complex.I *
    (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M 0 z -
      canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M 0 z)

/-- Wherever the characteristic is nonzero, the center-pinned full operator
response is exactly its signed chiral balance. -/
theorem canonicalCompletedC3FullOperatorNormalizedResponse_eq_chiralBalance
    (M : ℕ) {z : ℂ}
    (hz : completedNativeOperatorCharacteristic z ≠ 0) :
    canonicalCompletedC3FullOperatorNormalizedResponse M z =
      canonicalCompletedC3FullWronskianChiralBalanceResponse M z := by
  exact canonicalCompletedC3NormalizedFullWronskianKernel_div_eq_chiralDifference
    M completedNativeOperatorCharacteristic_zero_ne_zero hz

/-- Near the center, the signed chiral balance is exactly the completed
normalized logarithmic response `-F'/(2F)`. -/
theorem canonicalCompletedC3FullWronskianChiralBalanceResponse_eventuallyEq_completed
    (M : ℕ) :
    canonicalCompletedC3FullWronskianChiralBalanceResponse M =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  have hbalance :
      canonicalCompletedC3FullWronskianChiralBalanceResponse M =ᶠ[nhds 0]
        canonicalCompletedC3FullOperatorNormalizedResponse M := by
    filter_upwards [hnonzero] with z hz
    exact (canonicalCompletedC3FullOperatorNormalizedResponse_eq_chiralBalance
      M hz).symm
  exact hbalance.trans
    (canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed M)

/-- Taylor coefficient of the signed chiral response. -/
def canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
    (M order : ℕ) : ℂ :=
  iteratedDeriv order
      (canonicalCompletedC3FullWronskianChiralBalanceResponse M) 0 /
    order.factorial

/-- Every signed chiral coefficient is the corresponding completed response
coefficient. -/
theorem canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient_eq_completed
    (M order : ℕ) :
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient M order =
      completedNativeGreenResponseTaylorCoefficient order := by
  unfold canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    (canonicalCompletedC3FullWronskianChiralBalanceResponse_eventuallyEq_completed M)]

/-- The odd Taylor coefficients of the signed chiral balance are exactly the
canonical completed-native logarithmic moments at every order. -/
theorem canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment
    (M n : ℕ) :
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- Every mixed derivative order of the chiral balance gives the corresponding
polarized canonical moment coefficient. -/
theorem canonicalCompletedC3FullWronskianChiralResponse_succ_eq_polarizedMoment
    (M p q : ℕ) :
    canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (p + q + 1) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized]

/-- At the central collision the removable `dslope` of the signed chiral
balance is exactly the zeroth completed-native logarithmic moment.  Thus the
central moment is a derivative of the signed balance, not the norm of the raw
unpolarized state. -/
theorem canonicalCompletedC3FullWronskianChiralBalance_dslope_zero_zero
    (M : ℕ) :
    dslope (canonicalCompletedC3FullWronskianChiralBalanceResponse M) 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [dslope_same]
  have h :=
    canonicalCompletedC3FullWronskianChiralResponse_odd_eq_canonicalMoment M 0
  simpa [canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient,
    iteratedDeriv_one] using h

end

end CarrySelfAdjointOperator
