import CarrySelfAdjointOperator.CompletedC3FullWronskianChiralDslope
import CarrySelfAdjointOperator.CompletedNativeProductMomentCenter
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Scalar Hermite--Biehler coordinates of the completed boundary trace

The full completed C3 carrier proves that the logarithmic response is a signed
chiral balance.  This module expands the underlying two-coordinate boundary
pair before any geometric channels are recombined.  For a trace `(Psi, F)`,
the two chiral coordinates are exactly

`Psi + i F` and `Psi - i F`.

For the completed native pair `Psi = -F'`, these become the concrete
Hermite--Biehler candidates `-F' + i F` and `-F' - i F`.  The resulting
identities are algebraic and division-free until the final characteristic
normalization.  No positivity or zero-set hypothesis is introduced.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Scalar chiral coordinates -/

/-- Hermitian involution obtained from the scalar boundary quarter turn. -/
def completedScalarBoundaryHermitianInvolution
    (state : CompletedScalarBoundaryTraceCarrier) :
    CompletedScalarBoundaryTraceCarrier :=
  (-Complex.I) • completedScalarBoundarySymplecticRotation state

/-- Positive chirality of a scalar boundary trace. -/
def completedScalarBoundaryPositivePolarization
    (state : CompletedScalarBoundaryTraceCarrier) :
    CompletedScalarBoundaryTraceCarrier :=
  (2 : ℂ)⁻¹ • (state + completedScalarBoundaryHermitianInvolution state)

/-- Negative chirality of a scalar boundary trace. -/
def completedScalarBoundaryNegativePolarization
    (state : CompletedScalarBoundaryTraceCarrier) :
    CompletedScalarBoundaryTraceCarrier :=
  (2 : ℂ)⁻¹ • (state - completedScalarBoundaryHermitianInvolution state)

/-- One-dimensional coordinate carried by the positive polarization. -/
def completedScalarBoundaryPositiveCombination
    (state : CompletedScalarBoundaryTraceCarrier) : ℂ :=
  state.fst + Complex.I * state.snd

/-- One-dimensional coordinate carried by the negative polarization. -/
def completedScalarBoundaryNegativeCombination
    (state : CompletedScalarBoundaryTraceCarrier) : ℂ :=
  state.fst - Complex.I * state.snd

@[simp] theorem completedScalarBoundaryPositivePolarization_apply
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundaryPositivePolarization state =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * (state.fst + Complex.I * state.snd),
          (2 : ℂ)⁻¹ * (state.snd - Complex.I * state.fst)) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [completedScalarBoundaryPositivePolarization,
      completedScalarBoundaryHermitianInvolution,
      completedScalarBoundarySymplecticRotation_apply] <;>
    ring

@[simp] theorem completedScalarBoundaryNegativePolarization_apply
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundaryNegativePolarization state =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * (state.fst - Complex.I * state.snd),
          (2 : ℂ)⁻¹ * (state.snd + Complex.I * state.fst)) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;>
    simp [completedScalarBoundaryNegativePolarization,
      completedScalarBoundaryHermitianInvolution,
      completedScalarBoundarySymplecticRotation_apply] <;>
    ring

/-- The positive two-coordinate polarization is a duplicated copy of
`Psi + i F`, with its forced quarter-turn in the second coordinate. -/
theorem completedScalarBoundaryPositivePolarization_eq_combination
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundaryPositivePolarization state =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * completedScalarBoundaryPositiveCombination state,
          (-Complex.I) * (2 : ℂ)⁻¹ *
            completedScalarBoundaryPositiveCombination state) := by
  rw [completedScalarBoundaryPositivePolarization_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp [completedScalarBoundaryPositiveCombination]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The negative two-coordinate polarization is a duplicated copy of
`Psi - i F`, with the opposite forced quarter-turn. -/
theorem completedScalarBoundaryNegativePolarization_eq_combination
    (state : CompletedScalarBoundaryTraceCarrier) :
    completedScalarBoundaryNegativePolarization state =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * completedScalarBoundaryNegativeCombination state,
          Complex.I * (2 : ℂ)⁻¹ *
            completedScalarBoundaryNegativeCombination state) := by
  rw [completedScalarBoundaryNegativePolarization_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp [completedScalarBoundaryNegativeCombination]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Positive chiral Gram is one half of the scalar combination Gram. -/
theorem inner_completedScalarBoundaryPositivePolarization
    (x y : CompletedScalarBoundaryTraceCarrier) :
    inner ℂ
        (completedScalarBoundaryPositivePolarization x)
        (completedScalarBoundaryPositivePolarization y) =
      (2 : ℂ)⁻¹ * inner ℂ
        (completedScalarBoundaryPositiveCombination x)
        (completedScalarBoundaryPositiveCombination y) := by
  rw [completedScalarBoundaryPositivePolarization_eq_combination,
    completedScalarBoundaryPositivePolarization_eq_combination,
    WithLp.prod_inner_apply]
  simp only [RCLike.inner_apply, map_mul, map_inv₀, map_neg,
    Complex.conj_I]
  simp only [map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Negative chiral Gram is one half of the scalar combination Gram. -/
theorem inner_completedScalarBoundaryNegativePolarization
    (x y : CompletedScalarBoundaryTraceCarrier) :
    inner ℂ
        (completedScalarBoundaryNegativePolarization x)
        (completedScalarBoundaryNegativePolarization y) =
      (2 : ℂ)⁻¹ * inner ℂ
        (completedScalarBoundaryNegativeCombination x)
        (completedScalarBoundaryNegativeCombination y) := by
  rw [completedScalarBoundaryNegativePolarization_eq_combination,
    completedScalarBoundaryNegativePolarization_eq_combination,
    WithLp.prod_inner_apply]
  simp only [RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_I]
  simp only [map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact positive-polarization norm: no information is lost when the two
coordinates are compressed to `Psi + iF`. -/
theorem norm_sq_completedScalarBoundaryPositivePolarization
    (state : CompletedScalarBoundaryTraceCarrier) :
    ‖completedScalarBoundaryPositivePolarization state‖ ^ 2 =
      (2 : ℝ)⁻¹ * ‖completedScalarBoundaryPositiveCombination state‖ ^ 2 := by
  have h := inner_completedScalarBoundaryPositivePolarization state state
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- Exact negative-polarization norm. -/
theorem norm_sq_completedScalarBoundaryNegativePolarization
    (state : CompletedScalarBoundaryTraceCarrier) :
    ‖completedScalarBoundaryNegativePolarization state‖ ^ 2 =
      (2 : ℝ)⁻¹ * ‖completedScalarBoundaryNegativeCombination state‖ ^ 2 := by
  have h := inner_completedScalarBoundaryNegativePolarization state state
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- Scalar Wronskian readout as the signed difference of its two one-dimensional
chiral Gram channels. -/
theorem inner_completedScalarBoundarySymplecticRotation_eq_chiralDifference
    (x y : CompletedScalarBoundaryTraceCarrier) :
    inner ℂ x (completedScalarBoundarySymplecticRotation y) =
      Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization x)
            (completedScalarBoundaryPositivePolarization y) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization x)
            (completedScalarBoundaryNegativePolarization y)) := by
  rw [completedScalarBoundarySymplecticRotation_apply,
    completedScalarBoundaryPositivePolarization_apply,
    completedScalarBoundaryPositivePolarization_apply,
    completedScalarBoundaryNegativePolarization_apply,
    completedScalarBoundaryNegativePolarization_apply]
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, map_mul, map_inv₀,
    map_add, map_sub, Complex.conj_I]
  simp only [map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  rfl

/-! ## The completed pair `(F, -F')` -/

/-- Completed native value/companion pair in the scalar boundary carrier. -/
def completedNativeFNegFPrimeBoundaryTraceState (z : ℂ) :
    CompletedScalarBoundaryTraceCarrier :=
  completedScalarBoundaryTraceState
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion z

/-- Positive Hermite--Biehler coordinate of the completed native trace. -/
def completedNativePositiveHermiteBiehlerCoordinate (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z +
    Complex.I * completedNativeOperatorCharacteristic z

/-- Negative Hermite--Biehler coordinate of the completed native trace. -/
def completedNativeNegativeHermiteBiehlerCoordinate (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z -
    Complex.I * completedNativeOperatorCharacteristic z

@[simp] theorem completedNativeFNegFPrime_positiveCombination
    (z : ℂ) :
    completedScalarBoundaryPositiveCombination
        (completedNativeFNegFPrimeBoundaryTraceState z) =
      completedNativePositiveHermiteBiehlerCoordinate z := by
  simp [completedNativeFNegFPrimeBoundaryTraceState,
    completedScalarBoundaryPositiveCombination,
    completedScalarBoundaryTraceState,
    completedNativePositiveHermiteBiehlerCoordinate,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

@[simp] theorem completedNativeFNegFPrime_negativeCombination
    (z : ℂ) :
    completedScalarBoundaryNegativeCombination
        (completedNativeFNegFPrimeBoundaryTraceState z) =
      completedNativeNegativeHermiteBiehlerCoordinate z := by
  simp [completedNativeFNegFPrimeBoundaryTraceState,
    completedScalarBoundaryNegativeCombination,
    completedScalarBoundaryTraceState,
    completedNativeNegativeHermiteBiehlerCoordinate,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

/-- The positive polarization of `(F,-F')` contains exactly `-F' + iF`. -/
theorem completedNativeFNegFPrime_positivePolarization_eq
    (z : ℂ) :
    completedScalarBoundaryPositivePolarization
        (completedNativeFNegFPrimeBoundaryTraceState z) =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * completedNativePositiveHermiteBiehlerCoordinate z,
          (-Complex.I) * (2 : ℂ)⁻¹ *
            completedNativePositiveHermiteBiehlerCoordinate z) := by
  rw [completedScalarBoundaryPositivePolarization_eq_combination,
    completedNativeFNegFPrime_positiveCombination]

/-- The negative polarization of `(F,-F')` contains exactly `-F' - iF`. -/
theorem completedNativeFNegFPrime_negativePolarization_eq
    (z : ℂ) :
    completedScalarBoundaryNegativePolarization
        (completedNativeFNegFPrimeBoundaryTraceState z) =
      WithLp.toLp 2
        ((2 : ℂ)⁻¹ * completedNativeNegativeHermiteBiehlerCoordinate z,
          Complex.I * (2 : ℂ)⁻¹ *
            completedNativeNegativeHermiteBiehlerCoordinate z) := by
  rw [completedScalarBoundaryNegativePolarization_eq_combination,
    completedNativeFNegFPrime_negativeCombination]

/-! ## Characteristic-normalized scalar chiral kernels -/

/-- Positive scalar chiral state with the exact completed characteristic
normalization. -/
def completedNativeNormalizedPositiveChiralTraceState (z : ℂ) :
    CompletedScalarBoundaryTraceCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    completedScalarBoundaryPositivePolarization
      (completedNativeFNegFPrimeBoundaryTraceState z)

/-- Negative scalar chiral state with the same normalization. -/
def completedNativeNormalizedNegativeChiralTraceState (z : ℂ) :
    CompletedScalarBoundaryTraceCarrier :=
  canonicalCompletedC3FullWronskianChiralNormalization z •
    completedScalarBoundaryNegativePolarization
      (completedNativeFNegFPrimeBoundaryTraceState z)

/-- Positive scalar Hermite--Biehler Gram channel. -/
def completedNativeNormalizedPositiveChiralTraceKernel (z w : ℂ) : ℂ :=
  inner ℂ
    (completedNativeNormalizedPositiveChiralTraceState z)
    (completedNativeNormalizedPositiveChiralTraceState w)

/-- Negative scalar Hermite--Biehler Gram channel. -/
def completedNativeNormalizedNegativeChiralTraceKernel (z w : ℂ) : ℂ :=
  inner ℂ
    (completedNativeNormalizedNegativeChiralTraceState z)
    (completedNativeNormalizedNegativeChiralTraceState w)

/-- Exact normalized positive-channel energy in scalar coordinates. -/
theorem norm_sq_completedNativeNormalizedPositiveChiralTraceState
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    ‖completedNativeNormalizedPositiveChiralTraceState z‖ ^ 2 =
      ‖completedNativePositiveHermiteBiehlerCoordinate z‖ ^ 2 /
        (4 * ‖completedNativeOperatorCharacteristic z‖ ^ 2) := by
  unfold completedNativeNormalizedPositiveChiralTraceState
  rw [norm_smul, mul_pow,
    norm_sq_completedScalarBoundaryPositivePolarization,
    completedNativeFNegFPrime_positiveCombination]
  unfold canonicalCompletedC3FullWronskianChiralNormalization
  rw [norm_inv, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hF : ‖completedNativeOperatorCharacteristic z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hzF
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt, hF]
  rw [hsqrtSq]
  ring

/-- Exact normalized negative-channel energy in scalar coordinates. -/
theorem norm_sq_completedNativeNormalizedNegativeChiralTraceState
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    ‖completedNativeNormalizedNegativeChiralTraceState z‖ ^ 2 =
      ‖completedNativeNegativeHermiteBiehlerCoordinate z‖ ^ 2 /
        (4 * ‖completedNativeOperatorCharacteristic z‖ ^ 2) := by
  unfold completedNativeNormalizedNegativeChiralTraceState
  rw [norm_smul, mul_pow,
    norm_sq_completedScalarBoundaryNegativePolarization,
    completedNativeFNegFPrime_negativeCombination]
  unfold canonicalCompletedC3FullWronskianChiralNormalization
  rw [norm_inv, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hF : ‖completedNativeOperatorCharacteristic z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hzF
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt, hF]
  rw [hsqrtSq]
  ring

/-- Every finite positive scalar chiral Gram is positive semidefinite. -/
theorem completedNativeNormalizedPositiveChiralTraceKernel_posSemidef
    {ι : Type*} [Finite ι] (point : ι → ℂ) :
    (Matrix.of fun i j =>
      completedNativeNormalizedPositiveChiralTraceKernel
        (point i) (point j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    completedNativeNormalizedPositiveChiralTraceState (point i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- Every finite negative scalar chiral Gram is positive semidefinite. -/
theorem completedNativeNormalizedNegativeChiralTraceKernel_posSemidef
    {ι : Type*} [Finite ι] (point : ι → ℂ) :
    (Matrix.of fun i j =>
      completedNativeNormalizedNegativeChiralTraceKernel
        (point i) (point j)).PosSemidef := by
  change (Matrix.gram ℂ (fun i =>
    completedNativeNormalizedNegativeChiralTraceState (point i))).PosSemidef
  exact Matrix.posSemidef_gram ℂ _

/-- Generic scalar Wronskian as the signed chiral Gram difference. -/
theorem completedGreenWronskian_eq_scalarChiralDifference
    (F Psi : ℂ → ℂ) (z w : ℂ) :
    completedGreenWronskian F Psi z w =
      Complex.I *
        (inner ℂ
            (completedScalarBoundaryPositivePolarization
              (completedScalarBoundaryTraceState F Psi w))
            (completedScalarBoundaryPositivePolarization
              (completedScalarBoundaryTraceState F Psi z)) -
          inner ℂ
            (completedScalarBoundaryNegativePolarization
              (completedScalarBoundaryTraceState F Psi w))
            (completedScalarBoundaryNegativePolarization
              (completedScalarBoundaryTraceState F Psi z))) := by
  rw [completedGreenWronskian_eq_boundarySymplecticInner]
  exact inner_completedScalarBoundarySymplecticRotation_eq_chiralDifference
    (completedScalarBoundaryTraceState F Psi w)
    (completedScalarBoundaryTraceState F Psi z)

/-- Exact scalar analogue of the full-carrier characteristic normalization. -/
theorem completedNativeScalarWronskian_div_eq_chiralDifference
    {z w : ℂ}
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z /
        ((2 : ℂ) * completedNativeOperatorCharacteristic w *
          (starRingEnd ℂ) (completedNativeOperatorCharacteristic z)) =
      Complex.I *
        (completedNativeNormalizedPositiveChiralTraceKernel z w -
          completedNativeNormalizedNegativeChiralTraceKernel z w) := by
  rw [completedGreenWronskian_eq_scalarChiralDifference]
  unfold completedNativeNormalizedPositiveChiralTraceKernel
    completedNativeNormalizedNegativeChiralTraceKernel
    completedNativeNormalizedPositiveChiralTraceState
    completedNativeNormalizedNegativeChiralTraceState
    completedNativeFNegFPrimeBoundaryTraceState
    canonicalCompletedC3FullWronskianChiralNormalization
  simp only [inner_smul_left, inner_smul_right, map_inv₀, map_mul,
    Complex.conj_ofReal]
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqrtComplex : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsqrt
  have hstarZ :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hsqrtSq : ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp [hsqrtComplex, hwF, hstarZ]
  rw [hsqrtSq]

/-- After the exact characteristic normalization, the scalar signed chiral
difference is the Hermitian-polarized completed logarithmic response. -/
theorem completedNativeScalarChiralDifference_eq_polarizedResponseNumerator
    {z w : ℂ}
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    Complex.I *
        (completedNativeNormalizedPositiveChiralTraceKernel z w -
          completedNativeNormalizedNegativeChiralTraceKernel z w) =
      canonicalCompletedNativePolarizedResponseNumerator z w := by
  have hstarZ :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  rw [← completedNativeScalarWronskian_div_eq_chiralDifference hzF hwF]
  rw [completedGreenWronskian_eq_normalizedResponse_cross_mul
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion w z hwF hzF]
  unfold canonicalCompletedNativePolarizedResponseNumerator
  field_simp [hwF, hstarZ]

/-- Division-free scalar form: the exact chiral balance is separation times
the canonical completed-native `dslope`. -/
theorem completedNativeScalarChiralDifference_eq_separation_mul_dslope
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    Complex.I *
        (completedNativeNormalizedPositiveChiralTraceKernel z w -
          completedNativeNormalizedNegativeChiralTraceKernel z w) =
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [completedNativeScalarChiralDifference_eq_polarizedResponseNumerator
      hzF hwF,
    canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
      hzStrip hsep]

/-- The full channel-separated C3 carrier and the scalar `(F,-F')` trace have
the same signed chiral balance.  Their individual positive and negative
energies need not coincide, but no net logarithmic-derivative information is
missing from either representation. -/
theorem canonicalCompletedC3FullChiralBalance_eq_scalarChiralBalance
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel
            M z w -
          canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel
            M z w) =
      Complex.I *
        (completedNativeNormalizedPositiveChiralTraceKernel z w -
          completedNativeNormalizedNegativeChiralTraceKernel z w) := by
  rw [canonicalCompletedC3FullWronskianChiralDifference_eq_polarizedResponseNumerator
      M hzStrip hwStrip hzF hwF,
    completedNativeScalarChiralDifference_eq_polarizedResponseNumerator hzF hwF]

/-- Away from collision, the completed-native `dslope` is the scalar
Hermite--Biehler chiral quotient. -/
theorem completedNativePolarizedDslopeKernel_eq_scalarChiralDifference_div
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      Complex.I *
          (completedNativeNormalizedPositiveChiralTraceKernel z w -
            completedNativeNormalizedNegativeChiralTraceKernel z w) /
        (w - conj z) := by
  apply (eq_div_iff (sub_ne_zero.mpr hsep)).2
  rw [mul_comm]
  exact
    (completedNativeScalarChiralDifference_eq_separation_mul_dslope
      hzStrip hzF hwF hsep).symm

/-- On a nonreal diagonal, the sign of the completed `dslope` is exactly the
signed difference of the two normalized chiral energies divided by `2 Im z`.
This is the concrete Hermite--Biehler inequality that remains to be supplied
by the upstream tilt geometry. -/
theorem completedNativePolarizedDslopeKernel_diagonal_eq_chiralNormDifference
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : z.im ≠ 0) :
    canonicalCompletedNativePolarizedDslopeKernel z z =
      (((‖completedNativeNormalizedPositiveChiralTraceState z‖ ^ 2 -
          ‖completedNativeNormalizedNegativeChiralTraceState z‖ ^ 2 : ℝ) : ℂ) /
        ((2 * z.im : ℝ) : ℂ)) := by
  have hsep : z ≠ conj z := by
    intro h
    exact hzIm (Complex.conj_eq_iff_im.mp h.symm)
  rw [completedNativePolarizedDslopeKernel_eq_scalarChiralDifference_div
      hzStrip hzF hzF hsep,
    completedNativeNormalizedPositiveChiralTraceKernel,
    completedNativeNormalizedNegativeChiralTraceKernel,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    Complex.sub_conj]
  push_cast
  field_simp [hzIm]
  rfl

/-- In the upper half-plane, diagonal nonnegativity of the completed-native
`dslope` is equivalent to dominance of the positive Hermite--Biehler channel.
No positivity is assumed: this theorem identifies the exact concrete
inequality which an upstream tilt-energy argument must establish. -/
theorem completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_chiralNorm
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      ‖completedNativeNormalizedNegativeChiralTraceState z‖ ^ 2 ≤
        ‖completedNativeNormalizedPositiveChiralTraceState z‖ ^ 2 := by
  rw [completedNativePolarizedDslopeKernel_diagonal_eq_chiralNormDifference
    hzStrip hzF (ne_of_gt hzIm)]
  rw [← Complex.ofReal_div]
  simp only [Complex.ofReal_re]
  have hden : 0 < 2 * z.im := by positivity
  constructor
  · intro h
    rcases div_nonneg_iff.mp h with hpositive | hnegative
    · exact sub_nonneg.mp hpositive.1
    · linarith [hnegative.2]
  · intro h
    exact div_nonneg (sub_nonneg.mpr h) hden.le

/-- Strict diagonal positivity is likewise exactly strict positive-channel
dominance. -/
theorem completedNativePolarizedDslopeKernel_diagonal_re_pos_iff_chiralNorm
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 < (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      ‖completedNativeNormalizedNegativeChiralTraceState z‖ ^ 2 <
        ‖completedNativeNormalizedPositiveChiralTraceState z‖ ^ 2 := by
  rw [completedNativePolarizedDslopeKernel_diagonal_eq_chiralNormDifference
    hzStrip hzF (ne_of_gt hzIm)]
  rw [← Complex.ofReal_div]
  simp only [Complex.ofReal_re]
  have hden : 0 < 2 * z.im := by positivity
  constructor
  · intro h
    rcases div_pos_iff.mp h with hpositive | hnegative
    · exact sub_pos.mp hpositive.1
    · linarith [hnegative.2]
  · intro h
    exact div_pos (sub_pos.mpr h) hden

/-- Fully scalar spelling of diagonal nonnegativity: the exact gate is the
Hermite--Biehler norm inequality for `-F' ± iF`. -/
theorem
    completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_hermiteBiehler
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      ‖completedNativeNegativeHermiteBiehlerCoordinate z‖ ^ 2 ≤
        ‖completedNativePositiveHermiteBiehlerCoordinate z‖ ^ 2 := by
  have hden : 0 < 4 * ‖completedNativeOperatorCharacteristic z‖ ^ 2 := by
    have hnorm : 0 < ‖completedNativeOperatorCharacteristic z‖ :=
      norm_pos_iff.mpr hzF
    positivity
  rw [completedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_chiralNorm
      hzStrip hzF hzIm,
    norm_sq_completedNativeNormalizedNegativeChiralTraceState hzF,
    norm_sq_completedNativeNormalizedPositiveChiralTraceState hzF,
    div_le_div_iff_of_pos_right hden]

/-- Fully scalar spelling of strict diagonal positivity. -/
theorem completedNativePolarizedDslopeKernel_diagonal_re_pos_iff_hermiteBiehler
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : 0 < z.im) :
    0 < (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      ‖completedNativeNegativeHermiteBiehlerCoordinate z‖ ^ 2 <
        ‖completedNativePositiveHermiteBiehlerCoordinate z‖ ^ 2 := by
  have hden : 0 < 4 * ‖completedNativeOperatorCharacteristic z‖ ^ 2 := by
    have hnorm : 0 < ‖completedNativeOperatorCharacteristic z‖ :=
      norm_pos_iff.mpr hzF
    positivity
  rw [completedNativePolarizedDslopeKernel_diagonal_re_pos_iff_chiralNorm
      hzStrip hzF hzIm,
    norm_sq_completedNativeNormalizedNegativeChiralTraceState hzF,
    norm_sq_completedNativeNormalizedPositiveChiralTraceState hzF,
    div_lt_div_iff_of_pos_right hden]

/-! ## Centered chiral balance and the complete product log-jet -/

/-- Centered evenness removes the first derivative from the positive
Hermite--Biehler coordinate, leaving exactly `i F(0)`. -/
theorem completedNativePositiveHermiteBiehlerCoordinate_zero :
    completedNativePositiveHermiteBiehlerCoordinate 0 =
      Complex.I * completedNativeOperatorCharacteristic 0 := by
  have hderiv : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  simp [completedNativePositiveHermiteBiehlerCoordinate, hderiv]

/-- The negative coordinate has the opposite quarter turn at the center. -/
theorem completedNativeNegativeHermiteBiehlerCoordinate_zero :
    completedNativeNegativeHermiteBiehlerCoordinate 0 =
      -Complex.I * completedNativeOperatorCharacteristic 0 := by
  have hderiv : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  simp [completedNativeNegativeHermiteBiehlerCoordinate, hderiv]

/-- Exact positive chiral energy at the centered height. -/
theorem norm_sq_completedNativeNormalizedPositiveChiralTraceState_zero :
    ‖completedNativeNormalizedPositiveChiralTraceState 0‖ ^ 2 =
      (1 : ℝ) / 4 := by
  rw [norm_sq_completedNativeNormalizedPositiveChiralTraceState
      completedNativeOperatorCharacteristic_zero_ne_zero,
    completedNativePositiveHermiteBiehlerCoordinate_zero,
    norm_mul, Complex.norm_I, one_mul]
  have hnorm : ‖completedNativeOperatorCharacteristic 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hnorm]

/-- Exact negative chiral energy at the centered height. -/
theorem norm_sq_completedNativeNormalizedNegativeChiralTraceState_zero :
    ‖completedNativeNormalizedNegativeChiralTraceState 0‖ ^ 2 =
      (1 : ℝ) / 4 := by
  rw [norm_sq_completedNativeNormalizedNegativeChiralTraceState
      completedNativeOperatorCharacteristic_zero_ne_zero,
    completedNativeNegativeHermiteBiehlerCoordinate_zero,
    norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hnorm : ‖completedNativeOperatorCharacteristic 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hnorm]

/-- The centered scalar trace carries nonzero total energy even though its
signed chiral readout vanishes. -/
theorem completedNativeNormalizedChiralTrace_totalEnergy_zero :
    ‖completedNativeNormalizedPositiveChiralTraceState 0‖ ^ 2 +
        ‖completedNativeNormalizedNegativeChiralTraceState 0‖ ^ 2 =
      (1 : ℝ) / 2 := by
  rw [norm_sq_completedNativeNormalizedPositiveChiralTraceState_zero,
    norm_sq_completedNativeNormalizedNegativeChiralTraceState_zero]
  norm_num

/-- Center-pinned scalar chiral balance.  This is the smallest carrier that
retains both `F` and its completed log-jet `-F'`. -/
def completedNativeScalarChiralBalanceResponse (z : ℂ) : ℂ :=
  Complex.I *
    (completedNativeNormalizedPositiveChiralTraceKernel 0 z -
      completedNativeNormalizedNegativeChiralTraceKernel 0 z)

/-- Wherever the characteristic is nonzero, the center-pinned scalar chiral
balance is exactly the completed normalized logarithmic response. -/
theorem completedNativeScalarChiralBalanceResponse_eq_completed
    {z : ℂ} (hzF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeScalarChiralBalanceResponse z =
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z := by
  rw [completedNativeScalarChiralBalanceResponse,
    completedNativeScalarChiralDifference_eq_polarizedResponseNumerator
      completedNativeOperatorCharacteristic_zero_ne_zero hzF]
  unfold canonicalCompletedNativePolarizedResponseNumerator
  change
    completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z -
        conj (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion 0) = _
  have hderiv : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  unfold completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv 0, hderiv]
  simp

/-- The scalar chiral balance and the completed logarithmic response define
the same analytic germ at the center. -/
theorem completedNativeScalarChiralBalanceResponse_eventuallyEq_completed :
    completedNativeScalarChiralBalanceResponse =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hnonzero] with z hzF
  exact completedNativeScalarChiralBalanceResponse_eq_completed hzF

/-- Taylor coefficient of the center-pinned scalar chiral balance. -/
def completedNativeScalarChiralBalanceTaylorCoefficient
    (order : ℕ) : ℂ :=
  iteratedDeriv order completedNativeScalarChiralBalanceResponse 0 /
    order.factorial

/-- Every scalar chiral-balance coefficient is the corresponding coefficient
of the completed logarithmic response. -/
theorem completedNativeScalarChiralBalanceTaylorCoefficient_eq_completed
    (order : ℕ) :
    completedNativeScalarChiralBalanceTaylorCoefficient order =
      completedNativeGreenResponseTaylorCoefficient order := by
  unfold completedNativeScalarChiralBalanceTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    completedNativeScalarChiralBalanceResponse_eventuallyEq_completed]

/-- Every odd scalar chiral-balance coefficient is the canonical completed
native logarithmic moment. -/
theorem completedNativeScalarChiralBalance_odd_eq_canonicalMoment
    (n : ℕ) :
    completedNativeScalarChiralBalanceTaylorCoefficient (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [completedNativeScalarChiralBalanceTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]

/-- The removable derivative of the signed chiral balance is exactly the
zeroth completed-native logarithmic moment.  The equal `1/4` center energies
therefore do not erase the log-derivative: it lives in their first variation. -/
theorem completedNativeScalarChiralBalance_dslope_zero_zero :
    dslope completedNativeScalarChiralBalanceResponse 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [dslope_same]
  have h := completedNativeScalarChiralBalance_odd_eq_canonicalMoment 0
  simpa [completedNativeScalarChiralBalanceTaylorCoefficient,
    iteratedDeriv_one] using h

/-- Fully expanded product-rule form of the preceding chiral derivative.  The
mixed completion/native channel has the forced Leibniz coefficient `2`. -/
theorem completedNativeScalarChiralBalance_dslope_zero_zero_eq_productJet :
    dslope completedNativeScalarChiralBalanceResponse 0 0 =
      -(iteratedDeriv 2 nativeXiCompletionFactor 0 * nativeHeightScalar 0 +
          2 * deriv nativeXiCompletionFactor 0 * deriv nativeHeightScalar 0 +
          nativeXiCompletionFactor 0 * iteratedDeriv 2 nativeHeightScalar 0) /
        (2 * nativeXiCompletionFactor 0 * nativeHeightScalar 0) := by
  rw [completedNativeScalarChiralBalance_dslope_zero_zero,
    canonicalCompletedNativeLogDerivativeMoment_zero_eq_productJet]

/-! ## Logical strength of strict Hermite--Biehler dominance -/

/-- Strict upper-half-plane dominance of the completed chiral coordinates.
This definition names the exact scalar sign identified above; it does not
assert or assume that the sign has been proved. -/
def CanonicalCompletedNativeHermiteBiehlerStrictUpperHalfPlane : Prop :=
  ∀ z : ℂ,
    operatorHeightParameter z ∈ genuineCriticalStrip →
      0 < z.im →
        ‖completedNativeNegativeHermiteBiehlerCoordinate z‖ ^ 2 <
          ‖completedNativePositiveHermiteBiehlerCoordinate z‖ ^ 2

/-- A characteristic zero makes the two scalar chiral coordinates literally
equal.  Hence strict Hermite--Biehler dominance already forbids every zero in
the upper half-plane. -/
theorem completedNativeOperatorCharacteristic_ne_zero_of_hermiteBiehlerStrict
    (hHB : CanonicalCompletedNativeHermiteBiehlerStrictUpperHalfPlane)
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzIm : 0 < z.im) :
    completedNativeOperatorCharacteristic z ≠ 0 := by
  intro hzero
  have hstrict := hHB z hzStrip hzIm
  have hcoordinates :
      completedNativeNegativeHermiteBiehlerCoordinate z =
        completedNativePositiveHermiteBiehlerCoordinate z := by
    simp [completedNativeNegativeHermiteBiehlerCoordinate,
      completedNativePositiveHermiteBiehlerCoordinate, hzero]
  rw [hcoordinates] at hstrict
  exact (lt_irrefl _ hstrict)

/-- By centered evenness, the same strict dominance confines every completed
native characteristic zero in the natural strip to the real height axis. -/
theorem completedNativeOperator_zero_im_eq_zero_of_hermiteBiehlerStrict
    (hHB : CanonicalCompletedNativeHermiteBiehlerStrictUpperHalfPlane)
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 := by
  by_contra hzIm
  rcases lt_or_gt_of_ne hzIm with hzLower | hzUpper
  · have hnegStrip : operatorHeightParameter (-z) ∈ genuineCriticalStrip := by
      rw [operatorHeightParameter_neg]
      constructor <;> simp only [Complex.sub_re, Complex.one_re] <;>
        linarith [hzStrip.1, hzStrip.2]
    have hnegIm : 0 < (-z).im := by simp; linarith
    have hnegZero : completedNativeOperatorCharacteristic (-z) = 0 := by
      rw [completedNativeOperatorCharacteristic_neg hzStrip, hzero]
    exact
      (completedNativeOperatorCharacteristic_ne_zero_of_hermiteBiehlerStrict
        hHB hnegStrip hnegIm) hnegZero
  · exact
      (completedNativeOperatorCharacteristic_ne_zero_of_hermiteBiehlerStrict
        hHB hzStrip hzUpper) hzero

end

end CarrySelfAdjointOperator
