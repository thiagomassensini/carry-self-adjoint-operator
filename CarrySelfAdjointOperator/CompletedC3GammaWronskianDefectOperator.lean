import CarrySelfAdjointOperator.CompletedC3GammaFullWronskianOperatorBridge
import Mathlib.Tactic

/-!
# Operator carrier for the Gamma--Wronskian defect

The positive Gamma response and the completed Wronskian already live in
honest Hilbert carriers, but they are read by different operators.  This
module retains both coordinates in one direct sum.  Its block operator reads
the Gamma Green boundary in the first coordinate and the negative completed
Wronskian in the second coordinate.

Thus the remaining sewing gate is the vanishing of one concrete bounded-
operator readout.  No scalar channel is identified, discarded, or assumed to
vanish in this construction.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Direct sum retaining the positive Gamma response and the full completed
Wronskian state as separate Hilbert coordinates. -/
abbrev CanonicalCompletedC3GammaWronskianDefectCarrier :=
  WithLp 2
    (CarryGammaComplexNaimark ×
      CanonicalCompletedC3FullWronskianOperatorCarrier)

/-- The two independently constructed states at one spectral parameter. -/
def canonicalCompletedC3GammaWronskianDefectState
    (M : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    CanonicalCompletedC3GammaWronskianDefectCarrier :=
  WithLp.toLp 2
    (canonicalCompletedC3PolarizedGammaState z hz,
      canonicalCompletedC3NormalizedFullWronskianOperatorState M z)

/-- Two-point block operator.  The first block inserts the exact Gamma
spectral separation; the second block is minus the full symplectic
Wronskian operator. -/
def canonicalCompletedC3GammaWronskianDefectOperator
    (z w : ℂ) :
    CanonicalCompletedC3GammaWronskianDefectCarrier →L[ℂ]
      CanonicalCompletedC3GammaWronskianDefectCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      CarryGammaComplexNaimark
      CanonicalCompletedC3FullWronskianOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      ((((w - conj z) •
          ContinuousLinearMap.id ℂ CarryGammaComplexNaimark).comp
        (WithLp.fstL 2 ℂ
          CarryGammaComplexNaimark
          CanonicalCompletedC3FullWronskianOperatorCarrier)).prod
      ((-canonicalCompletedC3FullWronskianOperator).comp
        (WithLp.sndL 2 ℂ
          CarryGammaComplexNaimark
          CanonicalCompletedC3FullWronskianOperatorCarrier)))

@[simp] theorem canonicalCompletedC3GammaWronskianDefectOperator_apply
    (z w : ℂ) (state : CanonicalCompletedC3GammaWronskianDefectCarrier) :
    canonicalCompletedC3GammaWronskianDefectOperator z w state =
      WithLp.toLp 2
        ((w - conj z) • state.fst,
          -canonicalCompletedC3FullWronskianOperator state.snd) :=
  rfl

/-- Explicit inverse block candidate away from spectral collision.  The
Gamma block uses reciprocal separation, while the inverse of `-J` is `J`
because the full Wronskian operator squares to `-1`. -/
def canonicalCompletedC3GammaWronskianDefectOperatorInverse
    (z w : ℂ) :
    CanonicalCompletedC3GammaWronskianDefectCarrier →L[ℂ]
      CanonicalCompletedC3GammaWronskianDefectCarrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      CarryGammaComplexNaimark
      CanonicalCompletedC3FullWronskianOperatorCarrier).symm
    |>.toContinuousLinearMap.comp
      ((((w - conj z)⁻¹ •
          ContinuousLinearMap.id ℂ CarryGammaComplexNaimark).comp
        (WithLp.fstL 2 ℂ
          CarryGammaComplexNaimark
          CanonicalCompletedC3FullWronskianOperatorCarrier)).prod
      (canonicalCompletedC3FullWronskianOperator.comp
        (WithLp.sndL 2 ℂ
          CarryGammaComplexNaimark
          CanonicalCompletedC3FullWronskianOperatorCarrier)))

@[simp] theorem canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply
    (z w : ℂ) (state : CanonicalCompletedC3GammaWronskianDefectCarrier) :
    canonicalCompletedC3GammaWronskianDefectOperatorInverse z w state =
      WithLp.toLp 2
        ((w - conj z)⁻¹ • state.fst,
          canonicalCompletedC3FullWronskianOperator state.snd) :=
  rfl

/-- The inverse candidate is a left inverse whenever the spectral separation
is nonzero. -/
theorem canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply_apply
    {z w : ℂ} (hsep : w ≠ conj z)
    (state : CanonicalCompletedC3GammaWronskianDefectCarrier) :
    canonicalCompletedC3GammaWronskianDefectOperatorInverse z w
        (canonicalCompletedC3GammaWronskianDefectOperator z w state) =
      state := by
  rw [canonicalCompletedC3GammaWronskianDefectOperator_apply,
    canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (w - conj z)⁻¹ • ((w - conj z) • state.fst) = state.fst
    rw [← mul_smul]
    field_simp [sub_ne_zero.mpr hsep]
    exact one_smul ℂ state.fst
  · change
      canonicalCompletedC3FullWronskianOperator
          (-canonicalCompletedC3FullWronskianOperator state.snd) = state.snd
    rw [map_neg, canonicalCompletedC3FullWronskianOperator_sq]
    simp

/-- The same explicit candidate is also a right inverse. -/
theorem canonicalCompletedC3GammaWronskianDefectOperator_apply_inverse_apply
    {z w : ℂ} (hsep : w ≠ conj z)
    (state : CanonicalCompletedC3GammaWronskianDefectCarrier) :
    canonicalCompletedC3GammaWronskianDefectOperator z w
        (canonicalCompletedC3GammaWronskianDefectOperatorInverse z w state) =
      state := by
  rw [canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply,
    canonicalCompletedC3GammaWronskianDefectOperator_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (w - conj z) • ((w - conj z)⁻¹ • state.fst) = state.fst
    rw [← mul_smul]
    field_simp [sub_ne_zero.mpr hsep]
    exact one_smul ℂ state.fst
  · change
      -canonicalCompletedC3FullWronskianOperator
          (canonicalCompletedC3FullWronskianOperator state.snd) = state.snd
    rw [canonicalCompletedC3FullWronskianOperator_sq]
    simp

/-- Hence no vector information is lost by the defect operator away from
collision.  Its scalar null form is an orthogonality condition, not a vector
kernel condition. -/
theorem canonicalCompletedC3GammaWronskianDefectOperator_injective
    {z w : ℂ} (hsep : w ≠ conj z) :
    Function.Injective
      (canonicalCompletedC3GammaWronskianDefectOperator z w) := by
  intro x y hxy
  calc
    x = canonicalCompletedC3GammaWronskianDefectOperatorInverse z w
        (canonicalCompletedC3GammaWronskianDefectOperator z w x) :=
      (canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply_apply
        hsep x).symm
    _ = canonicalCompletedC3GammaWronskianDefectOperatorInverse z w
        (canonicalCompletedC3GammaWronskianDefectOperator z w y) := by rw [hxy]
    _ = y :=
      canonicalCompletedC3GammaWronskianDefectOperatorInverse_apply_apply
        hsep y

/-- The block readout expands without merging the Gamma and Wronskian
coordinates. -/
theorem canonicalCompletedC3GammaWronskianDefectOperator_inner
    (z w : ℂ) (x y : CanonicalCompletedC3GammaWronskianDefectCarrier) :
    inner ℂ x (canonicalCompletedC3GammaWronskianDefectOperator z w y) =
      (w - conj z) * inner ℂ x.fst y.fst -
        inner ℂ x.snd
          (canonicalCompletedC3FullWronskianOperator y.snd) := by
  rw [canonicalCompletedC3GammaWronskianDefectOperator_apply,
    WithLp.prod_inner_apply]
  change
    inner ℂ x.fst ((w - conj z) • y.fst) +
        inner ℂ x.snd
          (-canonicalCompletedC3FullWronskianOperator y.snd) = _
  rw [inner_smul_right, inner_neg_right]
  ring

/-- The concrete block-operator readout is exactly the already isolated raw
Gamma--Wronskian defect. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_operatorInner
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      inner ℂ
        (canonicalCompletedC3GammaWronskianDefectState M z hz)
        (canonicalCompletedC3GammaWronskianDefectOperator z w
          (canonicalCompletedC3GammaWronskianDefectState M w hw)) := by
  rw [canonicalCompletedC3RawGammaWronskianDefect_eq_sub_fullOperatorInner
      M hz hw hzStrip hwStrip,
    canonicalCompletedC3GammaWronskianDefectOperator_inner,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  rfl

/-- The gate at the normalized Gamma kernel is now equivalently the null form
of one explicit bounded operator on the uncollapsed direct-sum state. -/
theorem canonicalCompletedC3NormalizedGammaKernel_eq_dslope_iff_defectOperator
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      inner ℂ
        (canonicalCompletedC3GammaWronskianDefectState M z hz)
        (canonicalCompletedC3GammaWronskianDefectOperator z w
          (canonicalCompletedC3GammaWronskianDefectState M w hw)) = 0 := by
  rw [canonicalCompletedC3NormalizedGammaKernel_eq_dslope_iff_fullOperatorInner
      M z w hz hw hzStrip hwStrip hzF hwF hsep]
  rw [canonicalCompletedC3GammaWronskianDefectOperator_inner,
    show
      (canonicalCompletedC3GammaWronskianDefectState M z hz).fst =
        canonicalCompletedC3PolarizedGammaState z hz by rfl,
    show
      (canonicalCompletedC3GammaWronskianDefectState M w hw).fst =
        canonicalCompletedC3PolarizedGammaState w hw by rfl,
    show
      (canonicalCompletedC3GammaWronskianDefectState M z hz).snd =
        canonicalCompletedC3NormalizedFullWronskianOperatorState M z by rfl,
    show
      (canonicalCompletedC3GammaWronskianDefectState M w hw).snd =
        canonicalCompletedC3NormalizedFullWronskianOperatorState M w by rfl]
  change
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) ↔
      (w - conj z) *
          canonicalCompletedC3PolarizedGammaKernel z w hz hw -
        inner ℂ
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)
          (canonicalCompletedC3FullWronskianOperator
            (canonicalCompletedC3NormalizedFullWronskianOperatorState M w)) = 0
  rw [← canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  exact sub_eq_zero.symm

/-- At a hypothetical nonreal characteristic zero, the diagonal defect
operator readout is nonzero.  The direct sum therefore does not hide the
known incompatibility by cancellation. -/
theorem canonicalCompletedC3GammaWronskianDefectOperator_inner_ne_zero_of_characteristicZero
    (M : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    inner ℂ
        (canonicalCompletedC3GammaWronskianDefectState M z hz)
        (canonicalCompletedC3GammaWronskianDefectOperator z z
          (canonicalCompletedC3GammaWronskianDefectState M z hz)) ≠ 0 := by
  rw [← canonicalCompletedC3RawGammaWronskianDefect_eq_operatorInner
    M hz hz hzStrip hzStrip]
  unfold canonicalCompletedC3RawGammaWronskianDefect
  have hwronskian :
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z = 0 := by
    simp [completedGreenWronskian, hzero]
  rw [hwronskian, sub_zero]
  exact canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
    hzStrip hz

end

end CarrySelfAdjointOperator
