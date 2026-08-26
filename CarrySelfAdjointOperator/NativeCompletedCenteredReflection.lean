import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import CarrySelfAdjointOperator.NativeScalarDirectSchwarzReflection
import Mathlib.Tactic

/-!
# Centered reflection from the completed native channel

The direct native bracket series gives the antilinear identity

`F (-conj z) = conj (F z)`

for the completed characteristic: negated conjugation of centered height is
ordinary conjugation of the spectral parameter.  Composing this native
identity with the already proved centered parity `F (-z) = F z` yields the
centered Schwarz reflection `F (conj z) = conj (F z)` on the natural strip.

The two steps remain separate below, so the native conjugation channel is not
silently identified with centered parity.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Negated conjugation of centered height is ordinary conjugation of the
corresponding spectral parameter. -/
theorem operatorHeightParameter_neg_conj (z : ℂ) :
    operatorHeightParameter (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (operatorHeightParameter z) := by
  apply Complex.ext <;> simp [operatorHeightParameter]

/-- The native archimedean completion factor follows the same direct
conjugation channel. -/
theorem nativeXiCompletionFactor_neg_conj_from_nativeChannel (z : ℂ) :
    nativeXiCompletionFactor (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (nativeXiCompletionFactor z) := by
  unfold nativeXiCompletionFactor
  dsimp only
  rw [operatorHeightParameter_neg_conj]
  simp only [map_mul, map_sub, map_one, map_ofNat, map_div₀]
  rw [← Complex.exp_conj, ← Complex.Gamma_conj]
  congr 2 <;>
    simp only [map_neg, map_mul, map_div₀, map_ofNat,
      Complex.conj_ofReal]

/-- Direct antilinear reflection of the completed characteristic.  This step
uses only conjugation of the completion factor and the termwise native bracket
channel; centered parity is not used. -/
theorem completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel
    (z : ℂ) :
    completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  unfold completedNativeOperatorCharacteristic
  rw [nativeXiCompletionFactor_neg_conj_from_nativeChannel,
    operatorHeightParameter_neg_conj,
    nativeScalar_conj_from_nativeSeries]
  simp

/-- Conjugating centered height is reflection of the spectral parameter about
the critical center: `s ↦ 1 - conj s`. -/
theorem operatorHeightParameter_conj_eq_reflectedParameter (z : ℂ) :
    operatorHeightParameter ((starRingEnd ℂ) z) =
      reflectedParameter (operatorHeightParameter z) := by
  apply Complex.ext
  · simp [operatorHeightParameter, reflectedParameter]
    ring
  · simp [operatorHeightParameter, reflectedParameter]

/-- The reflected centered-height parameter remains in the natural strip. -/
theorem operatorHeightParameter_conj_mem_genuineCriticalStrip
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    operatorHeightParameter ((starRingEnd ℂ) z) ∈ genuineCriticalStrip := by
  rw [operatorHeightParameter_conj_eq_reflectedParameter]
  exact reflectedParameter_mem_genuineCriticalStrip hs

/-- After the direct native conjugation identity, centered Schwarz reflection
at `z` is exactly centered parity at `conj z`.  This equivalence isolates the
two logically distinct ingredients. -/
theorem completedNativeOperatorCharacteristic_centeredReflection_iff_evenAtConj
    (z : ℂ) :
    (completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (completedNativeOperatorCharacteristic z)) ↔
      (completedNativeOperatorCharacteristic (-(starRingEnd ℂ) z) =
        completedNativeOperatorCharacteristic ((starRingEnd ℂ) z)) := by
  rw [completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel]
  exact eq_comm

/-- Centered Schwarz reflection of the completed native characteristic.

The antilinear leg is the direct native channel above.  Centered parity is
then applied at `conj z`; no scalar channel is collapsed or cancelled. -/
theorem completedNativeOperatorCharacteristic_centeredReflection_via_nativeConjugation
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic z) := by
  have hsConj :
      operatorHeightParameter ((starRingEnd ℂ) z) ∈ genuineCriticalStrip :=
    operatorHeightParameter_conj_mem_genuineCriticalStrip hs
  have heven := completedNativeOperatorCharacteristic_neg
    (z := (starRingEnd ℂ) z) hsConj
  exact
    (completedNativeOperatorCharacteristic_centeredReflection_iff_evenAtConj z).2
      heven

end

end CarrySelfAdjointOperator
