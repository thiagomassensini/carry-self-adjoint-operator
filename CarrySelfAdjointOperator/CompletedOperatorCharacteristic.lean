import CarrySelfAdjointOperator.CompletedNativeCharacteristic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# The completed characteristic used by the native operator

The exact head-plus-tail camera ledger equals `factor camera s * nativeScalar
s`.  The reference operator then removes the camera factor and applies the
classical archimedean completion

`(1/2) * s * (s - 1) * pi^(-s/2) * Gamma(s/2)`.

This file names that camera-independent completed scalar in the centered
height variable `s = 1/2 + i z`, and proves a cross-multiplied identity that
connects it to every exact camera head-plus-tail presentation.  No division by
the camera factor is needed in the theorem.
-/

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Spectral parameter corresponding to the centered height variable. -/
def operatorHeightParameter (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

/-- Archimedean completion factor used by the reference operator. -/
def nativeXiCompletionFactor (z : ℂ) : ℂ :=
  let s := operatorHeightParameter z
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (s / 2)

/-- Camera-independent completed characteristic whose even logarithmic
moments feed the Hankel/Jacobi construction. -/
def completedNativeOperatorCharacteristic (z : ℂ) : ℂ :=
  nativeXiCompletionFactor z *
    nativeScalar (operatorHeightParameter z)

/-- Exact cross-multiplied bridge from every complete camera cutoff to the
camera-independent characteristic used by the operator. -/
theorem nativeXiCompletionFactor_mul_completedNativeCharacteristic
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {z : ℂ}
    (hs : operatorHeightParameter z ∈ nativeScalarDomain) :
    nativeXiCompletionFactor z *
        completedNativeCharacteristic camera cutoff
          (operatorHeightParameter z) =
      factor camera (operatorHeightParameter z) *
        completedNativeOperatorCharacteristic z := by
  rw [completedNativeCharacteristic_eq_factor_mul_nativeScalar
    hcamera hs]
  simp only [completedNativeOperatorCharacteristic]
  ring

end


end CarrySelfAdjointOperator
