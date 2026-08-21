import CarrySelfAdjointOperator.GreenWronskianRecomposition
import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
# Product-jet decomposition of the completed native characteristic

The characteristic used by the height operator is literally the product of
the archimedean xi-completion factor and the native scalar in centered-height
coordinates.  This file aligns the canonical companion `-F'` with the exact
product companion and specializes the Green product rule to that concrete
factorization.

The specialization records an important lossless bookkeeping fact.  At a
zero of the native scalar, the completion-jet channel is multiplied by the
squared scalar value and therefore vanishes.  Consequently an independently
retained Green/provenance coordinate cannot be cancelled by the scalar
completion jet after projection.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Native scalar written in the centered height coordinate of the operator. -/
def nativeHeightScalar (z : ℂ) : ℂ :=
  nativeScalar (operatorHeightParameter z)

/-- Canonical jet companion of the centered native scalar. -/
def nativeHeightScalarBoundaryCompanion (z : ℂ) : ℂ :=
  -deriv nativeHeightScalar z

/-- Canonical jet companion of the archimedean completion factor. -/
def nativeXiCompletionBoundaryCompanion (z : ℂ) : ℂ :=
  -deriv nativeXiCompletionFactor z

/-- Negative differentiation obeys exactly the product-boundary convention
used by the Green Wronskian. -/
theorem productBoundaryCompanion_negDeriv
    (A G : ℂ → ℂ) {z : ℂ}
    (hA : DifferentiableAt ℂ A z)
    (hG : DifferentiableAt ℂ G z) :
    productBoundaryCompanion
        A (fun u ↦ -deriv A u)
        G (fun u ↦ -deriv G u) z =
      -deriv (fun u ↦ A u * G u) z := by
  have hmul := (hA.hasDerivAt.mul hG.hasDerivAt).deriv
  change deriv (fun u ↦ A u * G u) z =
      deriv A z * G z + A z * deriv G z at hmul
  unfold productBoundaryCompanion
  rw [hmul]
  ring

/-- The centered native scalar is holomorphic wherever its spectral
parameter belongs to the native scalar domain. -/
theorem nativeHeightScalar_differentiableAt
    {z : ℂ} (hs : operatorHeightParameter z ∈ nativeScalarDomain) :
    DifferentiableAt ℂ nativeHeightScalar z := by
  have hparameter : DifferentiableAt ℂ operatorHeightParameter z := by
    unfold operatorHeightParameter
    fun_prop
  have hnative : DifferentiableAt ℂ nativeScalar
      (operatorHeightParameter z) :=
    nativeScalar_differentiableOn.differentiableAt
      (isOpen_nativeScalarDomain.mem_nhds hs)
  exact hnative.comp z hparameter

/-- On the open critical strip, the xi-completion factor is holomorphic in
the centered height variable.  In particular its Gamma argument has positive
real part and misses every Gamma pole. -/
theorem nativeXiCompletionFactor_differentiableAt
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    DifferentiableAt ℂ nativeXiCompletionFactor z := by
  have hparameter : DifferentiableAt ℂ operatorHeightParameter z := by
    unfold operatorHeightParameter
    fun_prop
  have hgammaBase :
      DifferentiableAt ℂ Complex.Gamma (operatorHeightParameter z / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hmRe := congrArg Complex.re hm
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp at hmRe
    linarith [hs.1]
  have hgamma :
      DifferentiableAt ℂ
        (fun u ↦ Complex.Gamma (operatorHeightParameter u / 2)) z := by
    exact hgammaBase.comp z (hparameter.div_const 2)
  unfold nativeXiCompletionFactor
  dsimp only
  apply DifferentiableAt.mul
  · fun_prop
  · exact hgamma

/-- The archimedean completion factor has no zero when the corresponding
spectral parameter lies in the open critical strip. -/
theorem nativeXiCompletionFactor_ne_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    nativeXiCompletionFactor z ≠ 0 := by
  have hsZero : operatorHeightParameter z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith [hs.1]
  have hsOne : operatorHeightParameter z - 1 ≠ 0 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hs.2]
  have hargRe : 0 < (operatorHeightParameter z / 2).re := by
    simpa using (div_pos hs.1 (by norm_num : (0 : ℝ) < 2))
  have hgamma : Complex.Gamma (operatorHeightParameter z / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hargRe
  unfold nativeXiCompletionFactor
  dsimp only
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hsZero)
        hsOne)
      (Complex.exp_ne_zero _))
    hgamma

/-- The actual canonical boundary companion is the product companion of the
xi factor and the centered native scalar. -/
theorem completedNativeOperatorBoundaryCompanion_eq_product
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorBoundaryCompanion z =
      productBoundaryCompanion
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
        nativeHeightScalar nativeHeightScalarBoundaryCompanion z := by
  have hsNative : operatorHeightParameter z ∈ nativeScalarDomain := by
    exact ⟨by linarith [hs.1], hs.2⟩
  unfold completedNativeOperatorBoundaryCompanion
    completedNativeOperatorCharacteristic
    nativeHeightScalar nativeXiCompletionBoundaryCompanion
    nativeHeightScalarBoundaryCompanion
  exact (productBoundaryCompanion_negDeriv
    nativeXiCompletionFactor
    (fun u ↦ nativeScalar (operatorHeightParameter u))
    (nativeXiCompletionFactor_differentiableAt hs)
    (nativeHeightScalar_differentiableAt hsNative)).symm

/-- At a native-scalar zero, the diagonal completed Wronskian reduces to the
native-scalar channel weighted by the squared xi factor.  The completion-jet
channel itself is absent. -/
theorem completedNativeOperatorGreenWronskian_at_nativeScalar_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : nativeHeightScalar z = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      nativeXiCompletionFactor z *
          (starRingEnd ℂ) (nativeXiCompletionFactor z) *
        completedGreenWronskian
          nativeHeightScalar nativeHeightScalarBoundaryCompanion z z := by
  change completedGreenWronskian
      (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
      completedNativeOperatorBoundaryCompanion z z = _
  calc
    completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        completedNativeOperatorBoundaryCompanion z z =
      completedGreenWronskian
        (fun u ↦ nativeXiCompletionFactor u * nativeHeightScalar u)
        (productBoundaryCompanion
          nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
          nativeHeightScalar nativeHeightScalarBoundaryCompanion) z z := by
            unfold completedGreenWronskian
            rw [completedNativeOperatorBoundaryCompanion_eq_product hs]
    _ = _ := completedGreenWronskian_mul_at_right_zero
      nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
      nativeHeightScalar nativeHeightScalarBoundaryCompanion hzero

/-- Both sides of the preceding decomposition vanish at the scalar zero;
the theorem is retained to make explicit which product channel disappeared. -/
theorem completedNativeOperatorGreenWronskian_eq_zero_at_nativeScalar_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : nativeHeightScalar z = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z = 0 := by
  rw [completedNativeOperatorGreenWronskian_at_nativeScalar_zero hs hzero]
  simp [completedGreenWronskian, hzero]

/-- The same product-channel reduction stated directly at a Riemann-zeta
zero.  The native scalar is not an auxiliary fitted characteristic here: its
previously proved analytic identification with `riemannZeta` supplies the
zero used by the exact product ledger. -/
theorem completedNativeOperatorGreenWronskian_at_riemannZeta_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : riemannZeta (operatorHeightParameter z) = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z =
      nativeXiCompletionFactor z *
          (starRingEnd ℂ) (nativeXiCompletionFactor z) *
        completedGreenWronskian
          nativeHeightScalar nativeHeightScalarBoundaryCompanion z z := by
  apply completedNativeOperatorGreenWronskian_at_nativeScalar_zero hs
  unfold nativeHeightScalar
  rw [nativeScalar_eq_riemannZeta hs, hzero]

/-- In particular the scalar diagonal Wronskian of the completed native
characteristic vanishes at every zeta zero in the open strip.  This makes
precise why the nonzero C3 provenance state must be retained before scalar
projection. -/
theorem completedNativeOperatorGreenWronskian_eq_zero_at_riemannZeta_zero
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : riemannZeta (operatorHeightParameter z) = 0) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z z = 0 := by
  apply completedNativeOperatorGreenWronskian_eq_zero_at_nativeScalar_zero hs
  unfold nativeHeightScalar
  rw [nativeScalar_eq_riemannZeta hs, hzero]

end

end CarrySelfAdjointOperator
