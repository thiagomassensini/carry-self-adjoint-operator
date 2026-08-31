import CarrySelfAdjointOperator.CompletedC3CoisometricWronskianProjectionGate
import CarrySelfAdjointOperator.CanonicalC3RadialGreenEnergy
import Mathlib.Tactic

/-!
# Coisometric Wronskian energy gate

The canonical coisometric boundary is a purely imaginary Green square on the
diagonal.  This module removes the Gamma response and every correction channel
from the remaining sewing equation.  What remains is one real equality between
the completed TFVD `(F,-F')` Wronskian and the full ambient Dirichlet-gradient
energy.

No vanishing, positivity comparison, characteristic zero, or spectral premise
is used below.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The canonical coisometric diagonal boundary is purely imaginary. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_diagonal_re_eq_zero
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3CoisometricCompressedBoundaryReadout
      z z hzHalf hzHalf).re = 0 := by
  rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel]
  rw [inner_self_eq_norm_sq_to_K]
  let q : ℂ :=
    ((‖canonicalCompletedC3GammaCameraView
      (completedC3SymplecticCameraState
        (operatorHeightParameter z) hzHalf)‖ : ℂ) ^ 2)
  change ((z - conj z) * q).re = 0
  have hqIm : q.im = 0 := by
    dsimp only [q]
    calc
      (((‖canonicalCompletedC3GammaCameraView
        (completedC3SymplecticCameraState
          (operatorHeightParameter z) hzHalf)‖ : ℂ) ^ 2)).im =
          (((‖canonicalCompletedC3GammaCameraView
            (completedC3SymplecticCameraState
              (operatorHeightParameter z) hzHalf)‖ ^ 2 : ℝ) : ℂ)).im :=
        congrArg Complex.im
          (Complex.ofReal_pow
            ‖canonicalCompletedC3GammaCameraView
              (completedC3SymplecticCameraState
                (operatorHeightParameter z) hzHalf)‖ 2).symm
      _ = 0 := rfl
  rw [Complex.mul_re, hqIm]
  simp

/-- Its imaginary part is exactly twice the centered height times the norm
square of the complete source-matched ambient response. -/
theorem canonicalCompletedC3CoisometricCompressedBoundaryReadout_diagonal_im_eq_ambientEnergy
    (z : ℂ) (hzIm : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    (canonicalCompletedC3CoisometricCompressedBoundaryReadout
        z z hzHalf hzHalf).im =
      2 * z.im *
        ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 := by
  rw [← canonicalCompletedC3AmbientBoundaryReadout_eq_coisometricCompressed]
  exact canonicalCompletedC3AmbientBoundaryReadout_diagonal_im_eq_energy
    hzIm hzHalf

/-- Since both diagonal objects are purely imaginary, their complex equality
is equivalent to equality of their imaginary parts. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_im
    (z : ℂ) (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzHalf hzHalf =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      (canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzHalf hzHalf).im =
        (completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z).im := by
  constructor
  · intro h
    exact congrArg Complex.im h
  · intro him
    apply Complex.ext
    · rw [canonicalCompletedC3CoisometricCompressedBoundaryReadout_diagonal_re_eq_zero,
        completedGreenWronskian_diagonal_re_eq_zero]
    · exact him

/-- The diagonal sewing equation after eliminating the Gamma/correction
factorization: Wronskian imaginary part equals the full ambient energy. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_ambientEnergy
    (z : ℂ) (hzIm : z.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzHalf hzHalf =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      2 * z.im *
          ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 =
        (completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z).im := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_im,
    canonicalCompletedC3CoisometricCompressedBoundaryReadout_diagonal_im_eq_ambientEnergy
      z hzIm hzHalf]

/-- The same gate with the Wronskian read from the completed enriched TFVD
trace.  This uses the exact value/log-jet reconstruction, not a Green sewing
hypothesis. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_tfvdEnergy
    (M : ℕ) (z : ℂ) (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      2 * z.im *
          ‖canonicalCompletedC3AmbientResponseState z hzStrip.1‖ ^ 2 =
        (canonicalC3BracketTfvdCompletedWronskianReadout M z z).im := by
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  have htfvd :
      canonicalC3BracketTfvdCompletedWronskianReadout M z z =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z := by
    rw [hcompanion]
    exact canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      M hzStrip hzStrip
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_ambientEnergy
      z hzIm hzStrip.1,
    ← htfvd]

/-- Fully geometric spelling of the remaining scalar gate.  The right-hand
side is the completed TFVD Wronskian; the left-hand side contains only the
radial coefficient and the completed ordinary Dirichlet-gradient norm. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gradientEnergy
    (M : ℕ) (z : ℂ) (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      2 * z.im *
          ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
            ‖canonicalCompletedC3DirichletGradientState
              (operatorHeightParameter z) hzStrip.1‖ ^ 2) =
        (canonicalC3BracketTfvdCompletedWronskianReadout M z z).im := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_tfvdEnergy
      M z hzIm hzStrip,
    canonicalCompletedC3AmbientResponseEnergy_eq_gradient]

/-- The diagonal TFVD Wronskian is the first variation of the completed native
vertical modulus energy.  The center--leg synthesis keeps every local, cross,
completion, and residual channel in this identification. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_im_eq_verticalModulusEnergy_deriv
    {ι : Type*} [Fintype ι]
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (legs : ReflectedBoundarySynthesisData ι) :
    (canonicalC3BracketTfvdCompletedWronskianReadout M z z).im =
      deriv (completedNativeVerticalModulusEnergy z) 0 := by
  have hledger := congrArg Complex.im
    (canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_eq_localLegLedger
      M hzStrip legs)
  have hderiv :=
    (hasDerivAt_completedNativeVerticalModulusEnergy_eq_localLegLedger
      hzStrip legs).deriv
  exact hledger.trans hderiv.symm

/-- Differential form of the coisometric sewing gate.  It is now a comparison
between two energies derived upstream from the native geometry. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_verticalModulusEnergy
    {ι : Type*} [Fintype ι]
    (M : ℕ) (z : ℂ) (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (legs : ReflectedBoundarySynthesisData ι) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      2 * z.im *
          ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
            ‖canonicalCompletedC3DirichletGradientState
              (operatorHeightParameter z) hzStrip.1‖ ^ 2) =
        deriv (completedNativeVerticalModulusEnergy z) 0 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gradientEnergy
      M z hzIm hzStrip,
    canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_im_eq_verticalModulusEnergy_deriv
      M z hzStrip legs]

/-- Explicit real balance left after the coisometric substitution. -/
def canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re) : ℝ :=
  2 * z.im *
      ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
        ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter z) hzHalf‖ ^ 2) -
    (canonicalC3BracketTfvdCompletedWronskianReadout M z z).im

/-- The original complex sewing statement is exactly vanishing of the
explicit real TFVD/gradient balance. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_energyBalance
    (M : ℕ) (z : ℂ) (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
          M z hzStrip.1 = 0 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_gradientEnergy
    M z hzIm hzStrip]
  unfold canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
  exact sub_eq_zero.symm

/-- The explicit balance is the ambient gradient energy minus the exact first
variation of the native vertical modulus energy. -/
theorem canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_gradient_sub_verticalModulusEnergy_deriv
    {ι : Type*} [Fintype ι]
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (legs : ReflectedBoundarySynthesisData ι) :
    canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 =
      2 * z.im *
          ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
            ‖canonicalCompletedC3DirichletGradientState
              (operatorHeightParameter z) hzStrip.1‖ ^ 2) -
        deriv (completedNativeVerticalModulusEnergy z) 0 := by
  unfold canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_im_eq_verticalModulusEnergy_deriv
    M z hzStrip legs]

/-- At a characteristic zero, the TFVD/Wronskian term vanishes and the real
balance is exactly the complete coisometric gradient energy. -/
theorem canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_gradientEnergy_of_characteristicZero
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 =
      2 * z.im *
        ((completedC3RadialRealCoefficient (operatorHeightParameter z) ^ 2 + 1) *
          ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter z) hzStrip.1‖ ^ 2) := by
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) := by
    funext u
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv u
  have htfvd :
      canonicalC3BracketTfvdCompletedWronskianReadout M z z =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z := by
    rw [hcompanion]
    exact canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      M hzStrip hzStrip
  unfold canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
  rw [htfvd]
  simp [completedGreenWronskian, hzero]

/-- Consequently the explicit real balance cannot vanish at a hypothetical
off-axis characteristic zero.  This certifies the precise logical strength of
the remaining equality without assuming confinement. -/
theorem canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_ne_zero_of_characteristicZero
    (M : ℕ) (z : ℂ) (hzIm : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 ≠ 0 := by
  intro hbalance
  have hsewing :=
    (canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_energyBalance
      M z hzIm hzStrip).mpr hbalance
  exact
    (canonicalCompletedC3CoisometricBoundaryReadout_ne_wronskian_of_characteristicZero
      hzIm hzStrip hzero) hsewing

/-- In the upper half-plane the obstruction at a hypothetical characteristic
zero has a strict positive sign, supplied by the nondegenerate completed
Dirichlet-gradient state. -/
theorem canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_pos_of_characteristicZero
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    0 < canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 := by
  rw [canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_gradientEnergy_of_characteristicZero
    M z hzStrip hzero]
  have hgradient :
      canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter z) hzStrip.1 ≠ 0 :=
    canonicalCompletedC3DirichletGradientState_ne_zero hzStrip
  have hnorm :
      0 < ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter z) hzStrip.1‖ :=
    norm_pos_iff.mpr hgradient
  have hnormSq :
      0 < ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter z) hzStrip.1‖ ^ 2 :=
    pow_pos hnorm 2
  have hradial :
      0 < completedC3RadialRealCoefficient
          (operatorHeightParameter z) ^ 2 + 1 := by
    nlinarith [sq_nonneg
      (completedC3RadialRealCoefficient (operatorHeightParameter z))]
  positivity

end

end CarrySelfAdjointOperator
